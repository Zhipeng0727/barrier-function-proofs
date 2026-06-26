"""
self_evolve.py — a self-evolving, GLM-driven loop for Lean-4 barrier/Lyapunov
formalization. Claude seeds direction (canonical obstruction goals, which
families to target) and audits; GLM does the volume; two GROUND-TRUTH ORACLES
decide what is true, so the loop converges instead of amplifying hallucination:

    * lean_compile_check  — a proof/recipe is real ONLY if it compiles (strict sorry)
    * local_verify        — a certificate is real ONLY if it passes numeric/symbolic check

Persistent learned memory:
    recipe_store.json     — compile-VERIFIED Lean snippets (bridging lemmas) per
                            transcendental family. Grows every round; injected into
                            the formalization writer prompt to kill lemma-name
                            hallucination on non-polynomial proofs.

Capabilities (each a GLM agent gated by an oracle):
    mine_recipe(family)         propose→compile→repair until a verified snippet exists
    evolve_recipes(families)    mine the whole non-poly frontier, persist, report
    generate_dataset(family,n)  GLM proposes (system,cert); local_verify filters
    recipes_block(family)       verified snippets as prompt text (used by lean_escalation)

CLI:
    python3 self_evolve.py mine tanh log exp trig
    python3 self_evolve.py dataset tanh 3
    python3 self_evolve.py status
"""
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

from runtime_state import (call_api, reset_tokens, TOKENS, API_CONFIG, PROVIDER,
                           PROVIDERS)
from barrier_core import (lean4_system, proposer_system, parse_json_response,
                          local_verify)
from lean_proof import extract_lean_code, lean_compile_check, _cert_family
from lean_error_kb import repair_hint

HERE = os.path.dirname(os.path.abspath(__file__))
RECIPE_STORE = os.path.join(HERE, "recipe_store.json")
EVOLVE_LOG = os.path.join(HERE, "evolve_history.jsonl")

# ─────────────────────────────────────────────────────────────────────────────
# CLAUDE-SEEDED DIRECTION: the canonical transcendental OBSTRUCTIONS that recur in
# barrier/Lyapunov decrease conditions. Each is a minimal, self-contained Lean goal
# whose verified proof is the bridging lemma the big proof keeps failing to name.
# These are the "what to learn" — GLM learns "how" by proposing compilable proofs.
# ─────────────────────────────────────────────────────────────────────────────
OBSTRUCTIONS = {
    "tanh": [
        ("tanh_sign", "0 ≤ y * Real.tanh y",
         "damping term y·tanh(y) is nonneg — the Lie derivative of a quadratic "
         "Lyapunov fn under tanh damping reduces to -y·tanh(y) ≤ 0"),
        ("tanh_bound", "Real.tanh y ≤ 1 ∧ -1 ≤ Real.tanh y",
         "tanh is bounded in [-1,1]"),
    ],
    "log": [
        ("log_sub_one", "0 < x → Real.log x ≤ x - 1",
         "Gibbs/entropy core: log x ≤ x - 1 for x>0"),
        ("log_self_lower", "0 < x → 1 - 1 / x ≤ Real.log x",
         "lower companion: 1 - 1/x ≤ log x"),
    ],
    "exp": [
        ("exp_add_one", "1 + x ≤ Real.exp x",
         "convexity core: 1 + x ≤ exp x for all x"),
        ("exp_pos", "0 < Real.exp x", "exp is strictly positive"),
    ],
    "trig": [
        ("sin_cos_sq", "Real.sin t ^ 2 + Real.cos t ^ 2 = 1",
         "Pythagorean identity — energy certificates"),
        ("one_sub_cos_nonneg", "0 ≤ 1 - Real.cos t",
         "pendulum energy: 1 - cos θ ≥ 0"),
    ],
    "sqrt": [
        ("sqrt_sq_abs", "0 ≤ x → Real.sqrt (x ^ 2) = |x|",
         "sqrt of a square is the absolute value"),
    ],
}

_FAMILY_IMPORTS = {
    # tanh sign/bound lemmas (sinh_nonneg_iff, cosh_pos, ...) live in DerivHyp, NOT
    # in Trigonometric.Basic — GLM could not find them without this import, which is
    # exactly why tanh mining failed until Claude supplied the module (direction).
    "tanh": ("import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic\n"
             "import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp"),
    "trig": "import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic",
    "log": "import Mathlib.Analysis.SpecialFunctions.Log.Basic",
    "exp": "import Mathlib.Analysis.SpecialFunctions.Exp",
    "sqrt": "import Mathlib.Analysis.SpecialFunctions.Pow.NNRpow",
}


# ─────────────────────────────────────────────────────────────────────────────
# Recipe store (persistent learned memory)
# ─────────────────────────────────────────────────────────────────────────────
def load_store() -> dict:
    if os.path.exists(RECIPE_STORE):
        with open(RECIPE_STORE, encoding="utf-8") as f:
            return json.load(f)
    return {"_meta": {"purpose": "compile-verified Lean bridging-lemma library, "
                      "mined by self_evolve.py; injected into the formalization "
                      "writer prompt to eliminate lemma-name hallucination."},
            "recipes": {}}


def save_store(store: dict):
    with open(RECIPE_STORE, "w", encoding="utf-8") as f:
        json.dump(store, f, indent=2, ensure_ascii=False)


def _log(rec: dict):
    with open(EVOLVE_LOG, "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False, default=str) + "\n")


# ─────────────────────────────────────────────────────────────────────────────
# GLM agent #1: mine a verified recipe for one obstruction (propose→compile→repair)
# ─────────────────────────────────────────────────────────────────────────────
_MINER_SYS = (
    "You are a Lean 4 + Mathlib4 expert. You write MINIMAL, self-contained proofs "
    "that COMPILE. You never invent lemma names: if unsure a lemma exists, you "
    "derive the fact from basic, certain lemmas (sq_nonneg, mul_nonneg, le_total, "
    "div_nonneg, Real.exp_pos, Real.add_one_le_exp, Real.log_le_sub_one_of_pos) or "
    "close it with nlinarith/positivity/gcongr. Output ONLY one ```lean code block."
)


# Family-directed SOS / lemma hints — VERIFIED lemma names (checked to exist in this
# Mathlib) + the tactic shape that closes each family. This is what lets the miner
# crack obstructions GLM fails on free-form (it hallucinates names): we hand it the
# real names up front. The per-family text is injected into the miner prompt.
_SOS_HINTS = {
    "tanh": (
        "VERIFIED tanh lemmas (exist in this Mathlib — use these exact names): "
        "`Real.tanh_lt_one x` (tanh x < 1), `Real.neg_one_lt_tanh x` (-1 < tanh x), "
        "`Real.tanh_eq_sinh_div_cosh`, `Real.cosh_pos x` (0 < cosh x), "
        "`Real.sinh_nonneg_iff` (0 ≤ sinh x ↔ 0 ≤ x; needs import "
        "Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp). "
        "For a SIGN goal (y·tanh y ≥ 0): rw [tanh_eq_sinh_div_cosh, ← mul_div_assoc], "
        "`apply div_nonneg _ (cosh_pos y).le`, case-split `rcases le_total 0 y`, use "
        "sinh_nonneg_iff. For a BOUND goal: `⟨(tanh_lt_one y).le, (neg_one_lt_tanh y).le⟩`."),
    "log": (
        "VERIFIED log lemmas: `Real.log_le_sub_one_of_pos (hx : 0 < x)` (log x ≤ x-1), "
        "`Real.log_inv` (log x⁻¹ = -log x), `Real.log_div`, `Real.exp_log`. "
        "For a LOWER bound 1 - 1/x ≤ log x: apply log_le_sub_one_of_pos to (1/x), then "
        "`rw [one_div, Real.log_inv] at h` and finish with nlinarith [h]."),
    "exp": (
        "VERIFIED exp lemmas: `Real.add_one_le_exp x` (1+x ≤ exp x), `Real.exp_pos x` "
        "(0 < exp x), `Real.exp_log`. Substitute z := exp x and use add_one_le_exp."),
    "trig": (
        "VERIFIED trig lemmas: `Real.sin_sq_add_cos_sq x` (= 1), `Real.neg_one_le_cos`, "
        "`Real.cos_le_one`, `Real.neg_one_le_sin`, `Real.sin_le_one`. For 0 ≤ 1 - cos: "
        "`linarith [Real.cos_le_one t]`."),
    "sqrt": (
        "VERIFIED: `Real.sqrt_sq_eq_abs` (√(x^2) = |x|), `Real.sqrt_sq (h : 0 ≤ x)`."),
    # generic obstruction shape from the auto-loop: an interval polynomial nonneg.
    "poly": (
        "For an INTERVAL polynomial nonnegativity (e.g. ∀ x ∈ Set.Icc 0 1, p x ≥ 0): "
        "unpack membership with `obtain ⟨hx0, hx1⟩ := hx` (or `hx.1`/`hx.2`), then feed "
        "nlinarith the ENDPOINT PRODUCTS it cannot guess: "
        "`nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ 1 - x), sq_nonneg x, "
        "sq_nonneg (x - 1), mul_nonneg hx0 hx0]`."),
}


def _miner_prompt(family, lean_goal, desc, imports, prior_fail=None, variant=0):
    sos = _SOS_HINTS.get(family, "")
    angle = ["", "\nTry the most ELEMENTARY route (case-split + nlinarith/positivity).",
             "\nTry a DIFFERENT lemma than an obvious first guess; derive if unsure.",
             "\nKeep it SHORT: one rewrite then one closing tactic if possible."][variant % 4]
    base = (
        f"Prove this Lean 4 lemma. It is the recurring bridging fact for the "
        f"'{family}' family in barrier-certificate decrease conditions:\n\n"
        f"  GOAL ({desc}):\n  example (x y t : ℝ) : {lean_goal} := by ...\n\n"
        f"Use these imports:\n{imports}\nimport Mathlib.Tactic\nopen Real\n\n"
        f"Write a COMPLETE `example` (drop unused binders among x y t) with a proof "
        f"that compiles. Prefer real, certain Mathlib lemma names; if a name is "
        f"uncertain, derive the step instead of guessing. No `sorry`."
        + (f"\n\n{sos}" if sos else "") + angle
    )
    if prior_fail:
        base += (f"\n\nYOUR PREVIOUS ATTEMPT FAILED TO COMPILE:\n```lean\n"
                 f"{prior_fail['code']}\n```\nCompiler diagnostic:\n{prior_fail['diag'][:900]}\n\n"
                 f"{repair_hint(prior_fail['diag'])}\n\nFix it. Replace any unknown "
                 f"identifier with a real one or derive the step. Output the full "
                 f"corrected ```lean block.")
    return base


ESCALATE_PROVIDER = os.environ.get("ESCALATE_PROVIDER", "openai")   # stronger model fallback


def _propose_and_check(family, oid, lean_goal, desc, imports, prior, variant,
                       effort, provider, tag):
    """One candidate: GLM(/provider) proposes, the Lean compiler verifies. Returns
    (ok, code, diag). The compile tag must be UNIQUE per candidate (parallel runs
    write distinct temp files)."""
    prompt = _miner_prompt(family, lean_goal, desc, imports, prior, variant)
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt}],
                            effort=effort, label=f"mine-{family}-{oid}-{tag}",
                            provider=provider)
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"mine_{family}_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def mine_recipe(family, oid, lean_goal, desc, max_rounds=4, effort="high",
                n_parallel=3, escalate=True, escalate_rounds=2):
    """Mine a compiling proof of `lean_goal`. Three reinforcements over the v1
    single-shot miner:
      • N-candidate PARALLEL proposals per round (diverse prompt angles) — first to
        compile wins, so one round explores several tactic routes at once.
      • family-directed SOS hints (verified lemma names) injected via _miner_prompt.
      • model ESCALATION: if GLM exhausts its rounds, retry with the stronger
        ESCALATE_PROVIDER (gpt-5.5) — the automated stand-in for hand integration.
    Returns (verified_code | None, rounds_used, diag)."""
    imports = _FAMILY_IMPORTS.get(family, "")
    prior = None

    def _run_phase(provider, rounds, base_round, tag_prefix):
        nonlocal prior
        pname = provider or "glm"
        for rnd in range(1, rounds + 1):
            variants = list(range(n_parallel))
            results = [None] * n_parallel
            with ThreadPoolExecutor(max_workers=n_parallel) as ex:
                futs = {ex.submit(_propose_and_check, family, oid, lean_goal, desc,
                                  imports, prior, v, effort, provider,
                                  f"{tag_prefix}r{rnd}c{v}"): v for v in variants}
                for fut in as_completed(futs):
                    results[futs[fut]] = fut.result()
            ok_one = next((r for r in results if r and r[0]), None)
            if ok_one:
                print(f"    [{pname}] round {base_round+rnd}: ✅ VERIFIED "
                      f"({n_parallel} parallel)")
                return ok_one[1], base_round + rnd, ok_one[2]
            # carry the most informative failure (longest diag) into the next round
            fails = [r for r in results if r and r[1]]
            if fails:
                prior = {"code": fails[0][1], "diag": fails[0][2] or ""}
                for r in fails:
                    if len(r[2] or "") > len(prior["diag"]):
                        prior = {"code": r[1], "diag": r[2]}
            head = (prior or {}).get("diag", "").splitlines()[:1]
            print(f"    [{pname}] round {base_round+rnd}: ✗ "
                  f"({head[0][:70] if head else 'no compile'})")
        return None, base_round + rounds, (prior or {}).get("diag", "")

    code, used, diag = _run_phase(None, max_rounds, 0, "glm")
    if code:
        return code, used, diag
    if escalate and ESCALATE_PROVIDER in PROVIDERS:
        print(f"    ↑ ESCALATE to {ESCALATE_PROVIDER} ({PROVIDERS[ESCALATE_PROVIDER]['model']})")
        try:
            code, used, diag = _run_phase(ESCALATE_PROVIDER, escalate_rounds, used, "esc")
            if code:
                return code, used, diag
        except Exception as e:
            print(f"    escalation unavailable: {type(e).__name__}")
    return None, used, diag


# ─────────────────────────────────────────────────────────────────────────────
# Driver: evolve the whole non-poly frontier, persist verified recipes
# ─────────────────────────────────────────────────────────────────────────────
def evolve_recipes(families, max_rounds=4):
    store = load_store()
    reset_tokens()
    print(f"provider={PROVIDER} model={API_CONFIG['model']}  evolving recipes for: "
          f"{', '.join(families)}\n")
    report = []
    for fam in families:
        for oid, lean_goal, desc in OBSTRUCTIONS.get(fam, []):
            key = f"{fam}.{oid}"
            if store["recipes"].get(key, {}).get("verified"):
                print(f"[{key}] already verified — skip"); continue
            print(f"[{key}] mining: {lean_goal}")
            t0 = time.time()
            code, rounds, diag = mine_recipe(fam, oid, lean_goal, desc, max_rounds)
            dt = round(time.time() - t0)
            if code:
                store["recipes"][key] = {
                    "family": fam, "obstruction": oid, "goal": lean_goal,
                    "desc": desc, "lean": code, "verified": True,
                    "rounds": rounds, "out_tokens": TOKENS["output"]}
                save_store(store)          # persist immediately — crash-safe
            report.append((key, bool(code), rounds, dt))
            _log({"key": key, "verified": bool(code), "rounds": rounds, "sec": dt,
                  "goal": lean_goal, "out_tokens_cum": TOKENS["output"]})

    print(f"\n{'#'*60}\nRECIPE EVOLUTION SUMMARY\n{'#'*60}")
    for key, ok, rounds, dt in report:
        print(f"  {'✅' if ok else '❌'} {key:22s} rounds={rounds} {dt}s")
    nver = sum(1 for r in report if r[1])
    print(f"\nVERIFIED {nver}/{len(report)} this run | "
          f"store now holds {sum(1 for v in store['recipes'].values() if v.get('verified'))} "
          f"recipes | out_tokens={TOKENS['output']}")
    return store


# ─────────────────────────────────────────────────────────────────────────────
# Prompt injection: verified recipes for a family (used by lean_escalation writer)
# ─────────────────────────────────────────────────────────────────────────────
def recipes_block(family, cert="", max_recipes=4) -> str:
    """Compile-verified bridging lemmas relevant to `cert`/`family`, as prompt text.
    These supersede hand-guessed template lemma names — they are KNOWN to compile."""
    store = load_store()
    fams = {family}
    c = (cert or "").lower()
    for f, toks in (("tanh", ["tanh"]), ("log", ["log"]), ("exp", ["exp", "sinh", "cosh"]),
                    ("trig", ["sin", "cos"]), ("sqrt", ["sqrt"])):
        if any(t in c for t in toks):
            fams.add(f)
    picked = [v for v in store.get("recipes", {}).values()
              if v.get("verified") and v.get("family") in fams][:max_recipes]
    if not picked:
        return ""
    out = ["VERIFIED bridging lemmas (these COMPILE against this exact Mathlib — "
           "reuse the lemma names and tactic shape; do NOT invent alternatives):"]
    for v in picked:
        out.append(f"-- {v['desc']}\n```lean\n{v['lean']}\n```")
    return "\n".join(out)


# ─────────────────────────────────────────────────────────────────────────────
# GLM agent #2: dataset construction (GLM proposes; STRICT structural validation +
# numeric/symbolic local_verify is the oracle).
#
# Hardening lessons from the first run (GLM emitted `poly(exp(1), x^2+y^2)` and it
# "passed"):
#   * pseudo-syntax: `poly(...)` sympifies to a sympy Poly OBJECT (garbage cert);
#     `min/max/sat(...)` etc. must be rejected unless they are real allowed funcs.
#   * VACUOUS PASS: local_verify returns passed=True when the symbolic check did not
#     RUN (sym_ok is None — e.g. f_expr absent because the ODE was never parsed).
#     Fix: parse the ODE into f_expr first, and require symbolic_valid IS True.
#   * a "non-polynomial" cert that contains no transcendental is off-spec → reject.
# ─────────────────────────────────────────────────────────────────────────────
import sympy as _sp
from dataset_loader import _parse_equation_dynamics, _norm_expr

_ALLOWED_FUNCS = {"exp", "log", "sin", "cos", "tan", "sinh", "cosh", "tanh",
                  "asin", "acos", "atan", "Abs"}     # sqrt is Pow(_,1/2), handled below
_FAMILY_FUNC = {"tanh": {"tanh"}, "log": {"log"}, "exp": {"exp", "sinh", "cosh", "tanh"},
                "trig": {"sin", "cos", "tan"}, "sqrt": {"sqrt"}}


def _strict_validate(rec, family):
    """Structural + oracle validation. Returns (system, h_str, None) on accept, or
    (None, None, reason) on reject. NO vacuous passes: the symbolic Lyapunov check
    must actually run and return valid."""
    h = (rec.get("h") or "").strip()
    ode = (rec.get("ode") or rec.get("dynamics") or "").strip()
    if not h or not ode:
        return None, None, "missing h/ode"
    # 1) dynamics must parse to real sympy RHS (rejects pseudo-syntax in the ODE)
    sv, f_expr, discrete, _ = _parse_equation_dynamics({"dynamics": ode})
    if sv is None:
        return None, None, f"bad dynamics: {f_expr}"
    # 2) certificate must be a plain real scalar Expr in the state vars
    syms = {v: _sp.Symbol(v) for v in sv}
    raw = _norm_expr(h)
    if any(tok in raw.replace(" ", "").lower() for tok in
           ("poly(", "min(", "max(", "sat(", "sign(", "relu(", "clip(")):
        return None, None, f"pseudo-syntax in h: {h[:40]}"
    try:
        e = _sp.sympify(raw, locals=syms)
    except Exception as ex:
        return None, None, f"h not parseable: {type(ex).__name__}"
    if not isinstance(e, _sp.Expr) or isinstance(e, _sp.Poly):
        return None, None, "h is not a scalar expression"
    bad = e.free_symbols - set(syms.values())
    if bad:
        return None, None, f"unknown symbols in h: {bad}"
    fnames = {f.func.__name__ for f in e.atoms(_sp.Function)}
    if fnames - _ALLOWED_FUNCS:
        return None, None, f"disallowed funcs in h: {fnames - _ALLOWED_FUNCS}"
    # 3) must genuinely be of the requested non-polynomial family — the
    #    transcendental may live in the CERTIFICATE or in the DYNAMICS (the Lie
    #    derivative inherits it either way), so scan h ∪ f_expr.
    def _funcs_of(expr):
        names = {f.func.__name__ for f in expr.atoms(_sp.Function)}
        if expr.has(_sp.sqrt) or any(getattr(p, "exp", None) == _sp.Rational(1, 2)
                                     for p in expr.atoms(_sp.Pow)):
            names.add("sqrt")
        return names
    present = set(fnames) | ({"sqrt"} if "sqrt" in _funcs_of(e) else set())
    for fe in f_expr:
        try:
            present |= _funcs_of(_sp.sympify(_norm_expr(fe), locals={**syms,
                                  "t": _sp.Symbol("t")}))
        except Exception:
            pass
    if not (present & _FAMILY_FUNC.get(family, set())):
        return None, None, f"not a '{family}' system (funcs={present or '∅'})"
    # 4) build a verifiable system and run the ORACLE — no vacuous pass
    system = {"name": rec.get("name", f"gen-{family}"), "ode": ode, "state_vars": sv,
              "f_expr": f_expr, "X_domain": rec.get("X_domain", ""),
              "task_type": "lyapunov", "discrete": bool(discrete)}
    try:
        lv = local_verify(system, h, {"xu_points": [], "escape_points": []})
    except Exception as ex:
        return None, None, f"verify EXC {type(ex).__name__}"
    if not lv.get("passed"):
        return None, None, f"oracle reject: {(lv.get('feedback') or '')[:60]}"
    if lv.get("symbolic", {}).get("symbolic_valid") is not True:
        return None, None, "symbolic check vacuous (did not run/confirm)"
    system["cert_gt"] = h
    system["_verified_family"] = _cert_family(h)
    return system, h, None


def generate_dataset(family, n=3, effort="high", max_tries=None):
    """GLM proposes non-polynomial systems for `family`; keep only those passing
    STRICT structural validation AND a non-vacuous numeric/symbolic oracle."""
    reset_tokens()
    kept, tries = [], 0
    max_tries = max_tries or n * 4
    allowed = ", ".join(sorted(_ALLOWED_FUNCS | {"sqrt"}))
    sysprompt = (
        "You design SIMPLE 2-D continuous dynamical systems (state vars x, y) that "
        f"admit a CORRECT Lyapunov certificate genuinely using {family}. "
        "Output strict JSON only.")
    rules = (
        f"Propose ONE system whose decrease condition genuinely involves {family}. "
        "HARD RULES:\n"
        f"- h and the ODE RHS must be PLAIN infix math in x,y using only: {allowed}, "
        "+ - * / ** and parentheses. \n"
        "- FORBIDDEN: poly(...), min(...), max(...), sat(...), sign(...), any "
        "helper/undefined function, matrix/list notation.\n"
        f"- h MUST contain {family} (or its family) and be a single scalar expression.\n"
        "- Keep it genuinely valid: V>0 away from 0 and V̇≤0 along the flow.\n"
        'Return JSON: {"name":..., "ode":"dx/dt=..., dy/dt=...", '
        '"state_vars":["x","y"], "X_domain":"", "h":"<certificate>"}.')
    while len(kept) < n and tries < max_tries:
        tries += 1
        try:
            reply, _ = call_api(sysprompt, [{"role": "user", "content": rules}],
                                effort=effort, label=f"dataset-{family}-{tries}")
        except Exception as e:
            print(f"  try {tries}: API {type(e).__name__}"); continue
        rec = parse_json_response(reply) or {}
        system, h, reason = _strict_validate(rec, family)
        if system:
            print(f"  try {tries}: ✅ KEEP  h={h[:46]}")
            kept.append(system)
        else:
            print(f"  try {tries}: ✗ {reason}")
    print(f"\nkept {len(kept)}/{tries} STRICT-valid '{family}' systems "
          f"(out_tokens={TOKENS['output']})")
    return kept


def status():
    store = load_store()
    recs = store.get("recipes", {})
    ver = {k: v for k, v in recs.items() if v.get("verified")}
    print(f"recipe_store: {len(ver)} verified recipes")
    by_fam = {}
    for v in ver.values():
        by_fam.setdefault(v["family"], []).append(v["obstruction"])
    for fam, ids in sorted(by_fam.items()):
        print(f"  {fam:6s}: {', '.join(ids)}")
    total = sum(len(v) for v in OBSTRUCTIONS.values())
    print(f"frontier coverage: {len(ver)}/{total} seeded obstructions verified")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "status"
    if cmd == "mine":
        evolve_recipes(sys.argv[2:] or list(OBSTRUCTIONS))
    elif cmd == "dataset":
        fam = sys.argv[2] if len(sys.argv) > 2 else "tanh"
        n = int(sys.argv[3]) if len(sys.argv) > 3 else 3
        out = generate_dataset(fam, n)
        print(json.dumps(out, ensure_ascii=False, indent=2))
    elif cmd == "status":
        status()
    else:
        print(__doc__)
