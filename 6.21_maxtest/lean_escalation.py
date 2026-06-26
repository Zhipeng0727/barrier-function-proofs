"""
lean_escalation.py — three-level escalation orchestrator for formalizing a
(numerically verified) barrier certificate in Lean 4.

Levels (driven by lean_error_kb.route_for on the real compiler diagnostic):
  L1  in-place repair      — same proof thread, fix the reported error
  L2  rewrite strategy     — fresh attempt, different tactic family / lemmas / statement
  L3  regenerate barrier   — the certificate is formalization-hostile; go back to the
                             Proposer for a DIFFERENT, formalization-friendly certificate

The state machine (`run_lean_escalation`) takes injected callables for write / compile /
propose, so the whole control flow can be exercised with fakes at ZERO token cost
(see test_escalation_fake.py). `formalize_certificate` wires in the real LLM + Lean.
"""
import json
import re

from runtime_state import call_api
from barrier_core import (lean4_system, proposer_system, _task_framework,
                          parse_json_response, local_verify)
from lean_proof import extract_lean_code, lean_compile_check, _TEMPLATES, _cert_family
from lean_error_kb import route_for, repair_hint, error_kb_block

DEFAULT_BUDGET = {"inner": 3, "barriers": 3, "max_calls": 10, "repeat_l3": 2}

# Weaker models (e.g. glm-4-flash) default to Lean 3 / mathlib3 syntax, which never
# compiles under Lean 4. Blunt, explicit guard with the exact forbidden tokens.
_LEAN4_GUARD = (
    "CRITICAL — Lean 4 + Mathlib4 ONLY, never Lean 3 / mathlib3:\n"
    "  FORBIDDEN (Lean 3): `import tactic`, `import data.*`, `import algebra.*`, "
    "`open_locale`, `begin ... end`, lowercase types `real`/`nat`, `λ x, …`.\n"
    "  REQUIRED (Lean 4): `import Mathlib.Data.Real.Basic`, `import Mathlib.Tactic`, "
    "`open Real`, capitalized `Real`/`Nat`/`ℝ`, `by` tactic blocks, `fun x => …`.\n"
    "  Proofs use `:= by nlinarith [...]` style. No `begin`/`end`.\n"
    "SOUNDNESS (a proof breaking these is REJECTED even if it compiles):\n"
    "  NO `axiom` of any kind — never re-declare ℝ/its operations (`axiom Real`, "
    "`axiom realAdd`, …) and never axiomatize the calculus/Nagumo bridge; import and "
    "use Mathlib's real numbers. NO `sorry`/`admit`. Name the main result as a "
    "top-level `theorem` (not anonymous `example`) so `#print axioms` can audit it. "
    "A real proof rests only on propext / Classical.choice / Quot.sound."
)

# Positive-definiteness (Lyapunov P1: V>0 away from the equilibrium) is a proof
# obligation in EVERY Lyapunov problem, and it is the #1 silent killer: nlinarith
# CANNOT exploit a negated conjunction `¬(x=0 ∧ y=0)` (or `x≠0 ∨ y≠0`) on its own,
# so `nlinarith [sq_nonneg x, sq_nonneg y]` fails the strict `> 0` goal. This is the
# VERIFIED recipe (compiles against this Mathlib) — case-split, then `positivity`
# uses the `≠ 0` hypothesis to get one strict square:
_POSDEF_RECIPE = (
    "Positive-definiteness (V>0 for state ≠ equilibrium) — nlinarith ALONE FAILS this "
    "(it cannot use `¬(x=0 ∧ y=0)`). Use this exact, verified pattern:\n"
    "```lean\n"
    "  -- goal: 0.5*x^2 + 0.5*y^2 > 0   from   h : ¬(x = 0 ∧ y = 0)\n"
    "  rcases not_and_or.mp h with hx | hy\n"
    "  · have : x^2 > 0 := by positivity   -- positivity reads hx : x ≠ 0\n"
    "    nlinarith [sq_nonneg y]\n"
    "  · have : y^2 > 0 := by positivity\n"
    "    nlinarith [sq_nonneg x]\n"
    "```\n"
    "If the hypothesis is already `x ≠ 0 ∨ y ≠ 0`, skip `not_and_or.mp` and `rcases h`."
)

# Lean 3 fingerprints — if the model emits these, the code is mathlib3 and must be redone.
_LEAN3_MARKERS = (
    "import tactic", "open_locale", "\nbegin", " begin\n", "\nend", "import data.",
    "import algebra.", "import analysis.", "λ ", ":= λ",
)


def _norm_cert(c: str) -> str:
    """Whitespace-insensitive cert key for dedup. The reproposer often returns a
    pure whitespace variant of an already-tried cert (`a+b` vs `a + b`); exact
    string compare lets it through and wastes a barrier regeneration on a
    duplicate. Collapse all whitespace so such variants compare equal."""
    return re.sub(r"\s+", "", c or "")


def _cert_seen(c: str, tried) -> bool:
    return _norm_cert(c) in {_norm_cert(t) for t in tried}


def _looks_empty(code: str) -> bool:
    c = (code or "").strip()
    return len(c) < 15 or not re.search(r"\b(theorem|lemma|example|def)\b", c)


def _looks_lean3(code: str) -> bool:
    c = code or ""
    return any(m in c for m in _LEAN3_MARKERS)


# ─────────────────────────────────────────────────────────────────────────────
# The state machine (pure control flow; all I/O is injected)
# ─────────────────────────────────────────────────────────────────────────────
def run_lean_escalation(system, cert, *, write_fn, compile_fn, propose_fn,
                        budget=None, on_event=None):
    """Escalate L1→L2→L3 until the certificate is formalized or budget runs out.

    write_fn(ctx)            -> lean code str;  ctx = {system, cert, strategy, history, hint}
    compile_fn(code)         -> (ok: bool|None, diag: str)
    propose_fn(system, diag, prev_certs) -> new cert str | None     (L3)

    Returns a result dict: solved, cert, code, diag, levels[], certs_tried[], calls.
    """
    budget = {**DEFAULT_BUDGET, **(budget or {})}
    emit = on_event or (lambda e: None)
    calls = 0
    certs_tried = [cert]
    last_diag = ""
    result = {"solved": False, "cert": cert, "code": None, "diag": None,
              "levels": [], "certs_tried": certs_tried, "calls": 0,
              "final_level": None}

    for b_idx in range(budget["barriers"]):
        emit({"event": "barrier", "idx": b_idx, "cert": cert})
        history, strategy, hint = [], "fresh", None
        inner_ok = False
        seen_errs = {}     # err id -> count (same error persisting ⇒ structural ⇒ L3)

        for i in range(budget["inner"]):
            if calls >= budget["max_calls"]:
                emit({"event": "budget_exhausted", "calls": calls})
                break
            calls += 1
            code = write_fn({"system": system, "cert": cert, "strategy": strategy,
                             "history": list(history), "hint": hint})
            ok, diag = compile_fn(code)
            last_diag = diag or ""
            r = {"route": "OK", "id": "compiled"} if ok else route_for(diag)
            lvl = {"barrier": b_idx, "inner": i, "strategy": strategy,
                   "compile_ok": ok, "route": r["route"], "err": r.get("id")}
            result["levels"].append(lvl)
            emit({"event": "attempt", **lvl})

            if ok:
                inner_ok = True
                result.update(solved=True, cert=cert, code=code, diag=diag,
                              final_level="L1" if i == 0 else strategy)
                break

            hint = repair_hint(diag)
            eid = r.get("id")
            seen_errs[eid] = seen_errs.get(eid, 0) + 1
            structural = r["route"] == "L3" or seen_errs[eid] >= budget["repeat_l3"]
            if structural:                                # same error persists → leave inner loop
                emit({"event": "escalate", "to": "L3",
                      "reason": f"{eid}×{seen_errs[eid]}"})
                break
            elif r["route"] == "L2":                      # different strategy, fresh thread
                strategy, history = "new_strategy", []
                emit({"event": "escalate", "to": "L2", "reason": r["id"]})
            else:                                         # L1 in-place repair
                strategy = "repair"
                history = history + [{"role": "assistant", "content": code},
                                     {"role": "user", "content": hint}]
                emit({"event": "escalate", "to": "L1", "reason": r["id"]})

        if inner_ok:
            break
        # inner exhausted / structural failure → regenerate barrier (L3)
        if b_idx < budget["barriers"] - 1 and calls < budget["max_calls"]:
            emit({"event": "regenerate_barrier", "after_cert": cert})
            new_cert = propose_fn(system, last_diag, list(certs_tried))
            if not new_cert or _cert_seen(new_cert, certs_tried):
                emit({"event": "propose_failed", "cert": new_cert})
                break
            cert = new_cert
            certs_tried.append(cert)
        else:
            break

    result["calls"] = calls
    result["diag"] = result["diag"] or last_diag
    if not result["solved"]:
        result["final_level"] = "partial"
    return result


# ─────────────────────────────────────────────────────────────────────────────
# Real implementations (LLM via call_api, Lean via lake)
# ─────────────────────────────────────────────────────────────────────────────
def _verified_recipes(family, cert):
    """Compile-verified bridging lemmas for this family from the self-evolve recipe
    store (mined by self_evolve.py). Empty string if the store is absent/empty, so
    the orchestrator has no hard dependency on it."""
    try:
        from self_evolve import recipes_block
        block = recipes_block(family, cert)
        return block + "\n\n" if block else ""
    except Exception:
        return ""


def _base_lean_prompt(system, cert, strategy, hint, extra=None):
    """Build the Lean-writer prompt. `extra` carries the synthesis-side context that
    generate_lean_proof used to pass (precomputed decrease quantity, certified set,
    discrete vs continuous statement hint) so the escalation path is a strict
    superset of the old linear prompt — never a regression for discrete systems."""
    fw = _task_framework(system)
    family = _cert_family(cert)
    extra = extra or {}
    # decrease quantity / certified set are cert-specific; if L3 has swapped in a
    # different certificate they are stale, so apply them only while cert matches.
    _applies = _norm_cert(extra.get("cert", cert)) == _norm_cert(cert)
    discrete = bool(system.get("discrete"))
    decrease = extra.get("lie_derivative", "") if _applies else ""
    decrease_line = (
        (f"One-step quantity: {decrease}\n" if discrete else
         f"Lie derivative / decrease quantity: {decrease}\n") if decrease else "")
    certified_set = extra.get("invariant_set", "") if _applies else ""
    set_line = f"Certified set: {certified_set}\n" if certified_set else ""
    statement_hint = (
        "For this DISCRETE system the conditions are inequalities about the map f itself "
        "(no derivatives needed in Lean): formalize x+ = f(x) as a function and prove the "
        "one-step inequality directly." if discrete else
        "Formalize the vector field componentwise; for the decrease condition you may state "
        "it as an inequality about the explicit closed-form derivative expression (already "
        "computed above) rather than re-deriving it via HasDerivAt, if that keeps the proof compiling.")
    strat_note = ""
    if strategy == "new_strategy":
        strat_note = (
            "\nYOUR PREVIOUS PROOF STRATEGY FAILED. Take a DIFFERENT approach this time: "
            "switch tactic family (nlinarith↔polyrith↔positivity), add the lemmas suggested "
            "below as explicit hints, or restate the goal more directly. Do not repeat the "
            f"previous tactic verbatim.\nTargeted guidance:\n{hint}\n")
    return (
        f"Generate a Lean 4 formal proof for this verified certificate.\n\n"
        f"Task: {fw['goal']}\n"
        f"Dynamics: {system['ode']}\n"
        f"State vars: {', '.join(system['state_vars'])}\n"
        f"Domain: {system.get('X_domain','')}\n"
        + (f"Unsafe set: {system['X_u_desc']}\n" if system.get('X_u_desc') else "")
        + f"Certificate: {cert}\n"
        + set_line
        + decrease_line
        + f"\nConditions to state and prove:\n{fw['conditions']}\n\n"
        f"{statement_hint}\n\n"
        f"Recommended skeleton for the {family} family:\n```lean\n{_TEMPLATES[family]}\n```\n\n"
        f"{_verified_recipes(family, cert + ' ' + system.get('ode', ''))}"
        f"{_POSDEF_RECIPE}\n\n"
        f"{_LEAN4_GUARD}\n\n"
        f"{error_kb_block()}\n"
        f"{strat_note}\n"
        f"Do NOT use bare `import Mathlib`; import specific modules. The proof MUST be "
        f"`sorry`-free (strict: a file with `sorry` is REJECTED). Output ONLY one Lean 4 code block."
    )


def make_real_writer(effort="high", write_retries=2, extra=None):
    """Real Lean writer. Guards against two failure modes seen with weak models:
    empty/truncated output (relay flakiness) and Lean 3 syntax — both get an
    internal re-ask with a stern correction, so they don't waste a Lean compile
    or get misrouted as a proof failure.

    `extra` (lie_derivative / invariant_set) is forwarded to every prompt build so
    the escalation writer keeps the synthesis-side context across L1/L2 attempts."""
    def _w(ctx):
        system, cert = ctx["system"], ctx["cert"]
        base = _base_lean_prompt(system, cert, ctx["strategy"], ctx["hint"], extra=extra)
        correction = ""
        code = ""
        for _ in range(write_retries + 1):
            messages = [{"role": "user", "content": base + correction}] + ctx["history"]
            try:
                reply, _ = call_api(lean4_system(system), messages, effort=effort,
                                    label=f"lean-{ctx['strategy']}")
            except Exception:
                reply = ""
            code = extract_lean_code(reply)
            if _looks_empty(code):
                correction = ("\n\nYour last reply had NO usable Lean 4 code. "
                              "Output exactly one ```lean ... ``` block with a complete proof.")
                continue
            if _looks_lean3(code):
                correction = ("\n\nYour last reply used LEAN 3 / mathlib3 syntax, which does "
                              "NOT compile. Rewrite in LEAN 4 + Mathlib4: " + _LEAN4_GUARD)
                continue
            break
        return code
    return _w


def make_real_compiler(tag="esc", strict_sorry=True, state_vars=None):
    seq = {"n": 0}

    def _c(code):
        seq["n"] += 1
        return lean_compile_check(code, f"{tag}{seq['n']}", strict_sorry=strict_sorry,
                                  audit=True, state_vars=state_vars)
    return _c


def make_real_proposer(effort="high", retries=2):
    def _p(system, lean_diag, prev_certs):
        prev = "; ".join(prev_certs)
        msg = (
            "A previous barrier certificate was numerically VERIFIED but could not be "
            "FORMALIZED in Lean 4. The Lean failure (last diagnostic):\n"
            f"{(lean_diag or '')[:800]}\n\n"
            f"Already-tried certificates (do NOT repeat): {prev}\n\n"
            "Propose a DIFFERENT certificate for the SAME system that is formalization-"
            "friendly: prefer a low-degree POLYNOMIAL form, avoid nested log/exp/trig, "
            "and leave a comfortable decrease margin. It must still satisfy the barrier "
            "conditions. Output JSON with an 'h' field (the certificate expression)."
        )
        for _ in range(retries + 1):
            reply, _e = call_api(proposer_system(system),
                                 [{"role": "user", "content": msg}],
                                 effort=effort, label="L3-reproposer")
            h = (parse_json_response(reply) or {}).get("h", "")
            if not h or _cert_seen(h, prev_certs):
                continue
            lv = local_verify(system, h, {"xu_points": [], "escape_points": []})
            if lv.get("passed"):       # never spend Lean on an unverified cert
                return h
        return None
    return _p


def _print_event(e):
    ev = e.get("event")
    if ev == "barrier":
        print(f"  [L0] barrier candidate #{e['idx']+1}: h = {e['cert']}")
    elif ev == "attempt":
        tag = "OK ✅" if e["compile_ok"] else f"FAIL → {e['route']} ({e['err']})"
        print(f"      attempt b{e['barrier']}.{e['inner']} [{e['strategy']}] {tag}")
    elif ev == "escalate":
        print(f"      ↑ escalate {e['to']}  ({e['reason']})")
    elif ev == "regenerate_barrier":
        print("  [L3] regenerating barrier (certificate formalization-hostile)…")
    elif ev == "budget_exhausted":
        print(f"  [stop] budget exhausted after {e['calls']} calls")
    elif ev == "propose_failed":
        print("  [L3] could not propose a new verified certificate — stopping")


def formalize_certificate(system, cert, *, final=None, budget=None, effort="high",
                          strict_sorry=True, on_event=_print_event):
    """End-to-end: formalize `cert` for `system` with real LLM + Lean, escalating.

    `final` (optional) is the synthesis result dict; its precomputed
    `lie_derivative` / `invariant_set` are forwarded into the writer prompt so the
    escalation path carries the same context the old generate_lean_proof did.
    """
    final = final or {}
    extra = {"cert": cert,
             "lie_derivative": final.get("lie_derivative", ""),
             "invariant_set": final.get("invariant_set", "")}
    return run_lean_escalation(
        system, cert,
        write_fn=make_real_writer(effort, extra=extra),
        compile_fn=make_real_compiler("esc", strict_sorry,
                                      state_vars=system.get("state_vars")),
        propose_fn=make_real_proposer(effort),
        budget=budget, on_event=on_event,
    )
