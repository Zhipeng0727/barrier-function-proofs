"""
auto_evolve.py — the UNATTENDED self-improvement loop. A multi-agent toolflow that
closes the circle: evolve recipes → formalize examples → on failure DISTILL the
minimal blocking lemma → mine it (oracle-verified) → re-inject → re-evaluate, until
the pass-rate stops moving or the frontier runs dry.

Agents (each GLM, each gated by a ground-truth oracle):
  formalizer        run_lean_escalation (writer/compiler/proposer)   [Lean compiler]
  obstruction-miner extract the minimal Lean sub-lemma from a failing proof+diag
  recipe-miner      self_evolve.mine_recipe (propose→compile→repair) [Lean compiler]

The obstruction-miner is the new piece: it turns an opaque proof failure into a
named, self-contained, COMPILE-CHECKABLE lemma the recipe-miner can attack in
isolation. Verified lemmas land in recipe_store.json and are injected into the next
formalization round via lean_escalation._verified_recipes.

Run:  python3 auto_evolve.py L4-014 B4-017 --rounds 3
"""
import json
import os
import sys
import time

from runtime_state import call_api, reset_tokens, TOKENS, API_CONFIG, PROVIDER
from barrier_core import parse_json_response
from dataset_loader import convert_manifest_record
from lean_escalation import (run_lean_escalation, make_real_writer,
                             make_real_proposer)
from lean_proof import lean_compile_check, _cert_family
from self_evolve import (load_store, save_store, mine_recipe, _log,
                         OBSTRUCTIONS, _FAMILY_IMPORTS)

MANIFEST = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"
HERE = os.path.dirname(os.path.abspath(__file__))
AUTO_LOG = os.path.join(HERE, "auto_evolve_history.jsonl")
EVAL_BUDGET = {"inner": 3, "barriers": 2, "max_calls": 5, "repeat_l3": 2}


def _load_systems(ids):
    d = json.load(open(MANIFEST, encoding="utf-8"))
    by_id = {r["id"]: r for r in d["core200"]}
    out = []
    for i in ids:
        s, _ = convert_manifest_record(by_id[i], None, {})
        if s and s.get("cert_gt"):
            out.append((i, s))
    return out


# ─────────────────────────────────────────────────────────────────────────────
# Formalize one example, CAPTURING the last failing (code, diag) for distillation
# ─────────────────────────────────────────────────────────────────────────────
def formalize_capture(system, cert, budget=EVAL_BUDGET):
    writer = make_real_writer(effort="high")
    last_fail = {"code": None, "diag": None}
    seq = {"n": 0}

    def cap_writer(ctx):
        code = writer(ctx)
        last_fail["_pending"] = code
        return code

    def cap_compiler(code):
        seq["n"] += 1
        ok, diag = lean_compile_check(code, f"auto{seq['n']}", strict_sorry=True)
        if not ok:
            last_fail["code"], last_fail["diag"] = code, diag
        return ok, diag

    res = run_lean_escalation(system, cert, write_fn=cap_writer,
                              compile_fn=cap_compiler,
                              propose_fn=make_real_proposer(effort="high"),
                              budget=budget, on_event=None)
    return res, last_fail


# ─────────────────────────────────────────────────────────────────────────────
# GLM agent: distill the minimal blocking lemma from a failing proof + diagnostic
# ─────────────────────────────────────────────────────────────────────────────
_DISTILL_SYS = (
    "You are a Lean 4 proof-failure analyst. Given a failed barrier/Lyapunov proof "
    "and its compiler diagnostic, you identify the SINGLE smallest self-contained "
    "lemma whose absence blocks the proof — the bridging fact about a transcendental "
    "(tanh/log/exp/sin/cos/sqrt) or an algebraic obstruction. You output it as a "
    "minimal Lean Prop over fresh real variables, NOT the whole proof."
)


def extract_obstruction(system, cert, code, diag):
    """Return {family, oid, goal, desc} for the minimal blocking lemma, or None."""
    if not diag:
        return None
    msg = (
        f"System dynamics: {system.get('ode','')}\nCertificate: {cert}\n\n"
        f"The Lean proof FAILED. Code:\n```lean\n{(code or '')[:1500]}\n```\n"
        f"Compiler diagnostic:\n{diag[:1200]}\n\n"
        "Identify the ONE minimal self-contained lemma that, if proven and supplied, "
        "would unblock this proof. State it as a Lean 4 Prop over fresh variables "
        "(x y t : ℝ) with any needed hypothesis as an arrow (e.g. `0 < x → ...`). "
        "Prefer the transcendental bridging fact if one is involved. "
        'Output JSON: {"family":"tanh|log|exp|trig|sqrt|poly", '
        '"oid":"<short_snake_id>", "goal":"<Lean Prop>", "desc":"<one line>"}.')
    try:
        reply, _ = call_api(_DISTILL_SYS, [{"role": "user", "content": msg}],
                            effort="high", label="distill-obstruction")
    except Exception:
        return None
    j = parse_json_response(reply) or {}
    if not j.get("goal") or not j.get("family"):
        return None
    j["oid"] = (j.get("oid") or "auto").replace(" ", "_")[:32]
    j.setdefault("desc", f"distilled from {system.get('name','?')}")
    return j


# ─────────────────────────────────────────────────────────────────────────────
# The unattended loop
# ─────────────────────────────────────────────────────────────────────────────
def _evaluate(systems):
    """Formalize all; return (n_solved, results[list of (id, solved, fail)])."""
    results = []
    for eid, s in systems:
        res, fail = formalize_capture(s, s["cert_gt"])
        results.append((eid, s, res["solved"], fail))
        print(f"    {eid}: {'✅ SOLVED' if res['solved'] else '❌ '+str(res['final_level'])}"
              f"  ({res['calls']} calls)")
    return sum(1 for r in results if r[2]), results


def auto_iterate(ids, families=("tanh", "log", "exp", "trig"), rounds=3):
    print(f"provider={PROVIDER} model={API_CONFIG['model']}  AUTO-EVOLVE\n"
          f"eval set: {ids}  | families: {families} | rounds: {rounds}\n")
    systems = _load_systems(ids)
    store = load_store()
    seen_obstructions = set(store.get("recipes", {}).keys())
    trajectory = []

    for rnd in range(1, rounds + 1):
        print(f"\n{'='*60}\nROUND {rnd}\n{'='*60}")

        # 1) mine the current seeded frontier for any not-yet-verified obstruction
        print("[1] mining seeded frontier…")
        for fam in families:
            for oid, goal, desc in OBSTRUCTIONS.get(fam, []):
                key = f"{fam}.{oid}"
                if store["recipes"].get(key, {}).get("verified"):
                    continue
                code, r, _d = mine_recipe(fam, oid, goal, desc)
                if code:
                    store["recipes"][key] = {"family": fam, "obstruction": oid,
                        "goal": goal, "desc": desc, "lean": code, "verified": True,
                        "rounds": r, "source": "seeded"}
                    save_store(store)

        # 2) evaluate the eval set with the current recipe store
        print("[2] evaluating eval set…")
        n_solved, results = _evaluate(systems)
        trajectory.append((rnd, n_solved, len(systems)))
        print(f"    → {n_solved}/{len(systems)} solved this round")

        # 3) distill obstructions from failures, mine them (the feedback edge)
        failures = [(eid, s, fail) for eid, s, solved, fail in results
                    if not solved and fail.get("diag")]
        if not failures:
            print("[3] no failures with diagnostics — converged."); break
        print(f"[3] distilling obstructions from {len(failures)} failure(s)…")
        new_verified = 0
        for eid, s, fail in failures:
            ob = extract_obstruction(s, s["cert_gt"], fail["code"], fail["diag"])
            if not ob:
                print(f"    {eid}: no obstruction distilled"); continue
            key = f"{ob['family']}.{ob['oid']}"
            if key in seen_obstructions or store["recipes"].get(key, {}).get("verified"):
                print(f"    {eid}: → {key} (already known)"); continue
            seen_obstructions.add(key)
            print(f"    {eid}: distilled {key}: {ob['goal'][:60]}")
            code, r, _d = mine_recipe(ob["family"], ob["oid"], ob["goal"],
                                      ob["desc"], max_rounds=4)
            if code:
                store["recipes"][key] = {"family": ob["family"],
                    "obstruction": ob["oid"], "goal": ob["goal"], "desc": ob["desc"],
                    "lean": code, "verified": True, "rounds": r,
                    "source": f"distilled:{eid}"}
                save_store(store)
                new_verified += 1
                print(f"      ✅ verified & stored {key}")
            else:
                print(f"      ✗ could not verify {key} in {r} rounds")
        _log({"round": rnd, "solved": n_solved, "total": len(systems),
              "new_recipes": new_verified, "out_tokens_cum": TOKENS["output"]})
        if new_verified == 0:
            print("    no new verified recipes — frontier dry, stopping."); break

    print(f"\n{'#'*60}\nAUTO-EVOLVE TRAJECTORY\n{'#'*60}")
    for rnd, ns, tot in trajectory:
        print(f"  round {rnd}: {ns}/{tot} solved")
    nver = sum(1 for v in store["recipes"].values() if v.get("verified"))
    print(f"recipe store: {nver} verified | out_tokens={TOKENS['output']}")
    return trajectory


if __name__ == "__main__":
    rounds = 3
    argv = sys.argv[1:]
    if "--rounds" in argv:
        ri = argv.index("--rounds")
        rounds = int(argv[ri + 1])
        argv = argv[:ri] + argv[ri + 2:]      # drop the flag AND its value
    args = [a for a in argv if not a.startswith("--")]
    reset_tokens()
    auto_iterate(args or ["L4-014", "B4-017"], rounds=rounds)
