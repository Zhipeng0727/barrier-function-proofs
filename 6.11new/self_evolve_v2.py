#!/usr/bin/env python3
"""
self_evolve_v2.py — self-iterating evolving agent for Lean4 barrier/Lyapunov
certificate verification.

    EXPLORE  → attempt proofs on prioritized frontier
    ANALYZE  → categorize failures → extract obstruction goals
    MINE     → mine recipes (GLM primary, GPT fallback)
    VERIFY   → lean_compile_check oracle (inside mine_recipe)
    RE-INJECT → retry failed systems with new recipes
    CONVERGE → stop after K consecutive dry rounds

Run:
    python3 self_evolve_v2.py                          # full autonomous loop
    python3 self_evolve_v2.py --resume                 # resume from checkpoint
    python3 self_evolve_v2.py --untested-only           # just the 9 untested
    python3 self_evolve_v2.py --max-rounds 10 --budget 500000
"""

import json, os, sys, time, argparse, re

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from runtime_state import (call_api, reset_tokens, TOKENS, API_CONFIG,
                           PROVIDER, PROVIDERS, select_provider)
from barrier_core import parse_json_response
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import (load_store, save_store, mine_recipe, _MINER_SYS,
                         OBSTRUCTIONS, _FAMILY_IMPORTS, ESCALATE_PROVIDER)
from auto_expand_evolve import attempt_proof, analyze_obstructions
from call_log import init_run as _init_call_log

HERE = os.path.dirname(os.path.abspath(__file__))
EXPANSION_PATH = os.path.join(HERE, "lean4_expansion_v1.json")
CHECKPOINT_PATH = os.path.join(HERE, "evolve_v2_checkpoint.json")
RESULTS_PATH = os.path.join(HERE, "evolve_v2_results.json")
LOG_PATH = os.path.join(HERE, "evolve_v2.log")

DEFAULT_MAX_ROUNDS = 15
DEFAULT_K_DRY = 3
DEFAULT_TOKEN_BUDGET = 500_000
DEFAULT_BATCH_SIZE = 8

UNTESTED_IDS = {"PJ-005", "PJ-006", "PJ-007", "PJ-008",
                "PF-002", "PF-003", "PK-003", "PM-003", "PC-004"}


# ─────────────────────────────────────────────────────────────────────────────
# Logging
# ─────────────────────────────────────────────────────────────────────────────

def _log_event(event_type, message):
    entry = {"time": time.strftime("%H:%M:%S"), "event": event_type,
             "message": message, "tokens": TOKENS.get("output", 0)}
    with open(LOG_PATH, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


# ─────────────────────────────────────────────────────────────────────────────
# Dual-provider escalation for attempt_proof
# ─────────────────────────────────────────────────────────────────────────────

def attempt_proof_escalated(system, max_repairs=2):
    """attempt_proof via default provider, then retry via GPT if it fails.

    GPT escalation uses max_repairs=1 (not 2) because GPT produces ~15K tokens
    per attempt through the relay, making multiple repairs too slow."""
    result = attempt_proof(system, max_repairs=max_repairs)
    if result["proved"]:
        return result

    fallback = ESCALATE_PROVIDER if ESCALATE_PROVIDER in PROVIDERS else "openai"
    if fallback not in PROVIDERS:
        return result

    _log_event("escalate", f"{system['id']}: GLM failed, trying {fallback}")
    print(f"    ↑ escalating to {fallback} ({PROVIDERS[fallback]['model']})")

    old_provider = PROVIDER
    try:
        select_provider(fallback)
        result_fb = attempt_proof(system, max_repairs=1)
        if result_fb["proved"]:
            result_fb["_escalated_from"] = old_provider
            return result_fb
    except Exception as e:
        _log_event("escalate_fail", f"{system['id']}: {type(e).__name__}: {e}")
        print(f"    ↑ escalation failed: {type(e).__name__}")
    finally:
        select_provider(old_provider)

    return result


# ─────────────────────────────────────────────────────────────────────────────
# Obstruction extraction (adapted for expansion manifest)
# ─────────────────────────────────────────────────────────────────────────────

_DISTILL_SYS = (
    "You are a Lean 4 proof-failure analyst. Given a failed barrier/Lyapunov proof "
    "and its compiler diagnostic, identify the SINGLE smallest self-contained "
    "lemma whose absence blocks the proof. Output it as a minimal Lean Prop "
    "over fresh real variables, NOT the whole proof."
)


def extract_obstruction_from_expansion(sys_dict, error):
    """Distill a minimal blocking lemma from an expansion system's failure."""
    if not error or len(error) < 20:
        return None
    msg = (
        f"System: {sys_dict.get('dynamics','')}\n"
        f"Certificate: {sys_dict.get('certificate','')}\n"
        f"Proof strategy: {sys_dict.get('proof_core','')}\n\n"
        f"Compiler diagnostic:\n{error[:1200]}\n\n"
        "Identify the ONE minimal self-contained lemma that would unblock this. "
        "State it as a Lean 4 Prop over fresh variables (x y t : ℝ). "
        'Output JSON: {"family":"tanh|log|exp|trig|sqrt|poly|rational|piecewise|convex", '
        '"oid":"<short_snake_id>", "goal":"<Lean Prop>", "desc":"<one line>"}.'
    )
    try:
        reply, _ = call_api(_DISTILL_SYS, [{"role": "user", "content": msg}],
                            effort="high", label="distill-obs", retries=3)
    except Exception:
        return None
    j = parse_json_response(reply) or {}
    if not j.get("goal") or not j.get("family"):
        return None
    j["oid"] = (j.get("oid") or "auto").replace(" ", "_")[:32]
    j.setdefault("desc", f"distilled from {sys_dict.get('id','?')}")
    return j


# ─────────────────────────────────────────────────────────────────────────────
# Frontier prioritization
# ─────────────────────────────────────────────────────────────────────────────

def _infer_needed_families(sys_dict):
    text = " ".join([
        sys_dict.get("dynamics", ""),
        sys_dict.get("certificate", ""),
        sys_dict.get("proof_core", ""),
        sys_dict.get("dynamics_class", ""),
    ]).lower()
    families = set()
    if any(k in text for k in ("tanh", "sinh", "cosh")):
        families.add("tanh")
    if "log" in text:
        families.add("log")
    if "exp" in text and "log" not in text:
        families.add("exp")
    if any(k in text for k in ("sin", "cos", "trig")):
        families.add("trig")
    if "sqrt" in text:
        families.add("sqrt")
    if any(k in text for k in ("min(", "max(", "piecewise", "pwa")):
        families.add("piecewise")
    if any(k in text for k in ("div", "ratio", "/(", "monod", "michaelis", "holling")):
        families.add("rational")
    if any(k in text for k in ("convex", "weight", "jensen")):
        families.add("convex")
    if not families:
        families.add("poly")
    return families


def compute_frontier(expansion, store, system_results):
    verified_families = set()
    for v in store.get("recipes", {}).values():
        if v.get("verified"):
            verified_families.add(v.get("family", ""))

    frontier = []
    for sys in expansion:
        sid = sys["id"]
        if system_results.get(sid, {}).get("proved"):
            continue

        needs = _infer_needed_families(sys)
        have = needs & verified_families
        score = len(have) / max(len(needs), 1)

        vcc = sys.get("verif_cond_class", "poly")
        if vcc == "poly":
            score += 0.3
        elif vcc == "transcendental":
            score += 0.1
        if sid in UNTESTED_IDS:
            score += 0.2

        frontier.append((score, sys))

    frontier.sort(key=lambda x: -x[0])
    return frontier


# ─────────────────────────────────────────────────────────────────────────────
# Checkpoint (crash-safe)
# ─────────────────────────────────────────────────────────────────────────────

def save_checkpoint(state):
    tmp = CHECKPOINT_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=2, ensure_ascii=False)
    os.replace(tmp, CHECKPOINT_PATH)


def load_checkpoint():
    if os.path.exists(CHECKPOINT_PATH):
        with open(CHECKPOINT_PATH, encoding="utf-8") as f:
            return json.load(f)
    return {}


def compress_round_state(round_num, round_results, new_recipes, store):
    proved_ids = [r["id"] for r in round_results if r.get("proved")]
    failed_ids = [r["id"] for r in round_results if not r.get("proved")]
    return {
        "round": round_num,
        "proved": proved_ids,
        "failed": failed_ids,
        "new_recipe_keys": [nr["key"] for nr in new_recipes],
        "recipe_count": sum(1 for v in store.get("recipes", {}).values()
                           if v.get("verified")),
        "tokens_cum": TOKENS.get("output", 0),
        "ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
    }


# ─────────────────────────────────────────────────────────────────────────────
# Budget check
# ─────────────────────────────────────────────────────────────────────────────

def check_budget(budget):
    used = TOKENS.get("output", 0)
    if used >= budget:
        print(f"  [BUDGET] exhausted: {used}/{budget} output tokens")
        return False
    pct = 100 * (budget - used) / budget
    if pct < 10:
        print(f"  [BUDGET] {pct:.0f}% remaining ({used}/{budget})")
    return True


# ─────────────────────────────────────────────────────────────────────────────
# Main loop
# ─────────────────────────────────────────────────────────────────────────────

def main_loop(args):
    with open(EXPANSION_PATH, encoding="utf-8") as f:
        expansion = json.load(f)["expansion_v1"]

    checkpoint = load_checkpoint() if args.resume else {}
    start_round = checkpoint.get("last_round", 0) + 1
    system_results = checkpoint.get("system_results", {})
    dry_streak = checkpoint.get("dry_streak", 0)
    round_history = checkpoint.get("rounds", [])

    if args.untested_only:
        expansion = [s for s in expansion if s["id"] in UNTESTED_IDS]

    store = load_store()
    recipe_count = sum(1 for v in store.get("recipes", {}).values() if v.get("verified"))

    tag = "untested" if args.untested_only else "full"
    if args.resume:
        tag += "_resume"
    _init_call_log(
        tag=tag,
        provider=PROVIDER,
        model=API_CONFIG["model"],
        fallback=ESCALATE_PROVIDER,
        systems=len(expansion),
        recipes=recipe_count,
        budget=args.budget,
        max_rounds=args.max_rounds,
        k_dry=args.k_dry,
        no_escalate=args.no_escalate,
    )

    print(f"{'=' * 70}")
    print(f"SELF-EVOLVE V2 AGENT")
    print(f"  Provider: {PROVIDER} ({API_CONFIG['model']})")
    fb = ESCALATE_PROVIDER if ESCALATE_PROVIDER in PROVIDERS else "openai"
    print(f"  Fallback: {fb} ({PROVIDERS.get(fb, {}).get('model', '?')})")
    print(f"  Systems: {len(expansion)} | Recipes: {recipe_count}")
    print(f"  Resume round: {start_round} | Dry streak: {dry_streak}")
    print(f"  Budget: {args.budget} tok | Max rounds: {args.max_rounds} | K_dry: {args.k_dry}")
    print(f"{'=' * 70}\n")

    for rnd in range(start_round, start_round + args.max_rounds):
        if not check_budget(args.budget):
            break

        print(f"\n{'=' * 60}")
        print(f"ROUND {rnd}")
        print(f"{'=' * 60}")

        # ── STEP 1: EXPLORE ──────────────────────────────────────────
        print(f"\n[1/5] EXPLORE")
        store = load_store()
        frontier = compute_frontier(expansion, store, system_results)
        batch = frontier[:args.batch_size]

        if not batch:
            print("  Frontier empty — all proved or exhausted.")
            break

        print(f"  Trying {len(batch)} systems (priority order):")
        round_results = []
        for score, sys in batch:
            if not check_budget(args.budget):
                break
            sid = sys["id"]
            print(f"\n  [{sid}] {sys['title']} (score={score:.2f})")
            reset_tokens()
            if args.no_escalate:
                result = attempt_proof(sys, max_repairs=2)
            else:
                result = attempt_proof_escalated(sys, max_repairs=2)
            result["id"] = sid
            result["title"] = sys["title"]
            round_results.append(result)
            system_results[sid] = {
                "proved": result["proved"],
                "error": result.get("error"),
                "calls": result.get("calls"),
                "tokens": result.get("tokens"),
            }
            mark = "PROVED" if result["proved"] else "FAILED"
            print(f"    → {mark}  calls={result.get('calls')} "
                  f"tok={result.get('tokens')}")

        # ── STEP 2: ANALYZE ──────────────────────────────────────────
        print(f"\n[2/5] ANALYZE")
        failures = [r for r in round_results if not r.get("proved")]
        if failures:
            obs = analyze_obstructions(failures)
            for cat, items in obs.items():
                n = len(items) if isinstance(items, list) else items
                print(f"  {cat}: {n}")
        else:
            print("  No failures — all proved!")

        # ── STEP 3: MINE ─────────────────────────────────────────────
        print(f"\n[3/5] MINE")
        new_recipes = []
        seen_keys = set(store.get("recipes", {}).keys())

        for r in failures:
            if not check_budget(args.budget):
                break
            if not r.get("error"):
                continue

            sys_dict = next((s for _, s in frontier if s["id"] == r["id"]), None)
            if not sys_dict:
                continue

            ob = extract_obstruction_from_expansion(sys_dict, r["error"])
            if not ob:
                print(f"  [{r['id']}] no obstruction distilled")
                continue

            key = f"{ob['family']}.{ob['oid']}"
            if key in seen_keys:
                print(f"  [{r['id']}] → {key} (already known)")
                continue
            seen_keys.add(key)
            print(f"  [{r['id']}] distilled: {key}")
            print(f"    goal: {ob['goal'][:80]}")
            _log_event("mine_start", f"{key}: {ob['goal'][:60]}")

            code, rounds_used, diag = mine_recipe(
                ob["family"], ob["oid"], ob["goal"], ob["desc"],
                max_rounds=4, escalate=True, escalate_rounds=2,
            )

            if code:
                store["recipes"][key] = {
                    "family": ob["family"],
                    "obstruction": ob["oid"],
                    "goal": ob["goal"],
                    "desc": ob["desc"],
                    "lean": code,
                    "verified": True,
                    "rounds": rounds_used,
                    "source": f"v2:{r['id']}:R{rnd}",
                }
                save_store(store)
                new_recipes.append({"key": key, "rounds": rounds_used})
                print(f"    → VERIFIED {key} (round {rounds_used})")
                _log_event("recipe_verified", key)
            else:
                print(f"    → could not verify in {rounds_used} rounds")
                _log_event("recipe_failed", f"{key}: {diag[:80] if diag else 'no diag'}")

        if not failures:
            print("  No failures to mine from.")

        # ── STEP 4: VERIFY (inline in mine_recipe) ───────────────────
        print(f"\n[4/5] VERIFY: {len(new_recipes)} new recipe(s)")

        # ── STEP 5: RE-INJECT ────────────────────────────────────────
        if new_recipes:
            print(f"\n[5/5] RE-INJECT")
            new_fams = {nr["key"].split(".")[0] for nr in new_recipes}
            retries = []
            for r in failures:
                sys_dict = next((s for _, s in frontier if s["id"] == r["id"]), None)
                if sys_dict and _infer_needed_families(sys_dict) & new_fams:
                    retries.append((sys_dict, r))

            for sys_dict, old_r in retries[:5]:
                if not check_budget(args.budget):
                    break
                sid = sys_dict["id"]
                print(f"  Retrying [{sid}]...")
                reset_tokens()
                if args.no_escalate:
                    result = attempt_proof(sys_dict, max_repairs=2)
                else:
                    result = attempt_proof_escalated(sys_dict, max_repairs=2)
                if result["proved"]:
                    system_results[sid]["proved"] = True
                    print(f"    → PROVED on re-inject!")
                    _log_event("reinject_proved", sid)
                else:
                    print(f"    → still failed")
        else:
            print(f"\n[5/5] RE-INJECT: skipped (no new recipes)")

        # ── CONVERGENCE ──────────────────────────────────────────────
        if len(new_recipes) == 0:
            dry_streak += 1
        else:
            dry_streak = 0

        rs = compress_round_state(rnd, round_results, new_recipes, store)
        round_history.append(rs)

        save_checkpoint({
            "last_round": rnd,
            "rounds": round_history,
            "system_results": system_results,
            "dry_streak": dry_streak,
            "total_tokens": TOKENS.get("output", 0),
        })

        n_proved = sum(1 for v in system_results.values() if v.get("proved"))
        n_total = len(expansion)
        print(f"\n{'─' * 50}")
        print(f"ROUND {rnd} SUMMARY")
        print(f"  Proved this round: "
              f"{sum(1 for r in round_results if r.get('proved'))}")
        print(f"  New recipes: {len(new_recipes)}")
        print(f"  Cumulative: {n_proved}/{n_total} "
              f"({100 * n_proved / max(n_total, 1):.0f}%)")
        print(f"  Dry streak: {dry_streak}/{args.k_dry}")
        print(f"  Tokens out: {TOKENS.get('output', 0)}")
        print(f"{'─' * 50}")

        if dry_streak >= args.k_dry:
            print(f"\n[CONVERGED] {args.k_dry} consecutive rounds, no new recipes.")
            break

    _final_report(expansion, system_results, store, round_history)


# ─────────────────────────────────────────────────────────────────────────────
# Final report
# ─────────────────────────────────────────────────────────────────────────────

def _final_report(expansion, system_results, store, rounds):
    proved = [sid for sid, v in system_results.items() if v.get("proved")]
    failed = [sid for sid, v in system_results.items() if not v.get("proved")]
    recipe_count = sum(1 for v in store.get("recipes", {}).values() if v.get("verified"))

    report = {
        "agent": "self_evolve_v2",
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "model": API_CONFIG.get("model", "?"),
        "fallback": PROVIDERS.get(ESCALATE_PROVIDER, {}).get("model", "?"),
        "proved_count": len(proved),
        "failed_count": len(failed),
        "total": len(expansion),
        "prove_rate": f"{100 * len(proved) / max(len(expansion), 1):.1f}%",
        "recipe_count": recipe_count,
        "rounds_run": len(rounds),
        "proved_ids": sorted(proved),
        "failed_ids": sorted(failed),
        "rounds": rounds,
    }

    with open(RESULTS_PATH, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)

    print(f"\n{'=' * 70}")
    print(f"FINAL REPORT")
    print(f"  Proved: {len(proved)}/{len(expansion)} ({report['prove_rate']})")
    print(f"  Recipes: {recipe_count}")
    print(f"  Rounds: {len(rounds)}")
    print(f"  Proved: {', '.join(sorted(proved)) or '(none)'}")
    print(f"  Saved: {RESULTS_PATH}")
    print(f"{'=' * 70}")


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Self-evolving Lean4 verification agent v2")
    parser.add_argument("--max-rounds", type=int, default=DEFAULT_MAX_ROUNDS)
    parser.add_argument("--k-dry", type=int, default=DEFAULT_K_DRY)
    parser.add_argument("--budget", type=int, default=DEFAULT_TOKEN_BUDGET)
    parser.add_argument("--batch-size", type=int, default=DEFAULT_BATCH_SIZE)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--untested-only", action="store_true")
    parser.add_argument("--no-escalate", action="store_true",
                        help="Skip GPT escalation — GLM only (faster)")
    parser.add_argument("--provider", type=str, default=None)
    args = parser.parse_args()

    if args.provider:
        select_provider(args.provider)

    main_loop(args)


if __name__ == "__main__":
    main()
