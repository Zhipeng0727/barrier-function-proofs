"""
agent_arena.py — CONTROLLED comparison of agent architectures on the recipe-mining
task (prove a minimal Lean bridging lemma until it COMPILES).

Controlled variables (held identical across every architecture):
  * obstruction test set (same goals)            * effort = "high"
  * proposer BUDGET B per obstruction (= #GLM    * oracle = lean_compile_check(strict_sorry)
    proposal calls allowed)                       * SOS hint text (self_evolve._SOS_HINTS)
  * per-family imports

The ONLY thing that varies is the architecture — how the B proposals are spent and
what extra signal each gets. Six architectures (a 2×2 of {depth|breadth}×{no-hint|SOS}
plus single-shot baseline and a critic-debate top):

  A_single        B independent single-shots, no repair, no hint   (pure sampling)
  B_sequential    B sequential REPAIR rounds (depth), no hint
  C_seq_sos       sequential repair + family SOS hints
  D_parallel      breadth: rounds×width=B parallel candidates, no hint
  E_parallel_sos  parallel + SOS hints                              (the reinforced miner)
  F_debate_sos    parallel + SOS + a CRITIC agent between rounds (proposer↔critic debate)

Metric: solve-rate over the test set; ties broken by rounds-to-solve and tokens.
Critic calls are reported separately (F spends extra GLM but the user opted to ignore
GLM cost — so we compare capability AND show the cost honestly).

Run:  python3 agent_arena.py --budget 4 --width 2
"""
import json
import os
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

from runtime_state import call_api, reset_tokens, TOKENS, API_CONFIG, PROVIDER
from lean_proof import extract_lean_code, lean_compile_check
from self_evolve import _MINER_SYS, _miner_prompt, _FAMILY_IMPORTS, _SOS_HINTS

HERE = os.path.dirname(os.path.abspath(__file__))
ARENA_OUT = os.path.join(HERE, "agent_arena_results.json")

# ── controlled obstruction test set: spread of difficulty across families ──
# (goal strings are self-contained Lean Props over fresh reals x y t)
TESTSET = [
    ("exp", "exp_pos", "0 < Real.exp x", "easy"),
    ("trig", "sin_cos_sq", "Real.sin t ^ 2 + Real.cos t ^ 2 = 1", "easy"),
    ("log", "log_sub_one", "0 < x → Real.log x ≤ x - 1", "medium"),
    ("exp", "exp_add_one", "1 + x ≤ Real.exp x", "medium"),
    ("tanh", "tanh_sign", "0 ≤ y * Real.tanh y", "hard"),
    ("log", "log_self_lower", "0 < x → 1 - 1 / x ≤ Real.log x", "hard"),
    ("poly", "logistic_inv",
     "∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → 0 ≤ (38/10)*x*(1-x) ∧ (38/10)*x*(1-x) ≤ 1", "hard"),
]


# ── shared primitive: one proposal, compiled (the controlled atom) ──
def _propose(ob, prior, sos_on, variant, tag, effort="high"):
    fam, oid, goal, _ = ob
    imports = _FAMILY_IMPORTS.get(fam, "")
    # control SOS: _miner_prompt always reads _SOS_HINTS[fam]; to run a NO-HINT arm we
    # temporarily blank that family's hint so the prompt text is identical minus SOS.
    saved = _SOS_HINTS.get(fam)
    if not sos_on and saved is not None:
        _SOS_HINTS[fam] = ""
    try:
        prompt = _miner_prompt(fam, goal, oid, imports, prior, variant)
    finally:
        if not sos_on and saved is not None:
            _SOS_HINTS[fam] = saved
    try:
        reply, _ = call_api(_MINER_SYS, [{"role": "user", "content": prompt}],
                            effort=effort, label=f"arena-{tag}")
    except Exception as e:
        return False, "", f"API {type(e).__name__}"
    code = extract_lean_code(reply)
    ok, diag = lean_compile_check(code, f"arena_{oid}_{tag}", strict_sorry=True)
    return ok, code, diag


def _carry(results):
    """Pick the most informative failure (longest diag) to seed the next round."""
    fails = [r for r in results if r and r[1]]
    if not fails:
        return None
    best = max(fails, key=lambda r: len(r[2] or ""))
    return {"code": best[1], "diag": best[2] or ""}


# ── critic agent (for F): analyse failures, emit one targeted fix instruction ──
_CRITIC_SYS = ("You are a skeptical Lean 4 proof CRITIC. Given failed attempts and "
               "their compiler errors, you state in 2-3 sentences the single most "
               "likely root cause and the concrete fix (a real lemma name or a tactic "
               "change). You do NOT write the whole proof — just the diagnosis.")


def _critique(ob, results):
    fam, oid, goal, _ = ob
    fails = [r for r in results if r and not r[0]]
    if not fails:
        return ""
    blob = "\n\n".join(f"attempt:\n{(r[1] or '')[:600]}\nerror:\n{(r[2] or '')[:400]}"
                       for r in fails[:2])
    try:
        reply, _ = call_api(_CRITIC_SYS, [{"role": "user", "content":
            f"Goal: {goal}\n\n{blob}\n\nWhat is the root cause and the concrete fix?"}],
            effort="high", label=f"critic-{oid}")
        return "CRITIC GUIDANCE (address this): " + reply.strip()[:500]
    except Exception:
        return ""


# ── the six architectures (uniform signature) ──
def arch_single(ob, B, width):
    n = 0
    for i in range(B):
        n += 1
        ok, code, _ = _propose(ob, None, False, i, f"{ob[1]}_A_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


def _sequential(ob, B, sos_on, tagc):
    n, prior = 0, None
    for i in range(B):
        n += 1
        ok, code, diag = _propose(ob, prior, sos_on, i, f"{ob[1]}_{tagc}_{i}")
        if ok:
            return {"solved": True, "rounds": i + 1, "proposer_calls": n, "critic_calls": 0}
        prior = {"code": code, "diag": diag}
    return {"solved": False, "rounds": B, "proposer_calls": n, "critic_calls": 0}


def arch_sequential(ob, B, width):
    return _sequential(ob, B, False, "B")


def arch_seq_sos(ob, B, width):
    return _sequential(ob, B, True, "C")


def _parallel(ob, B, width, sos_on, critic_on, tagc):
    n, c, prior = 0, 0, None
    rounds = max(1, B // width)
    for rnd in range(rounds):
        results = [None] * width
        with ThreadPoolExecutor(max_workers=width) as ex:
            futs = {ex.submit(_propose, ob, prior, sos_on, rnd * width + v,
                              f"{ob[1]}_{tagc}_r{rnd}c{v}"): v for v in range(width)}
            for fut in as_completed(futs):
                results[futs[fut]] = fut.result()
        n += width
        win = next((r for r in results if r and r[0]), None)
        if win:
            return {"solved": True, "rounds": rnd + 1, "proposer_calls": n, "critic_calls": c}
        prior = _carry(results)
        if critic_on and rnd < rounds - 1:
            guidance = _critique(ob, results)
            c += 1
            if guidance and prior:
                prior = {**prior, "diag": (prior["diag"] + "\n\n" + guidance)[:1400]}
    return {"solved": False, "rounds": rounds, "proposer_calls": n, "critic_calls": c}


def arch_parallel(ob, B, width):
    return _parallel(ob, B, width, False, False, "D")


def arch_parallel_sos(ob, B, width):
    return _parallel(ob, B, width, True, False, "E")


def arch_debate_sos(ob, B, width):
    return _parallel(ob, B, width, True, True, "F")


ARCHS = [
    ("A_single", arch_single),
    ("B_sequential", arch_sequential),
    ("C_seq_sos", arch_seq_sos),
    ("D_parallel", arch_parallel),
    ("E_parallel_sos", arch_parallel_sos),
    ("F_debate_sos", arch_debate_sos),
]


def main(budget=4, width=2):
    print(f"provider={PROVIDER} model={API_CONFIG['model']}  AGENT ARENA\n"
          f"controlled: budget B={budget} proposer calls/obstruction, width={width}, "
          f"effort=high, oracle=strict_sorry\n test set ({len(TESTSET)}): "
          f"{', '.join(o[1] for o in TESTSET)}\n")
    grid = {}                          # arch -> {oid -> result}
    for arch_name, fn in ARCHS:
        reset_tokens()
        print(f"\n{'='*60}\n{arch_name}\n{'='*60}")
        t0 = time.time()
        row, solved = {}, 0
        for ob in TESTSET:
            r = fn(ob, budget, width)
            r["tokens"] = TOKENS["output"]
            row[ob[1]] = r
            solved += int(r["solved"])
            mark = f"✅ r{r['rounds']}" if r["solved"] else "❌"
            print(f"  {ob[1]:16s} [{ob[3]:6s}] {mark}  "
                  f"calls={r['proposer_calls']}+{r['critic_calls']}c")
        dt = round(time.time() - t0)
        pcalls = sum(v["proposer_calls"] for v in row.values())
        ccalls = sum(v["critic_calls"] for v in row.values())
        grid[arch_name] = {"row": row, "solved": solved, "n": len(TESTSET),
                           "proposer_calls": pcalls, "critic_calls": ccalls,
                           "out_tokens": TOKENS["output"], "wall_s": dt}
        json.dump(grid, open(ARENA_OUT, "w"), indent=2, ensure_ascii=False, default=str)
        print(f"  → {arch_name}: {solved}/{len(TESTSET)} solved | "
              f"calls={pcalls}+{ccalls}c | {TOKENS['output']} tok | {dt}s")

    # ── comparison matrix + ranking ──
    print(f"\n\n{'#'*66}\nCONTROLLED COMPARISON  (B={budget}, width={width})\n{'#'*66}")
    oids = [o[1] for o in TESTSET]
    hdr = "arch".ljust(16) + "".join(f"{o[:10]:>11s}" for o in oids) + "  solve"
    print(hdr); print("-" * len(hdr))
    for arch_name, _ in ARCHS:
        g = grid[arch_name]
        cells = ""
        for oid in oids:
            r = g["row"][oid]
            cells += f"{('r'+str(r['rounds']) if r['solved'] else '·'):>11s}"
        print(arch_name.ljust(16) + cells + f"   {g['solved']}/{g['n']}")
    print("\nrank (solve-rate, then fewer proposer calls, then fewer tokens):")
    ranked = sorted(ARCHS, key=lambda a: (-grid[a[0]]["solved"],
                    grid[a[0]]["proposer_calls"], grid[a[0]]["out_tokens"]))
    for i, (arch_name, _) in enumerate(ranked, 1):
        g = grid[arch_name]
        print(f"  {i}. {arch_name:16s} {g['solved']}/{g['n']} solved | "
              f"{g['proposer_calls']}+{g['critic_calls']}c calls | "
              f"{g['out_tokens']} tok | {g['wall_s']}s")
    print(f"\nsaved {ARENA_OUT}")
    return grid


if __name__ == "__main__":
    B = int(sys.argv[sys.argv.index("--budget") + 1]) if "--budget" in sys.argv else 4
    W = int(sys.argv[sys.argv.index("--width") + 1]) if "--width" in sys.argv else 2
    main(B, W)
