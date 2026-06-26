"""
dataset_arena.py — competitive dataset construction. GLM proposes N candidates IN
PARALLEL; a dedicated ADVERSARY agent attacks each survivor (hunts a point where the
certificate fails); and three acceptance methods are run on the SAME proposal pool so
their datasets can be compared on an objective held-out metric.

Agents (GLM), oracles (ground truth):
  proposer (×N parallel)   propose a non-poly (system, cert)            [thread pool]
  adversary                find a point where V>0/V̇≤0 is VIOLATED       — GLM
  refuter (oracle)         numerically evaluate the adversary's points  — sympy/numpy
  dense auditor (oracle)   held-out: violation rate over a dense grid   — sympy/numpy

Acceptance methods compared (same pool, fair):
  A  naive       parse + cert sympifies                       (no oracle)
  B  strict      self_evolve._strict_validate                 (structural + local_verify)
  C  strict+adv  B AND survives the adversary                 (adversarial)

Objective comparison metric = mean dense-audit VIOLATION RATE of each method's kept
set (lower = more accurate dataset; this is what catches false positives a coarse
verifier lets through).

Run:  python3 dataset_arena.py tanh 8        # family, pool size N
"""
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor

import numpy as np
import sympy as sp

from runtime_state import call_api, reset_tokens, TOKENS, API_CONFIG, PROVIDER
from barrier_core import parse_json_response
from dataset_loader import _parse_equation_dynamics, _norm_expr
from self_evolve import _strict_validate, _FAMILY_FUNC

HERE = os.path.dirname(os.path.abspath(__file__))
ARENA_OUT = os.path.join(HERE, "arena_datasets.json")
TOL = 1e-6


# ─────────────────────────────────────────────────────────────────────────────
# Numeric core (the held-out oracle) — compile h, V̇ = ∇h·f to fast callables
# ─────────────────────────────────────────────────────────────────────────────
def _compile_numeric(system, cert):
    sv = system["state_vars"]
    syms = sp.symbols([v for v in sv])
    smap = dict(zip(sv, syms))
    h = sp.sympify(_norm_expr(cert), locals=smap)
    f = [sp.sympify(_norm_expr(fe), locals=smap) for fe in system["f_expr"]]
    vdot = sum(sp.diff(h, s) * fi for s, fi in zip(syms, f))
    hf = sp.lambdify(syms, h, "numpy")
    vf = sp.lambdify(syms, vdot, "numpy")
    return hf, vf, len(sv)


def dense_audit(system, cert, n=4000, box=2.5, seed_pts=None):
    """Held-out objective check: fraction of domain points violating V̇≤0 (decrease)
    or V>0 away from equilibrium. Robust to eval errors (NaN/inf points are skipped,
    counted toward 'undefined'). Returns dict with violation_rate."""
    try:
        hf, vf, dim = _compile_numeric(system, cert)
    except Exception as e:
        return {"violation_rate": 1.0, "error": f"compile {type(e).__name__}", "n": 0}
    rng = np.random.default_rng(12345)              # fixed seed → comparable across methods
    pts = rng.uniform(-box, box, size=(n, dim))
    if seed_pts:
        pts = np.vstack([np.array(seed_pts, dtype=float), pts])
    cols = [pts[:, i] for i in range(dim)]
    with np.errstate(all="ignore"):
        try:
            vd = np.asarray(vf(*cols), dtype=float)
            hv = np.asarray(hf(*cols), dtype=float)
        except Exception as e:
            return {"violation_rate": 1.0, "error": f"eval {type(e).__name__}", "n": 0}
    r2 = sum(c ** 2 for c in cols)
    away = r2 > 0.04                                 # skip a small ball around origin
    finite = np.isfinite(vd) & np.isfinite(hv)
    usable = finite & away
    nuse = int(usable.sum())
    if nuse == 0:
        return {"violation_rate": 1.0, "error": "no usable points", "n": 0}
    decr_viol = (vd[usable] > TOL).sum()             # V̇ should be ≤ 0
    pos_viol = (hv[usable] <= 0).sum()               # V should be > 0 away from eq
    vr = float((decr_viol + pos_viol) / nuse)
    return {"violation_rate": round(vr, 4), "decrease_viol": int(decr_viol),
            "pos_viol": int(pos_viol), "n": nuse,
            "undefined_frac": round(1 - finite.mean(), 3)}


# ─────────────────────────────────────────────────────────────────────────────
# GLM agent: parallel proposer
# ─────────────────────────────────────────────────────────────────────────────
def _propose_one(family, idx):
    allowed = ", ".join(sorted({"exp", "log", "sin", "cos", "tan", "sinh", "cosh",
                                "tanh", "sqrt", "Abs"}))
    sysp = ("You design SIMPLE 2-D continuous systems (x,y) with a CORRECT Lyapunov "
            f"certificate genuinely using {family}. Strict JSON only.")
    # vary the ask by idx so parallel proposals diversify (no RNG available in-proc)
    angle = ["with mild damping", "near a limit cycle", "with a saddle-free origin",
             "energy-shaping style", "gradient-flow style", "with a skew term",
             "slightly stiff", "textbook canonical"][idx % 8]
    msg = (f"Propose ONE system ({angle}) whose decrease genuinely involves {family}. "
           f"PLAIN infix math in x,y using only {allowed}, + - * / ** (). "
           "FORBIDDEN: poly()/min()/max()/sat()/sign()/undefined funcs/matrices. "
           "V>0 away from 0 and V̇≤0 along the flow. "
           'JSON: {"name":..., "ode":"dx/dt=..., dy/dt=...", "state_vars":["x","y"], '
           '"X_domain":"", "h":"<cert>"}.')
    try:
        reply, _ = call_api(sysp, [{"role": "user", "content": msg}],
                            effort="high", label=f"propose-{family}-{idx}")
        return parse_json_response(reply) or {}
    except Exception:
        return {}


def propose_n_parallel(family, n, workers=6):
    with ThreadPoolExecutor(max_workers=min(workers, n)) as ex:
        pool = list(ex.map(lambda i: _propose_one(family, i), range(n)))
    return [p for p in pool if p]


# ─────────────────────────────────────────────────────────────────────────────
# GLM agent: adversary / critic — hunt a point where the certificate fails
# ─────────────────────────────────────────────────────────────────────────────
_ADV_SYS = ("You are an ADVERSARIAL reviewer of Lyapunov certificates. Your job is to "
            "BREAK the claim by finding concrete state points where it fails — either "
            "V̇(x) > 0 (not decreasing) or V(x) ≤ 0 away from the equilibrium. You are "
            "skeptical by default and try hard to refute.")


def adversary_attack(system, cert, k=6):
    """GLM proposes challenge points; returns list of [x,y] floats to test."""
    msg = (f"System: {system.get('ode','')}\nClaimed Lyapunov certificate: V = {cert}\n"
           f"Equilibrium at origin. Find up to {k} concrete points (x,y) — especially "
           "near the boundary, along axes, or where the nonlinearity is strongest — "
           "where you suspect V̇>0 or V≤0. Be adversarial. "
           'Output JSON: {"points": [[x,y], ...], "reason":"<one line>"}.')
    try:
        reply, _ = call_api(_ADV_SYS, [{"role": "user", "content": msg}],
                            effort="high", label="adversary")
    except Exception:
        return []
    j = parse_json_response(reply) or {}
    pts = []
    for p in (j.get("points") or [])[:k]:
        try:
            pts.append([float(p[0]), float(p[1])])
        except Exception:
            continue
    return pts


def refute(system, cert, points):
    """Oracle: does ANY adversary point exhibit a REAL violation? Returns (broken, detail)."""
    if not points:
        return False, "no points"
    try:
        hf, vf, dim = _compile_numeric(system, cert)
    except Exception as e:
        return True, f"cert uncompilable: {type(e).__name__}"
    for p in points:
        try:
            with np.errstate(all="ignore"):
                vd = float(vf(*p)); hv = float(hf(*p))
        except Exception:
            continue
        if not (np.isfinite(vd) and np.isfinite(hv)):
            continue
        if (p[0] ** 2 + p[1] ** 2) > 0.04 and (vd > 1e-4 or hv <= 0):
            return True, f"@({p[0]:.3g},{p[1]:.3g}) Vdot={vd:.3g} V={hv:.3g}"
    return False, "adversary refuted (no real violation found)"


# ─────────────────────────────────────────────────────────────────────────────
# The arena: 3 methods on the SAME pool, compared on held-out audit
# ─────────────────────────────────────────────────────────────────────────────
def _naive_accept(rec):
    """Method A: parse + cert sympifies. No oracle. Builds a minimal system dict."""
    h = (rec.get("h") or "").strip()
    ode = (rec.get("ode") or "").strip()
    if not h or not ode:
        return None
    sv, f_expr, discrete, _ = _parse_equation_dynamics({"dynamics": ode})
    if sv is None:
        return None
    try:
        sp.sympify(_norm_expr(h), locals={v: sp.Symbol(v) for v in sv})
    except Exception:
        return None
    return {"name": rec.get("name", "naive"), "ode": ode, "state_vars": sv,
            "f_expr": f_expr, "X_domain": rec.get("X_domain", ""),
            "task_type": "lyapunov", "discrete": bool(discrete), "cert_gt": h}


def run_arena(family, n=8):
    reset_tokens()
    print(f"provider={PROVIDER} model={API_CONFIG['model']}  ARENA family={family} pool N={n}\n")
    print(f"[propose] firing {n} GLM proposals in parallel…")
    pool = propose_n_parallel(family, n)
    print(f"  got {len(pool)} non-empty proposals\n")

    methods = {"A_naive": [], "B_strict": [], "C_strict_adv": []}
    rows = []
    for i, rec in enumerate(pool):
        h = (rec.get("h") or "?")[:42]
        a = _naive_accept(rec)
        b, hb, rb = _strict_validate(rec, family)
        verdict = {"A": bool(a), "B": bool(b), "C": False}
        adv = "—"
        if a:
            methods["A_naive"].append(a)
        if b:
            methods["B_strict"].append(b)
            pts = adversary_attack(b, hb)
            broken, detail = refute(b, hb, pts)
            adv = f"{'BROKEN '+detail if broken else 'survived'} ({len(pts)}pts)"
            if not broken:
                verdict["C"] = True
                methods["C_strict_adv"].append(b)
        print(f"  cand {i:2d} h={h:44s} A={'✓' if verdict['A'] else '·'} "
              f"B={'✓' if verdict['B'] else '·'} C={'✓' if verdict['C'] else '·'}  adv:{adv}")
        rows.append({"h": rec.get("h"), "verdict": verdict, "adv": adv,
                     "strict_reason": rb if not b else None})

    # objective held-out comparison: mean dense-audit violation rate per method
    print(f"\n[audit] dense held-out violation-rate per kept set "
          f"(lower = more accurate)…")
    summary = {}
    for m, kept in methods.items():
        audits = [dense_audit(s, s["cert_gt"]) for s in kept]
        clean = [a for a in audits if a.get("n", 0) > 0]
        mvr = round(float(np.mean([a["violation_rate"] for a in clean])), 4) if clean else None
        clean_count = sum(1 for a in audits if a.get("violation_rate", 1.0) <= 0.01)
        summary[m] = {"kept": len(kept), "audited": len(clean),
                      "mean_violation_rate": mvr,
                      "clean_entries(≤1%viol)": clean_count}
        print(f"  {m:13s}: kept={len(kept):2d}  mean_viol_rate={mvr}  "
              f"clean(≤1%)={clean_count}")

    out = {"family": family, "pool": len(pool), "summary": summary, "rows": rows,
           "datasets": {m: [{"name": s.get("name"), "ode": s["ode"], "h": s["cert_gt"]}
                            for s in kept] for m, kept in methods.items()},
           "out_tokens": TOKENS["output"]}
    # merge into a persistent arena file keyed by family
    allres = {}
    if os.path.exists(ARENA_OUT):
        try:
            allres = json.load(open(ARENA_OUT))
        except Exception:
            allres = {}
    allres[family] = out
    json.dump(allres, open(ARENA_OUT, "w"), indent=2, ensure_ascii=False)

    print(f"\n{'#'*60}\nARENA VERDICT (family={family})\n{'#'*60}")
    print(f"  pool {len(pool)} → A_naive {summary['A_naive']['kept']} | "
          f"B_strict {summary['B_strict']['kept']} | "
          f"C_strict_adv {summary['C_strict_adv']['kept']}")
    print(f"  mean held-out violation rate: "
          f"A={summary['A_naive']['mean_violation_rate']} "
          f"B={summary['B_strict']['mean_violation_rate']} "
          f"C={summary['C_strict_adv']['mean_violation_rate']}")
    print(f"  → saved {ARENA_OUT}  (out_tokens={TOKENS['output']})")
    return out


if __name__ == "__main__":
    fam = sys.argv[1] if len(sys.argv) > 1 else "tanh"
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    run_arena(fam, n)
