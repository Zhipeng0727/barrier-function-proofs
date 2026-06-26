"""
features.py — extract the routing features the selector keys on, from a
SYSTEMS-style system dict (+ certificate). Features are detected from the actual
expressions (sympy atoms), not trusted from manifest metadata, so the agent also
works on systems with no `meta` (the paper's SYSTEMS catalog, ad-hoc inputs).
"""
from __future__ import annotations

import sympy as sp

# sympy transcendental function heads that put a problem outside z3/MILP's sound
# fragment (decidable real arithmetic) and into dReal/Lean territory.
_TRANSCENDENTAL = (
    sp.exp, sp.log, sp.sin, sp.cos, sp.tan, sp.cot, sp.sec, sp.csc,
    sp.asin, sp.acos, sp.atan, sp.atan2, sp.acot,
    sp.sinh, sp.cosh, sp.tanh, sp.asinh, sp.acosh, sp.atanh,
)

_SP_LOCALS = {
    "exp": sp.exp, "log": sp.log, "sin": sp.sin, "cos": sp.cos, "tan": sp.tan,
    "sqrt": sp.sqrt, "Abs": sp.Abs, "sinh": sp.sinh, "cosh": sp.cosh,
    "tanh": sp.tanh, "asinh": sp.asinh, "acosh": sp.acosh, "atanh": sp.atanh,
    "atan": sp.atan, "atan2": sp.atan2, "asin": sp.asin, "acos": sp.acos,
    "Min": sp.Min, "Max": sp.Max,
}


def _parse(expr_str: str, state_vars: list):
    syms = {v: sp.Symbol(v, real=True) for v in state_vars}
    try:
        return sp.sympify(str(expr_str).replace("^", "**"), locals={**syms, **_SP_LOCALS})
    except Exception:
        return None


def _classify_exprs(exprs, state_vars) -> dict:
    """Return {transcendental, has_abs_min_max, rational, polynomial} over a set
    of expression strings."""
    syms = [sp.Symbol(v, real=True) for v in state_vars]
    transcendental = has_piecewise = rational = False
    polynomial = True
    for es in exprs:
        if not es:
            continue
        e = _parse(es, state_vars)
        if e is None or not isinstance(e, sp.Basic):
            polynomial = False
            continue
        if any(e.has(fn) for fn in _TRANSCENDENTAL):
            transcendental = True
            polynomial = False
        if e.has(sp.Abs) or e.has(sp.Min) or e.has(sp.Max) or e.has(sp.sign):
            has_piecewise = True
            polynomial = False
        try:
            if not e.is_polynomial(*syms):
                polynomial = False
                if e.is_rational_function(*syms) and not transcendental and not has_piecewise:
                    rational = True
        except Exception:
            polynomial = False
    return {
        "transcendental": transcendental,
        "piecewise": has_piecewise,
        "rational": rational,
        "polynomial": polynomial and not transcendental and not has_piecewise,
    }


def extract_features(system: dict, cert: str | None = None) -> dict:
    """The routing feature vector. `cert` defaults to system['cert_gt']."""
    state_vars = system["state_vars"]
    cert = cert if cert is not None else system.get("cert_gt")
    meta = system.get("meta") or {}

    exprs = list(system.get("f_expr") or [])
    if cert:
        exprs = exprs + [cert]
    cls = _classify_exprs(exprs, state_vars)

    xu = (system.get("X_u_expr") or "").strip()
    feats = {
        "dim": len(state_vars),
        "discrete": bool(system.get("discrete")),
        "task_type": system.get("task_type", "barrier"),
        "has_unsafe": bool(xu) and xu not in ("False", "false"),
        "psd_ok": bool(system.get("psd_ok")),
        # expression-class (detected, with manifest label as a cross-check)
        "transcendental": cls["transcendental"],
        "piecewise": cls["piecewise"],
        "rational": cls["rational"],
        "polynomial": cls["polynomial"],
        # manifest hints (may be absent)
        "verif_cond_class": meta.get("verif_cond_class"),
        "dynamics_class": meta.get("dynamics_class"),
        "parametric": bool(meta.get("parametric")),
        "has_cert": bool(cert),
    }
    # decidable-real-arithmetic fragment z3/MILP handle soundly
    feats["decidable_real"] = (feats["polynomial"] or feats["rational"]) and not feats["transcendental"]
    return feats


def feature_summary(feats: dict) -> str:
    tags = []
    tags.append(f"dim{feats['dim']}")
    tags.append("disc" if feats["discrete"] else "cont")
    tags.append(feats["task_type"][:3])
    for k in ("transcendental", "rational", "piecewise", "polynomial"):
        if feats[k]:
            tags.append(k[:5])
    return " ".join(tags)
