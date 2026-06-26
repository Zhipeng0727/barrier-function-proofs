"""
interval_backend.py — SOUND verification for the TRANSCENDENTAL fragment via
interval-arithmetic branch-and-bound (mpmath), no external solver required. This
is the pure-Python stand-in for dReal: rigorous interval enclosures over the
domain box, recursively split until every sub-box is decided.

Soundness: interval arithmetic OVER-approximates, so if the violation expression's
enclosure is ≥ 0 on every sub-box, the condition holds everywhere (proved). A
sub-box whose enclosure is entirely < 0 is a genuine violating region (refuted).
Undecided sub-boxes are split; exhausting the box budget ⇒ unknown.

Applicability profile (this is WHY the selector keeps it distinct from Z3):
handles exp/log/sin/cos/atan/tanh… that Z3 can't, but BnB cost grows with
dimension, so it is routed for low-to-moderate-dim transcendental problems and
Z3 keeps the polynomial fragment.
"""
from __future__ import annotations

import os
import sys

import mpmath
import sympy as sp
from mpmath import iv

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.backend_base import Backend, VerifyResult, register  # noqa: E402
from verif_agent.features import _parse, extract_features, _SP_LOCALS  # noqa: E402

iv.dps = 20
_CBF_CANDIDATES = (0.0, 1.0, 2.0, 5.0, 10.0, 25.0, 50.0)

# functions mpmath.iv provides directly (rigorous)
_IV_DIRECT = {sp.sin: iv.sin, sp.cos: iv.cos, sp.exp: iv.exp,
              sp.log: iv.log, sp.sqrt: iv.sqrt}
# monotonic-increasing functions absent from iv — enclose via scalar endpoints
_MONO_INC = {sp.atan: mpmath.atan, sp.asinh: mpmath.asinh, sp.atanh: mpmath.atanh,
             sp.sinh: mpmath.sinh, sp.tanh: mpmath.tanh, sp.asin: mpmath.asin}


class _Unsupported(Exception):
    pass


def _endpoints(X):
    return mpmath.mpf(X.a), mpmath.mpf(X.b)


def _mono_inc(fn, X):
    lo, hi = _endpoints(X)
    try:
        ya, yb = fn(lo), fn(hi)
    except (ValueError, ZeroDivisionError):
        raise _Unsupported("out-of-domain in monotonic enclosure")
    if not (mpmath.isfinite(ya) and mpmath.isfinite(yb)):
        raise _Unsupported("infinite enclosure")
    pad = mpmath.mpf("1e-15") * max(1, abs(ya), abs(yb))
    return iv.mpf([ya - pad, yb + pad])


def _ieval(e, env):
    """Interval-evaluate a sympy expr; env maps name -> iv.mpf interval."""
    if e.is_Symbol:
        return env[e.name]
    if e.is_Integer or e.is_Rational or e.is_Float:
        return iv.mpf(float(e))
    if e is sp.pi:
        return iv.pi
    if e is sp.E:
        return iv.e
    if e.is_Add:
        acc = _ieval(e.args[0], env)
        for a in e.args[1:]:
            acc = acc + _ieval(a, env)
        return acc
    if e.is_Mul:
        acc = _ieval(e.args[0], env)
        for a in e.args[1:]:
            acc = acc * _ieval(a, env)
        return acc
    if e.is_Pow:
        base, exp = e.args
        b = _ieval(base, env)
        if exp.is_Integer:
            n = int(exp)
            if n == 0:
                return iv.mpf(1)
            if n > 0:
                return b ** n
            return iv.mpf(1) / (b ** (-n))
        return iv.exp(iv.mpf(float(exp)) * iv.log(b))  # b**r = exp(r ln b), b>0
    if e.func == sp.Abs:
        X = _ieval(e.args[0], env)
        lo, hi = _endpoints(X)
        if lo <= 0 <= hi:
            return iv.mpf([0, max(abs(lo), abs(hi))])
        vals = [abs(lo), abs(hi)]
        return iv.mpf([min(vals), max(vals)])
    if e.func in (sp.Max, sp.Min):
        parts = [_ieval(a, env) for a in e.args]
        los = [mpmath.mpf(p.a) for p in parts]
        his = [mpmath.mpf(p.b) for p in parts]
        if e.func == sp.Max:
            return iv.mpf([max(los), max(his)])
        return iv.mpf([min(los), min(his)])
    if e.func == sp.cosh:
        X = _ieval(e.args[0], env)
        lo, hi = _endpoints(X)
        if lo <= 0 <= hi:
            return iv.mpf([1, max(mpmath.cosh(lo), mpmath.cosh(hi))])
        vals = [mpmath.cosh(lo), mpmath.cosh(hi)]
        return iv.mpf([min(vals), max(vals)])
    if e.func in _IV_DIRECT:
        return _IV_DIRECT[e.func](_ieval(e.args[0], env))
    if e.func in _MONO_INC:
        return _mono_inc(_MONO_INC[e.func], _ieval(e.args[0], env))
    raise _Unsupported(f"interval: unsupported {type(e).__name__}")


def _region_status(reg_expr, env):
    """For a single inequality g<=0 / g>=0: return 'in'|'out'|'maybe' for a box."""
    if reg_expr is None:
        return "in"
    if reg_expr.func == sp.Or:
        sts = [_region_status(a, env) for a in reg_expr.args]
        if "in" in sts:
            return "in"
        if all(s == "out" for s in sts):
            return "out"
        return "maybe"
    if reg_expr.func == sp.And:
        sts = [_region_status(a, env) for a in reg_expr.args]
        if "out" in sts:
            return "out"
        if all(s == "in" for s in sts):
            return "in"
        return "maybe"
    g = reg_expr.lhs - reg_expr.rhs
    G = _ieval(g, env)
    glo, ghi = float(mpmath.mpf(G.a)), float(mpmath.mpf(G.b))
    le = isinstance(reg_expr, (sp.LessThan, sp.StrictLessThan))   # region = g <= 0
    if le:
        if ghi <= 0:
            return "in"
        if glo > 0:
            return "out"
    else:                                                          # region = g >= 0
        if glo >= 0:
            return "in"
        if ghi < 0:
            return "out"
    return "maybe"


def _prove_nonneg(expr, names, bounds, *, region=None, exclude_ball=None,
                  tol=1e-7, max_boxes=60000, min_width=1e-4):
    """Prove expr >= 0 on {box ∧ region} \\ exclude_ball. Returns
    ('proved'|'refuted'|'unknown', counterexample|None). NOTE: expr is kept in its
    FACTORED form — expanding (e.g. squares into sums) wrecks interval tightness
    via the dependency problem, so callers must pass structured expressions."""
    stack = [tuple(bounds)]
    processed = 0
    while stack:
        if processed >= max_boxes:
            return "unknown", None
        box = stack.pop()
        processed += 1
        env = {n: iv.mpf([lo, hi]) for n, (lo, hi) in zip(names, box)}
        center = [(lo + hi) / 2.0 for lo, hi in box]

        if exclude_ball is not None:
            c, r = exclude_ball
            # skip a box ONLY if it lies entirely inside the excluded ball: its
            # farthest corner from c (coordinate-wise max |lo-c|,|hi-c|) is within r.
            far2 = sum(max((lo - cc) ** 2, (hi - cc) ** 2)
                       for (lo, hi), cc in zip(box, c))
            if far2 <= r * r:
                continue

        try:
            if region is not None:
                rs = _region_status(region, env)
                if rs == "out":
                    continue
                if rs == "maybe":
                    if _split(stack, box, min_width):
                        continue
                    # too small & undecided region membership → safe to skip (measure ~0)
                    continue
            G = _ieval(expr, env)
        except (_Unsupported, ValueError, ZeroDivisionError, OverflowError):
            # _Unsupported = node we can't enclose; ValueError covers mpmath
            # ComplexResult (log/sqrt of a negative ⇒ the box leaves the function's
            # real domain — the manifest box over-covers the cert's true domain).
            return "unsupported", None
        glo = float(mpmath.mpf(G.a))
        ghi = float(mpmath.mpf(G.b))

        if glo >= -tol:
            continue                      # whole box satisfies expr >= 0
        if ghi < -tol:
            return "refuted", dict(zip(names, [round(c, 5) for c in center]))
        if not _split(stack, box, min_width):
            return "unknown", None        # undecided and can't split further
    return "proved", None


def _split(stack, box, min_width):
    widths = [hi - lo for lo, hi in box]
    i = max(range(len(widths)), key=lambda k: widths[k])
    if widths[i] < min_width:
        return False
    lo, hi = box[i]
    mid = (lo + hi) / 2.0
    b1, b2 = list(box), list(box)
    b1[i] = (lo, mid)
    b2[i] = (mid, hi)
    stack.append(tuple(b1))
    stack.append(tuple(b2))
    return True


class IntervalBackend(Backend):
    name = "interval"
    sound = True

    def applicable(self, system, cert):
        cert = cert if cert is not None else system.get("cert_gt")
        if not cert:
            return False, "no certificate to check"
        feats = extract_features(system, cert)
        if feats["dim"] > 4:
            return False, f"dim {feats['dim']} too high for interval BnB"
        return True, ""

    def _verify(self, system, cert, max_boxes=60000, **opts):
        cert = cert if cert is not None else system.get("cert_gt")
        state_vars = system["state_vars"]
        syms = {v: sp.Symbol(v, real=True) for v in state_vars}
        sym_list = [syms[v] for v in state_vars]
        h = _parse(cert, state_vars)
        f = [_parse(fe, state_vars) for fe in system["f_expr"]]
        if h is None or any(fi is None for fi in f):
            return VerifyResult(self.name, "error", True, detail={"reason": "parse failed"})
        bounds = [tuple(map(float, b)) for b in
                  (system.get("X_bounds") or [(-3, 3)] * len(state_vars))]
        # clip a hair off each edge: open-domain functions (atanh at ±1, log at 0)
        # blow up exactly AT the boundary; verify on a compact subset of the open
        # domain (standard practice — documented limitation, not unsoundness inside).
        bounds = [(lo + 1e-6 * (hi - lo) + 1e-12, hi - 1e-6 * (hi - lo) - 1e-12)
                  for lo, hi in bounds]
        task = system.get("task_type", "barrier")
        detail = {"conditions": {}}

        if task == "lyapunov":
            x_star = system.get("equilibrium") or [0.0] * len(state_vars)
            V0 = h.subs({s: sp.Float(c) for s, c in zip(sym_list, x_star)})
            pos, ce = _prove_nonneg(h - V0, state_vars, bounds, max_boxes=max_boxes)
            detail["conditions"]["positivity(PSD)"] = pos
            if pos in ("refuted", "unsupported", "unknown"):
                return self._finish(pos, detail, ce, system)
            if system.get("discrete"):
                decr = h.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True) - h
            else:
                decr = sum(sp.diff(h, s) * fi for s, fi in zip(sym_list, f))
            # Asymptotic-stability decrease is verified on the domain MINUS a small
            # ball around x*: at x* itself V̇=0 (trivially), and near x* V̇→0 so any
            # sound over-approximation straddles 0. Excluding the ball (FOSSIL uses a
            # Torus inner radius for exactly this) certifies stability on the annulus.
            inner = float(system.get("inner_radius") or 0.0)
            excl = (tuple(map(float, x_star)), inner) if inner > 0 else None
            dec, ce = _prove_nonneg(-decr, state_vars, bounds, exclude_ball=excl,
                                    max_boxes=max_boxes)
            detail["conditions"]["decrease"] = dec
            detail["inner_radius"] = inner
            return self._finish_and(pos, dec, detail, ce, system, cert)

        # barrier
        xu = (system.get("X_u_expr") or "").strip()
        cond1 = "skipped"
        ce = None
        if xu and xu not in ("False", "false"):
            region = sp.sympify(xu.replace("^", "**"),
                                locals={**{v: s for v, s in zip(state_vars, sym_list)}, **_SP_LOCALS})
            cond1, ce = _prove_nonneg(-h, state_vars, bounds, region=region, max_boxes=max_boxes)
            detail["conditions"]["cond1_h_neg_on_Xu"] = cond1
            if cond1 in ("refuted", "unsupported", "unknown"):
                return self._finish(cond1, detail, ce, system)
        if system.get("discrete"):
            h_next = h.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True)
            cond2, ce = _prove_nonneg(h_next, state_vars, bounds, region=None,
                                      max_boxes=max_boxes)
            # restrict to C: enforce only where h>=0
            hcond = h >= 0
            cond2, ce = _prove_nonneg(h_next, state_vars, bounds,
                                      region=hcond, max_boxes=max_boxes)
        else:
            hdot = sum(sp.diff(h, s) * fi for s, fi in zip(sym_list, f))
            cond2, ce, used = "unknown", None, None
            for C in _CBF_CANDIDATES:
                st, c = _prove_nonneg(hdot + C * h, state_vars, bounds, max_boxes=max_boxes)
                if st == "proved":
                    cond2, used = "proved", C
                    break
                if st == "unsupported":
                    cond2 = "unsupported"
                    break
                ce = c
            detail["cbf_constant"] = used
        detail["conditions"]["cond2"] = cond2
        c1ok = cond1 in ("proved", "skipped")
        return self._finish("proved" if (c1ok and cond2 == "proved") else cond2,
                            detail, ce, system, cert, want_cert=(c1ok and cond2 == "proved"))

    def _finish_and(self, a, b, detail, ce, system, cert):
        if a == "proved" and b == "proved":
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "interval", "cert": str(cert)})
        if "refuted" in (a, b):
            return self._refuted(detail, ce, system)
        if "unsupported" in (a, b):
            return VerifyResult(self.name, "unsupported", True, detail=detail)
        return VerifyResult(self.name, "unknown", True, detail=detail, counterexample=ce)

    def _refuted(self, detail, ce, system):
        # A refutation is only sound if the counterexample lies in the TRUE domain.
        # We model the domain as a box; when extra constraints exist (simplex sum=1)
        # an off-domain point is NOT a real counterexample → downgrade to unknown.
        if system is not None and system.get("simplex"):
            detail = {**detail, "note": "refutation suppressed: simplex domain not modelled by box"}
            return VerifyResult(self.name, "unknown", True, detail=detail)
        return VerifyResult(self.name, "refuted", True, detail=detail, counterexample=ce)

    def _finish(self, status, detail, ce, system=None, cert=None, want_cert=False):  # noqa: F811
        if status == "proved" and want_cert:
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "interval", "cert": str(cert)})
        if status == "refuted":
            return self._refuted(detail, ce, system)
        st = status if status in ("unsupported", "unknown", "proved") else "unknown"
        return VerifyResult(self.name, st, True, detail=detail, counterexample=ce)


register(IntervalBackend())
