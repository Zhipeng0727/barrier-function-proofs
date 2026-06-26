"""
z3_backend.py — SOUND verification for the polynomial fragment via Z3's nonlinear
real arithmetic (nlsat is a decision procedure for polynomial real arithmetic, so
an `unsat` counterexample search is a real proof).

Strategy: for each barrier/Lyapunov condition we ask Z3 to FIND a counterexample
inside the domain box. `unsat` ⇒ the condition holds everywhere (proved, sound).
`sat` ⇒ a concrete violating point (refuted). `unknown`/timeout ⇒ escalate.

Gated to the decidable fragment: transcendental functions (exp/sin/cos/log/atan…),
Abs/Min/Max, and non-integer powers route elsewhere (dReal). This keeps every
"proved" Z3 emits genuinely sound.

Barrier Condition 2 uses the exponential-CBF family ḣ(x) ≥ -C·h(x) (comparison
lemma ⇒ C invariant). Proving it for ANY C in a candidate ladder certifies
invariance; only a genuine boundary point (h=0 ∧ ḣ<0) counts as a refutation.
"""
from __future__ import annotations

import os
import sys

import sympy as sp
import z3

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.backend_base import Backend, VerifyResult, register  # noqa: E402
from verif_agent.features import extract_features, _parse, _SP_LOCALS  # noqa: E402

_CBF_CANDIDATES = (0.0, 1.0, 2.0, 5.0, 10.0, 25.0, 50.0)
_DEFAULT_TIMEOUT_MS = 8000


class _Unsupported(Exception):
    pass


def _to_z3(e, zvars):
    """Translate a polynomial sympy expression to a Z3 real term."""
    if e.is_Symbol:
        if e.name not in zvars:
            raise _Unsupported(f"free symbol {e.name}")
        return zvars[e.name]
    if e.is_Integer:
        return z3.RealVal(int(e))
    if e.is_Rational:
        return z3.RealVal(int(e.p)) / z3.RealVal(int(e.q))
    if e.is_Float:
        return z3.RealVal(str(e))
    if e.is_NumberSymbol:           # pi, E, ...
        raise _Unsupported("transcendental constant")
    if e.is_Add:
        acc = _to_z3(e.args[0], zvars)
        for a in e.args[1:]:
            acc = acc + _to_z3(a, zvars)
        return acc
    if e.is_Mul:
        acc = _to_z3(e.args[0], zvars)
        for a in e.args[1:]:
            acc = acc * _to_z3(a, zvars)
        return acc
    if e.is_Pow:
        base, exp = e.args
        if not exp.is_Integer:
            raise _Unsupported(f"non-integer power {exp}")
        n = int(exp)
        b = _to_z3(base, zvars)
        if n == 0:
            return z3.RealVal(1)
        if n < 0:
            raise _Unsupported("negative power (rational)")
        acc = b
        for _ in range(n - 1):
            acc = acc * b
        return acc
    raise _Unsupported(f"unsupported node {type(e).__name__}")


def _sign_term(expr, zvars):
    """A polynomial Z3 term with the SAME SIGN as `expr`, for comparison vs 0.
    For a rational expr = N/D, sign(N/D) == sign(N·D) for any D≠0, so N·D keeps the
    problem inside Z3's polynomial decision procedure. Polynomial expr ⇒ D=1 ⇒ N."""
    num, den = sp.fraction(sp.together(expr))
    n = _to_z3(sp.expand(num), zvars)
    if den == 1 or den.is_Number:
        # constant denominator: sign(N/c) == sign(N·c); fold the constant in
        return n * _to_z3(sp.expand(den), zvars) if not den.is_Number else (
            n if den > 0 else -n)
    return n * _to_z3(sp.expand(den), zvars)


def _num_term(expr, zvars):
    """Numerator of expr as a Z3 term (for the equality expr==0 ⟺ N==0, D≠0)."""
    num, _ = sp.fraction(sp.together(expr))
    return _to_z3(sp.expand(num), zvars)


def _rel_to_z3(rel, zvars):
    """Translate a sympy relational / And / Or into a Z3 boolean."""
    if rel.func == sp.Or:
        return z3.Or([_rel_to_z3(a, zvars) for a in rel.args])
    if rel.func == sp.And:
        return z3.And([_rel_to_z3(a, zvars) for a in rel.args])
    if rel is sp.true:
        return z3.BoolVal(True)
    if rel is sp.false:
        return z3.BoolVal(False)
    # compare (lhs - rhs) against 0 via the sign-preserving polynomial term,
    # so rational set descriptions (e.g. N/D >= c) stay decidable.
    s = _sign_term(rel.lhs - rel.rhs, zvars)
    z = z3.RealVal(0)
    if isinstance(rel, sp.StrictLessThan):
        return s < z
    if isinstance(rel, sp.LessThan):
        return s <= z
    if isinstance(rel, sp.StrictGreaterThan):
        return s > z
    if isinstance(rel, sp.GreaterThan):
        return s >= z
    if isinstance(rel, sp.Equality):
        return _num_term(rel.lhs - rel.rhs, zvars) == z
    raise _Unsupported(f"relation {type(rel).__name__}")


def _model_val(m, zv):
    try:
        v = m.eval(zv, model_completion=True)
        if z3.is_rational_value(v):
            return round(float(v.numerator_as_long()) / float(v.denominator_as_long()), 5)
        if z3.is_algebraic_value(v):
            a = v.approx(8)
            return round(float(a.numerator_as_long()) / float(a.denominator_as_long()), 5)
        return round(float(str(v)), 5)
    except Exception:
        return None


def _pole_in_box(exprs, zvars, box, timeout_ms=3000):
    """True if any expr's denominator can vanish inside the box. The N·D sign
    identity holds only where D≠0; a pole inside the domain means the certificate
    is undefined there, so we must NOT certify (and must NOT false-refute) — caller
    returns 'unsupported'."""
    for expr in exprs:
        den = sp.fraction(sp.together(expr))[1]
        if den == 1 or den.is_Number:
            continue
        try:
            d = _to_z3(sp.expand(den), zvars)
        except _Unsupported:
            return True
        s = z3.Solver()
        s.set("timeout", int(timeout_ms))
        for c in box:
            s.add(c)
        s.add(d == 0)
        if s.check() == z3.sat:
            return True
    return False


def _search_ce(constraints, zvars, timeout_ms):
    """Return ('proved'|'refuted'|'unknown', counterexample_or_None)."""
    s = z3.Solver()
    s.set("timeout", int(timeout_ms))
    for c in constraints:
        s.add(c)
    r = s.check()
    if r == z3.unsat:
        return "proved", None
    if r == z3.sat:
        m = s.model()
        return "refuted", {n: _model_val(m, zv) for n, zv in zvars.items()}
    return "unknown", None


class Z3Backend(Backend):
    name = "z3"
    sound = True

    def applicable(self, system, cert):
        cert = cert if cert is not None else system.get("cert_gt")
        if not cert:
            return False, "no certificate to check"
        feats = extract_features(system, cert)
        if feats["transcendental"]:
            return False, "transcendental — outside Z3 decidable fragment (use dReal/interval)"
        if feats["piecewise"]:
            return False, "Abs/Min/Max piecewise — needs case split / MILP"
        if not (feats["polynomial"] or feats["rational"]):
            return False, "non-polynomial/rational — use dReal/interval"
        return True, ""

    def _verify(self, system, cert, timeout_ms=_DEFAULT_TIMEOUT_MS, **opts):
        cert = cert if cert is not None else system.get("cert_gt")
        state_vars = system["state_vars"]
        zvars = {v: z3.Real(v) for v in state_vars}
        syms = {v: sp.Symbol(v, real=True) for v in state_vars}
        sym_list = [syms[v] for v in state_vars]

        h = _parse(cert, state_vars)
        f = [_parse(fe, state_vars) for fe in system["f_expr"]]
        if h is None or any(fi is None for fi in f):
            return VerifyResult(self.name, "error", True,
                                detail={"reason": "parse failed"})

        bounds = system.get("X_bounds") or [(-3, 3)] * len(state_vars)
        box = []
        for v, (lo, hi) in zip(state_vars, bounds):
            box += [zvars[v] >= z3.RealVal(str(lo)), zvars[v] <= z3.RealVal(str(hi))]
        # simplex domain: states live on {sum x_i = 1, x_i >= 0}. Adding the
        # equality both restricts proofs to the real domain and makes any
        # counterexample genuinely on-domain (else z3 could refute off-simplex).
        if system.get("simplex"):
            box.append(z3.Sum([zvars[v] for v in state_vars]) == z3.RealVal(1))

        task = system.get("task_type", "barrier")
        detail = {"conditions": {}}

        try:
            if task == "lyapunov":
                return self._verify_lyapunov(system, h, f, sym_list, zvars, box,
                                             state_vars, timeout_ms, detail)
            return self._verify_barrier(system, h, f, sym_list, zvars, box,
                                        state_vars, timeout_ms, detail)
        except _Unsupported as u:
            return VerifyResult(self.name, "unsupported", True, detail={"reason": str(u)})

    # ── barrier (continuous Nagumo / discrete one-step) ────────────────────
    def _verify_barrier(self, system, h, f, sym_list, zvars, box, state_vars,
                        timeout_ms, detail):
        discrete = bool(system.get("discrete"))
        hdot_chk = (h.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True) if discrete
                    else sum(sp.diff(h, s) * fi for s, fi in zip(sym_list, f)))
        if _pole_in_box([h, hdot_chk], zvars, box):
            return VerifyResult(self.name, "unsupported", True,
                                detail={"reason": "certificate has a pole inside the domain box"})
        # Condition 1: h < 0 on X_u  → search box ∧ Xu ∧ (h ≥ 0)
        xu = (system.get("X_u_expr") or "").strip()
        cond1 = "skipped"
        ce1 = None
        if xu and xu not in ("False", "false"):
            xu_expr = sp.sympify(xu.replace("^", "**"),
                                 locals={**{v: s for v, s in zip(state_vars, sym_list)}, **_SP_LOCALS})
            cons = box + [_rel_to_z3(xu_expr, zvars), _sign_term(h, zvars) >= 0]
            cond1, ce1 = _search_ce(cons, zvars, timeout_ms)
            detail["conditions"]["cond1_h_neg_on_Xu"] = cond1
            if cond1 == "refuted":
                return VerifyResult(self.name, "refuted", True, detail=detail,
                                    counterexample=ce1)

        # Condition 2
        if discrete:
            # h(f(x)) ≥ 0 on C: search box ∧ (h ≥ 0) ∧ (h∘f < 0)
            h_next = h.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True)
            cons = box + [_sign_term(h, zvars) >= 0, _sign_term(h_next, zvars) < 0]
            cond2, ce2 = _search_ce(cons, zvars, timeout_ms)
            detail["conditions"]["cond2_invariance"] = cond2
        else:
            # exponential-CBF: ḣ + C·h ≥ 0 over the box, for some C
            hdot = sum(sp.diff(h, s) * fi for s, fi in zip(sym_list, f))
            cond2, ce2, used_c = "unknown", None, None
            for C in _CBF_CANDIDATES:
                cons = box + [_sign_term(hdot + C * h, zvars) < 0]
                st, _ = _search_ce(cons, zvars, timeout_ms)
                if st == "proved":
                    cond2, used_c = "proved", C
                    break
            if cond2 != "proved":
                # genuine refutation only on the boundary h=0 ∧ ḣ<0
                cons = box + [_num_term(h, zvars) == 0, _sign_term(hdot, zvars) < 0]
                st, ce2 = _search_ce(cons, zvars, timeout_ms)
                cond2 = "refuted" if st == "refuted" else ("proved" if st == "proved" else "unknown")
            detail["conditions"]["cond2_nagumo"] = cond2
            detail["cbf_constant"] = used_c

        if cond2 == "refuted":
            return VerifyResult(self.name, "refuted", True, detail=detail, counterexample=ce2)

        c1ok = cond1 in ("proved", "skipped")
        if c1ok and cond2 == "proved":
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "z3", "cert": str(system.get("cert_gt")),
                                             "conditions": detail["conditions"]})
        return VerifyResult(self.name, "unknown", True, detail=detail)

    # ── Lyapunov ───────────────────────────────────────────────────────────
    def _verify_lyapunov(self, system, V, f, sym_list, zvars, box, state_vars,
                        timeout_ms, detail):
        x_star = system.get("equilibrium") or [0.0] * len(state_vars)
        decr_chk = (V.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True) - V
                    if system.get("discrete")
                    else sum(sp.diff(V, s) * fi for s, fi in zip(sym_list, f)))
        if _pole_in_box([V, decr_chk], zvars, box):
            return VerifyResult(self.name, "unsupported", True,
                                detail={"reason": "certificate has a pole inside the domain box"})
        V0 = V.subs({s: sp.Float(c) for s, c in zip(sym_list, x_star)})
        Vsh = V - V0  # shifted so V(x*) = 0

        # positivity: V_sh > 0 away from x*  → box ∧ dist²>eps² ∧ (V_sh ≤ 0)
        eps2 = 1e-4
        dist2 = sum((s - sp.Float(c))**2 for s, c in zip(sym_list, x_star))
        away = _to_z3(sp.expand(dist2), zvars) > z3.RealVal(str(eps2))
        z = z3.RealVal(0)
        if system.get("psd_ok"):
            pos_cons = box + [away, _sign_term(Vsh, zvars) < z]
        else:
            pos_cons = box + [away, _sign_term(Vsh, zvars) <= z]
        pos, ce_pos = _search_ce(pos_cons, zvars, timeout_ms)
        detail["conditions"]["positivity"] = pos
        if pos == "refuted":
            return VerifyResult(self.name, "refuted", True, detail=detail, counterexample=ce_pos)

        # decrease
        if system.get("discrete"):
            Vnext = V.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True)
            decr = Vnext - V
        else:
            decr = sum(sp.diff(V, s) * fi for s, fi in zip(sym_list, f))
        dec_cons = box + [_sign_term(decr, zvars) > z]
        dec, ce_dec = _search_ce(dec_cons, zvars, timeout_ms)
        detail["conditions"]["decrease"] = dec
        if dec == "refuted":
            return VerifyResult(self.name, "refuted", True, detail=detail, counterexample=ce_dec)

        if pos == "proved" and dec == "proved":
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "z3", "cert": str(system.get("cert_gt")),
                                             "conditions": detail["conditions"]})
        return VerifyResult(self.name, "unknown", True, detail=detail)


register(Z3Backend())
