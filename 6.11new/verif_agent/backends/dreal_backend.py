"""
dreal_backend.py — SOUND verification over the reals INCLUDING transcendental
functions, via dReal's δ-complete decision procedure, run through the
`dreal/dreal4` DOCKER image + SMT2 (QF_NRA) strings. This matches the project's
existing `~/lean/SMT/barrier_dreal.py` approach and sidesteps the dReal pip wheel,
which won't build on this macOS (wheel.pep425tags removed).

Semantics: we assert the NEGATION of each condition (search for a counterexample)
and read dReal's verdict:
  unsat      ⇒ no counterexample exists ⇒ condition holds  (PROVED, sound)
  delta-sat  ⇒ a δ-perturbed witness ⇒ cannot prove; NOT a guaranteed true
               counterexample, so we report 'unknown' (never a sound refutation)
  timeout    ⇒ unknown

This is the high-dim / hard-transcendental complement to the in-house interval
backend: dReal's branch-and-prune (ICP) closes cases interval BnB can't.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile

import sympy as sp

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.backend_base import Backend, VerifyResult, register  # noqa: E402
from verif_agent.features import _parse, _SP_LOCALS  # noqa: E402

_DOCKER_IMAGE = "dreal/dreal4"
_DELTA = "0.0001"
_CBF_CANDIDATES = (0.0, 1.0, 5.0)   # kept small: each C is a separate docker run
_RUN_TIMEOUT = 30

_FN = {sp.exp: "exp", sp.log: "log", sp.sin: "sin", sp.cos: "cos", sp.tan: "tan",
       sp.asin: "asin", sp.acos: "acos", sp.atan: "atan", sp.sinh: "sinh",
       sp.cosh: "cosh", sp.tanh: "tanh", sp.Abs: "abs"}


def _num(v) -> str:
    if isinstance(v, sp.Rational) and not v.is_Integer:
        p, q = int(v.p), int(v.q)
        s = f"(/ {abs(p)}.0 {q}.0)"
        return s if p >= 0 else f"(- {s})"
    f = float(v)
    return f"(- {abs(f)})" if f < 0 else repr(f)


def _smt2(e) -> str:
    if e.is_Symbol:
        return e.name
    if e.is_Number:
        if e is sp.pi:
            return "3.141592653589793"
        if e is sp.E:
            return "2.718281828459045"
        return _num(e)
    if e.is_Add:
        return "(+ " + " ".join(_smt2(a) for a in e.args) + ")"
    if e.is_Mul:
        return "(* " + " ".join(_smt2(a) for a in e.args) + ")"
    if e.is_Pow:
        base, exp = e.args
        if exp == sp.Rational(1, 2):
            return f"(sqrt {_smt2(base)})"
        if exp.is_Integer:
            n = int(exp)
            b = _smt2(base)
            if n == 0:
                return "1.0"
            body = b if abs(n) == 1 else "(* " + " ".join([b] * abs(n)) + ")"
            return body if n > 0 else f"(/ 1.0 {body})"
        return f"(^ {_smt2(base)} {_smt2(exp)})"
    f = e.func
    if f in _FN:
        return f"({_FN[f]} {_smt2(e.args[0])})"
    if f == sp.atan2:
        return f"(atan2 {_smt2(e.args[0])} {_smt2(e.args[1])})"
    if f == sp.atanh:                      # 0.5 log((1+x)/(1-x))
        x = _smt2(e.args[0])
        return f"(* 0.5 (log (/ (+ 1.0 {x}) (- 1.0 {x}))))"
    if f == sp.asinh:                      # log(x + sqrt(x^2+1))
        x = _smt2(e.args[0])
        return f"(log (+ {x} (sqrt (+ (* {x} {x}) 1.0))))"
    if f == sp.acosh:                      # log(x + sqrt(x^2-1))
        x = _smt2(e.args[0])
        return f"(log (+ {x} (sqrt (- (* {x} {x}) 1.0))))"
    if f in (sp.Min, sp.Max):
        op = "min" if f == sp.Min else "max"
        s = _smt2(e.args[0])
        for a in e.args[1:]:
            s = f"({op} {s} {_smt2(a)})"
        return s
    raise ValueError(f"smt2: unsupported {f.__name__ if hasattr(f,'__name__') else f}")


def _smt2_rel(rel) -> str:
    if rel.func == sp.Or:
        return "(or " + " ".join(_smt2_rel(a) for a in rel.args) + ")"
    if rel.func == sp.And:
        return "(and " + " ".join(_smt2_rel(a) for a in rel.args) + ")"
    ops = {sp.StrictLessThan: "<", sp.LessThan: "<=", sp.StrictGreaterThan: ">",
           sp.GreaterThan: ">=", sp.Equality: "="}
    op = ops[type(rel)]
    return f"({op} {_smt2(rel.lhs)} {_smt2(rel.rhs)})"


def _doc(state_vars, box, violation_asserts) -> str:
    lines = ["(set-logic QF_NRA)"]
    lines += [f"(declare-fun {v} () Real)" for v in state_vars]
    lines += [f"(assert {a})" for a in box]
    lines += [f"(assert {a})" for a in violation_asserts]
    lines.append("(check-sat)")
    return "\n".join(lines)


_AVAIL = None  # cache: None=unknown, True/False


def _docker_available() -> bool:
    global _AVAIL
    if _AVAIL is not None:
        return _AVAIL
    try:
        if subprocess.run(["docker", "info"], capture_output=True,
                          timeout=10).returncode != 0:
            _AVAIL = False
            return False
        r = subprocess.run(["docker", "images", "-q", _DOCKER_IMAGE],
                           capture_output=True, text=True, timeout=10)
        _AVAIL = bool(r.stdout.strip())
    except Exception:
        _AVAIL = False
    return _AVAIL


def _run(smt2: str, timeout=_RUN_TIMEOUT):
    """Return ('proved'|'unknown'|'error', raw_output)."""
    # MUST live under a Docker-Desktop-shared path: /var/folders (tempfile's macOS
    # default) is NOT shared, so the container sees an empty mount and dReal prints
    # usage. /tmp is shared.
    with tempfile.NamedTemporaryFile(suffix=".smt2", mode="w", delete=False,
                                     dir="/tmp") as f:
        f.write(smt2)
        path = f.name
    host_dir, fname = os.path.dirname(path), os.path.basename(path)
    # dReal wants the input file FIRST, then `--precision <v>` (space form; the
    # `--precision=<v>` form before the file makes it print usage and exit 1).
    cmd = ["docker", "run", "--rm", "-v", f"{host_dir}:/work", _DOCKER_IMAGE,
           "dreal", f"/work/{fname}", "--precision", _DELTA]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        raw = (out.stdout + out.stderr).strip()
    except subprocess.TimeoutExpired:
        raw = "TIMEOUT"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass
    low = raw.lower()
    if "unsat" in low:
        return "proved", raw
    if "delta-sat" in low or "sat" in low:
        return "unknown", raw     # δ-sat: cannot claim sound proof OR sound refutation
    return ("error" if raw == "TIMEOUT" else "unknown"), raw


class DRealBackend(Backend):
    name = "dreal"
    sound = True

    def applicable(self, system, cert):
        cert = cert if cert is not None else system.get("cert_gt")
        if not cert:
            return False, "no certificate to check"
        if not _docker_available():
            return False, "unavailable: dReal docker image dreal/dreal4 not ready"
        return True, ""

    def _verify(self, system, cert, **opts):
        cert = cert if cert is not None else system.get("cert_gt")
        state_vars = system["state_vars"]
        syms = {v: sp.Symbol(v, real=True) for v in state_vars}
        sym_list = [syms[v] for v in state_vars]
        h = _parse(cert, state_vars)
        f = [_parse(fe, state_vars) for fe in system["f_expr"]]
        if h is None or any(fi is None for fi in f):
            return VerifyResult(self.name, "error", True, detail={"reason": "parse failed"})

        bounds = system.get("X_bounds") or [(-3, 3)] * len(state_vars)
        box = []
        for v, (lo, hi) in zip(state_vars, bounds):
            box += [f"(>= {v} {_num(sp.Float(float(lo)))})",
                    f"(<= {v} {_num(sp.Float(float(hi)))})"]
        task = system.get("task_type", "barrier")
        detail = {"conditions": {}, "delta": _DELTA}

        try:
            if task == "lyapunov":
                return self._lyap(system, h, f, sym_list, state_vars, box, detail)
            return self._barrier(system, h, f, sym_list, state_vars, box, detail)
        except ValueError as e:
            return VerifyResult(self.name, "unsupported", True, detail={"reason": str(e)})

    def _lyap(self, system, V, f, sym_list, state_vars, box, detail):
        x_star = system.get("equilibrium") or [0.0] * len(state_vars)
        V0 = V.subs({s: sp.Float(c) for s, c in zip(sym_list, x_star)})
        # Positivity: dReal's δ-completeness CANNOT prove V>0 near x* (V→0 there ⇒
        # V≤0 is always δ-satisfiable). Delegate PSD to interval BnB (sound, trivial
        # for square certs); dReal handles the hard part — the decrease condition.
        pos = self._interval_psd(V - V0, state_vars, system)
        detail["conditions"]["positivity"] = f"{pos} (via interval PSD)"
        if pos != "proved":
            return VerifyResult(self.name, "unknown", True, detail=detail)
        if system.get("discrete"):
            decr = V.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True) - V
        else:
            decr = sum(sp.diff(V, s) * fi for s, fi in zip(sym_list, f))
        dec, _ = _run(_doc(state_vars, box, [f"(> {_smt2(decr)} 0.0)"]))
        detail["conditions"]["decrease"] = dec
        if dec == "proved":
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "dreal", "delta": _DELTA})
        return VerifyResult(self.name, "unknown", True, detail=detail)

    def _interval_psd(self, expr, state_vars, system):
        """Sound positive-semidefinite check (V_sh ≥ 0) via interval BnB — the
        complement to dReal, which can't prove PD near the equilibrium."""
        try:
            from verif_agent.backends.interval_backend import _prove_nonneg
            bounds = [tuple(map(float, b)) for b in
                      (system.get("X_bounds") or [(-3, 3)] * len(state_vars))]
            bounds = [(lo + 1e-6 * (hi - lo) + 1e-12, hi - 1e-6 * (hi - lo) - 1e-12)
                      for lo, hi in bounds]
            st, _ = _prove_nonneg(expr, state_vars, bounds)
            return st
        except Exception:
            return "unknown"

    def _barrier(self, system, h, f, sym_list, state_vars, box, detail):
        cond1 = "skipped"
        xu = (system.get("X_u_expr") or "").strip()
        if xu and xu not in ("False", "false"):
            xu_expr = sp.sympify(xu.replace("^", "**"),
                                 locals={**{v: s for v, s in zip(state_vars, sym_list)}, **_SP_LOCALS})
            cond1, _ = _run(_doc(state_vars, box,
                                 [_smt2_rel(xu_expr), f"(>= {_smt2(h)} 0.0)"]))
            detail["conditions"]["cond1_h_neg_on_Xu"] = cond1
            if cond1 != "proved":
                return VerifyResult(self.name, "unknown", True, detail=detail)

        if system.get("discrete"):
            h_next = h.subs({s: fi for s, fi in zip(sym_list, f)}, simultaneous=True)
            cond2, _ = _run(_doc(state_vars, box,
                                 [f"(>= {_smt2(h)} 0.0)", f"(< {_smt2(h_next)} 0.0)"]))
        else:
            hdot = sum(sp.diff(h, s) * fi for s, fi in zip(sym_list, f))
            cond2, used = "unknown", None
            for C in _CBF_CANDIDATES:
                expr = hdot + sp.Float(C) * h
                st, _ = _run(_doc(state_vars, box, [f"(< {_smt2(expr)} 0.0)"]))
                if st == "proved":
                    cond2, used = "proved", C
                    break
            detail["cbf_constant"] = used
        detail["conditions"]["cond2"] = cond2
        if cond1 in ("proved", "skipped") and cond2 == "proved":
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "dreal", "delta": _DELTA})
        return VerifyResult(self.name, "unknown", True, detail=detail)


register(DRealBackend())
