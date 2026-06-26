"""
lean_backend.py — SOUND, machine-checked certification via Lean 4 + Mathlib
(wraps lean_proof.generate_lean_proof). A "proved" verdict means a sorry-free Lean
file compiled against Mathlib (strict mode), the strongest guarantee in the pool.

Niche (per the agent's design): symbolic / parametric (∀n family) / meta-level
guarantees — NOT the right tool to grind a single big numeric instance. It is also
the most expensive backend (LLM-written proof + repair rounds + lake compile), so
the selector places it LAST in the ladder and the bulk benchmark leaves it
disabled unless --with-lean is passed.
"""
from __future__ import annotations

import os
import sys

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.backend_base import Backend, VerifyResult, register  # noqa: E402


class LeanBackend(Backend):
    name = "lean"
    sound = True

    def applicable(self, system, cert):
        cert = cert if cert is not None else system.get("cert_gt")
        if not cert:
            return False, "no certificate to check"
        try:
            import shutil
            if shutil.which("lake") is None:
                return False, "unavailable: lake (Lean) not on PATH"
        except Exception:
            return False, "unavailable: lake check failed"
        return True, ""

    def _verify(self, system, cert, repair_rounds=1, tag=None, **opts):
        cert = cert if cert is not None else system.get("cert_gt")
        tag = tag or ("va_" + str(abs(hash((system.get("name", ""), cert))) % 10**8))

        # Preferred path: the REINFORCED formalization pipeline (lean_escalation) —
        # three-level L1/L2/L3 escalation that INJECTS the self-evolve mined recipe
        # store (compile-verified bridging lemmas) + family SOS hints. This is what
        # lets Lean close cases neither z3 (transcendental) nor interval BnB (loose
        # product enclosure) can — e.g. the tanh decrease -y·tanh(y)≤0, whose
        # `tanh_sign` recipe is in the store. Falls back to the plain writer if the
        # escalation module or a required field is missing.
        try:
            from lean_escalation import formalize_certificate
            sysd = dict(system)
            sysd.setdefault("ode", ", ".join(
                f"d{v}/dt = {fe}" for v, fe in
                zip(system.get("state_vars", []), system.get("f_expr", []))))
            sysd.setdefault("X_domain", str(system.get("X_bounds", "")))
            sysd.setdefault("task", system.get("task_type", "lyapunov"))
            # verifying a GIVEN cert → barriers=1 (never regenerate the certificate);
            # give inner repair room (this is the last, most-capable backend).
            budget = opts.get("lean_budget",
                              {"inner": 5, "barriers": 1, "max_calls": 6, "repeat_l3": 3})
            res = formalize_certificate(sysd, cert, budget=budget,
                                        strict_sorry=True, on_event=None)
            detail = {"solved": res.get("solved"), "final_level": res.get("final_level"),
                      "calls": res.get("calls"), "pipeline": "reinforced+recipes"}
            if res.get("solved"):
                return VerifyResult(self.name, "proved", True, detail=detail,
                                    certificate={"backend": "lean", "code": res.get("code")})
            return VerifyResult(self.name, "unknown", True, detail=detail)
        except Exception as e:
            fallback_note = f"reinforced path unavailable ({type(e).__name__}); plain writer"

        from lean_proof import generate_lean_proof
        final = {"h": cert, "lie_derivative": "see certificate", "invariant_set": "C"}
        rec = generate_lean_proof(system, final, tag, repair_rounds=repair_rounds)
        ok = rec.get("compile_ok")
        detail = {"compile_ok": ok, "note": fallback_note,
                  "attempts": [{k: a.get(k) for k in ("attempt", "compile_ok", "elapsed_s")}
                               for a in rec.get("attempts", [])]}
        if ok is True:
            return VerifyResult(self.name, "proved", True, detail=detail,
                                certificate={"backend": "lean", "code": rec.get("code")})
        if ok is None:
            return VerifyResult(self.name, "unavailable", True, detail=detail)
        return VerifyResult(self.name, "unknown", True, detail=detail)


register(LeanBackend())
