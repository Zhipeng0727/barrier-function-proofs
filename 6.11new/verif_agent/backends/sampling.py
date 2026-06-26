"""
sampling.py — the cheap, UNSOUND falsification gate. Wraps the existing
barrier_core sampling verifiers (verify_symbolic / verify_symbolic_discrete /
verify_lyapunov). Its job: reject wrong certificates fast before any expensive
sound backend runs, and provide concrete counterexample points.

A "passed" verdict is sound=False (sampling can miss violations). A "refuted"
verdict carries a concrete point; it is marked sound=False too unless a sound
backend re-confirms it — see agent.py's optional counterexample confirmation.
"""
from __future__ import annotations

import os
import sys

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from barrier_core import (verify_symbolic, verify_symbolic_discrete,  # noqa: E402
                          verify_lyapunov)
from verif_agent.backend_base import Backend, VerifyResult, register  # noqa: E402


class SamplingBackend(Backend):
    name = "sampling"
    sound = False

    def _verify(self, system: dict, cert: str, **opts) -> VerifyResult:
        task = system.get("task_type", "barrier")
        if task == "lyapunov":
            res = verify_lyapunov(system, cert)
            ce_key = "decrease_violations"
        elif system.get("discrete"):
            res = verify_symbolic_discrete(system, cert)
            ce_key = "cond2_violations"
        else:
            res = verify_symbolic(system, cert)
            ce_key = "cond2_violations"

        if res.get("error"):
            return VerifyResult(self.name, "error", False, detail=res)

        valid = res.get("symbolic_valid")
        ce = (res.get(ce_key) or res.get("cond1_violations")
              or res.get("positivity_violations"))
        if valid is True:
            status = "proved"          # but sound=False — "no counterexample sampled"
        elif valid is False:
            status = "refuted"
        else:
            status = "unknown"
        return VerifyResult(
            self.name, status, sound=False, detail=res,
            counterexample=(ce[0] if ce else None))


register(SamplingBackend())
