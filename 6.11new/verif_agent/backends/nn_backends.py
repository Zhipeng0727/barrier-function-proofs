"""
nn_backends.py — registered-but-dormant adapters for the case the agent is
extended from SYMBOLIC certificates to NEURAL ones (B and/or the dynamics f given
as a network). The core200 benchmark has symbolic certificates, so these report
`unsupported` there; they exist so the routing pool and the paper's framing
("neural-network formal verification agent") are complete, and so wiring the real
solvers later is a drop-in.

- CROWNBackend  : sound incomplete bound propagation (auto_LiRPA / α,β-CROWN) —
                  fast Jacobian/Lie-derivative bounds for NN certificates, the
                  natural fast sound filter for high-dim / large nets.
- MILPBackend   : exact (complete) encoding for ReLU networks + PWL dynamics
                  (Gurobi). Blows up with ReLU count; exact where it fits.

Each guards on (a) the certificate actually being an NN, and (b) the solver being
importable, so they degrade gracefully exactly like dReal.
"""
from __future__ import annotations

import os
import sys

_PARENT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from verif_agent.backend_base import Backend, register  # noqa: E402


def _cert_is_nn(system, cert):
    """A NN certificate is signalled by system['cert_nn'] (a torch module / onnx
    path) rather than a sympy string. core200 entries never have this."""
    return bool(system.get("cert_nn")) or bool(system.get("dynamics_nn"))


class CROWNBackend(Backend):
    name = "crown"
    sound = True

    def applicable(self, system, cert):
        if not _cert_is_nn(system, cert):
            return False, "symbolic certificate — CROWN applies to NN certificates only"
        try:
            import auto_LiRPA  # noqa: F401
        except Exception:
            return False, "unavailable: auto_LiRPA not installed"
        return True, ""

    def _verify(self, system, cert, **opts):  # pragma: no cover - dormant on core200
        raise NotImplementedError("CROWN NN path not wired (no NN certificates in core200)")


class MILPBackend(Backend):
    name = "milp"
    sound = True

    def applicable(self, system, cert):
        if not _cert_is_nn(system, cert):
            return False, "symbolic certificate — MILP path targets ReLU NN certificates"
        try:
            import gurobipy  # noqa: F401
        except Exception:
            return False, "unavailable: gurobipy not installed / no license"
        return True, ""

    def _verify(self, system, cert, **opts):  # pragma: no cover - dormant on core200
        raise NotImplementedError("MILP NN path not wired (no NN certificates in core200)")


register(CROWNBackend())
register(MILPBackend())
