"""
backend_base.py — uniform interface every verification backend implements, plus a
small registry. This is the contract the selector routes over.

A "problem" is a (system, cert) pair, where `system` is the SYSTEMS-style dict
produced by dataset_loader (state_vars, f_expr, X_bounds, X_u_expr, task_type,
discrete, equilibrium, psd_ok, cert_gt, meta) and `cert` is the certificate
expression string to check (defaults to system['cert_gt']).

SOUNDNESS CONTRACT
------------------
Each backend declares `sound` = whether a "proved" verdict is a real mathematical
guarantee (z3/dReal/Lean) or merely "no counterexample found by sampling" (the
falsifier). The agent NEVER funnels everything to one backend: it composes
individually-sound backends and reports which one produced the certificate. A
sampled counterexample is a sound *refutation* only if the point is re-checked
exactly — the sampling backend therefore marks its refutations sound=False unless
confirmed.
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field
from typing import Optional


# Verdict vocabulary (status field of VerifyResult):
#   "proved"       — conditions hold (sound iff backend.sound)
#   "refuted"      — a concrete counterexample violates a condition
#   "unknown"      — backend ran but could neither prove nor refute (timeout/incomplete)
#   "unsupported"  — backend cannot model this problem (e.g. z3 on transcendental)
#   "unavailable"  — backend not installed in this environment (e.g. dReal)
#   "error"        — backend crashed
TERMINAL_PROVE = "proved"
TERMINAL_REFUTE = "refuted"


@dataclass
class VerifyResult:
    backend: str
    status: str
    sound: bool                       # is a "proved" verdict from this backend sound?
    elapsed_s: float = 0.0
    detail: dict = field(default_factory=dict)
    certificate: Optional[dict] = None     # backend-specific proof artifact
    counterexample: Optional[dict] = None  # {var: value} when refuted

    @property
    def conclusive(self) -> bool:
        """A result the agent can stop on: a sound proof, or any refutation."""
        return self.status == TERMINAL_REFUTE or (
            self.status == TERMINAL_PROVE and self.sound)

    def as_dict(self) -> dict:
        return {
            "backend": self.backend,
            "status": self.status,
            "sound": self.sound,
            "elapsed_s": round(self.elapsed_s, 3),
            "detail": self.detail,
            "certificate": self.certificate,
            "counterexample": self.counterexample,
        }


class Backend:
    """Base class. Subclasses set `name`, `sound`, and implement _verify()."""
    name: str = "base"
    sound: bool = False

    def applicable(self, system: dict, cert: str) -> tuple[bool, str]:
        """(ok, reason). Override to gate by feature (activation, transcendental,
        availability of the external solver, ...). Default: always applicable."""
        return True, ""

    def _verify(self, system: dict, cert: str, **opts) -> VerifyResult:
        raise NotImplementedError

    def verify(self, system: dict, cert: str, **opts) -> VerifyResult:
        """Wraps _verify with timing + applicability + crash isolation, so the
        selector can treat every backend uniformly and never die on one bad case."""
        ok, reason = self.applicable(system, cert)
        if not ok:
            status = "unavailable" if reason.startswith("unavailable") else "unsupported"
            return VerifyResult(self.name, status, self.sound, 0.0,
                                detail={"reason": reason})
        t0 = time.time()
        try:
            r = self._verify(system, cert, **opts)
            r.elapsed_s = time.time() - t0
            return r
        except Exception as e:  # never let one backend crash the benchmark
            return VerifyResult(self.name, "error", self.sound, time.time() - t0,
                                detail={"exception": f"{type(e).__name__}: {e}"})


# ── registry ──────────────────────────────────────────────────────────────
_REGISTRY: dict[str, Backend] = {}


def register(backend: Backend) -> Backend:
    _REGISTRY[backend.name] = backend
    return backend


def get_backend(name: str) -> Backend:
    return _REGISTRY[name]


def all_backends() -> dict[str, Backend]:
    return dict(_REGISTRY)
