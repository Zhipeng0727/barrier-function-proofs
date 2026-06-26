"""
agent.py — the verification-method-selection agent. Given a (system, certificate),
it extracts features, asks the selector for a backend ladder, and runs the ladder
cheapest-first, STOPPING at the first conclusive verdict (a sound proof or any
refutation). It never funnels to one backend and never trusts an unsound verdict
as final: a "proved" is only returned as sound when it came from a sound backend.

Returns an AgentResult with the full per-backend trace, so the benchmark can
compare routed-vs-oracle-vs-single-backend and measure the time saved by stopping
early (selection == acceleration).
"""
from __future__ import annotations

import time
from dataclasses import dataclass, field

from verif_agent import backends  # noqa: F401  (import side-effect: registers backends)
from verif_agent.backend_base import get_backend
from verif_agent.selector import route_system


@dataclass
class AgentResult:
    status: str                 # proved | refuted | unknown
    sound: bool                 # is the final verdict a sound guarantee?
    chosen_backend: str | None
    ladder: list
    rationale: str
    elapsed_s: float
    trace: list = field(default_factory=list)   # [VerifyResult.as_dict(), ...]
    features: dict = field(default_factory=dict)

    def as_dict(self):
        return {
            "status": self.status, "sound": self.sound,
            "chosen_backend": self.chosen_backend, "ladder": self.ladder,
            "rationale": self.rationale, "elapsed_s": round(self.elapsed_s, 3),
            "features": self.features, "trace": self.trace,
        }


def verify(system: dict, cert: str | None = None, *, with_lean: bool = False,
           timeout_ms: int = 6000, verbose: bool = False) -> AgentResult:
    cert = cert if cert is not None else system.get("cert_gt")
    routing = route_system(system, cert)
    ladder = list(routing["ladder"])
    if not with_lean:
        ladder = [b for b in ladder if b != "lean"]

    t0 = time.time()
    trace, chosen, final_status, final_sound = [], None, "unknown", False

    for name in ladder:
        backend = get_backend(name)
        # pass timeout to solvers that accept it
        kwargs = {}
        if name in ("z3",):
            kwargs["timeout_ms"] = timeout_ms
        r = backend.verify(system, cert, **kwargs)
        trace.append(r.as_dict())
        if verbose:
            print(f"    [{name}] {r.status} (sound={r.sound}, {r.elapsed_s:.2f}s)")

        # sampling refutation = falsification gate fired → stop (unsound but the
        # certificate clearly fails; a concrete point was found)
        if name == "sampling" and r.status == "refuted":
            chosen, final_status, final_sound = name, "refuted", False
            break
        # a sound backend that proves or refutes is conclusive
        if r.sound and r.status in ("proved", "refuted"):
            chosen, final_status, final_sound = name, r.status, True
            break
        # remember an unsound "pass" only as a weak fallback
        if name == "sampling" and r.status == "proved" and chosen is None:
            chosen, final_status, final_sound = name, "proved", False
            # keep going — try to upgrade to a sound proof

    return AgentResult(
        status=final_status, sound=final_sound, chosen_backend=chosen,
        ladder=ladder, rationale=routing["rationale"],
        elapsed_s=time.time() - t0, trace=trace,
        features=routing["feature_vector"])
