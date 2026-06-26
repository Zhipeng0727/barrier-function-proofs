"""
verif_agent — a verification-method-SELECTION agent for barrier / Lyapunov
certificates. Given a (dynamical system, certificate), it routes to the cheapest
SOUND backend that can settle the problem, falling back across a ladder
(sampling falsifier → Z3 → dReal → Lean), and reports which backend produced the
guarantee. Selection is the acceleration mechanism: stop at the first conclusive,
sound verdict.

Public API:
    from verif_agent import verify, route_system
    res = verify(system_dict)            # -> AgentResult
    route_system(system_dict)            # -> {ladder, rationale, ...}
"""
from verif_agent.agent import verify, AgentResult  # noqa: F401
from verif_agent.selector import route_system, route  # noqa: F401
from verif_agent.features import extract_features  # noqa: F401
