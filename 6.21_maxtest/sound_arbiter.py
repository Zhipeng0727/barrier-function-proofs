"""
sound_arbiter.py — bridge the synthesis loop to the SOUND verification backends in
verif_agent (Z3 today; dReal/interval when installed).

The synthesis loop calls `sound_verify()` as its ARBITER, not a side check:
  • a sound "proved"  → the candidate is genuinely verified (verify_level L2_smt),
                        the loop may stop and record it as solved;
  • a sound "refuted" → a real counterexample, fed straight back to the Proposer
                        (counterexample-guided synthesis / CEGIS);
  • "unsupported"/"unknown" (e.g. transcendental, outside Z3's decidable fragment,
                        or a timeout) → level is None, so the caller falls back to
                        the NON-authoritative LLM filter and the Lean L3/L4 path.

Importing this module registers the Z3 backend only (no torch / nn backends). The
backend's own verify() is crash-isolated, so sound_verify never raises.
"""
from verif_agent.backends import z3_backend  # noqa: F401  (registers "z3")
from verif_agent.backend_base import get_backend

# verify_level taxonomy used across the pipeline (sound ⟺ a real guarantee):
#   L0_sample  — local sampling only (NOT sound)
#   L1_llm     — local + LLM Refuter "valid" (NOT sound)
#   L2_smt     — Z3 / SMT proved over the domain (SOUND)
#   L3_lean    — Lean compiled + L4 soundness audit passed (SOUND)
#   refuted    — a sound backend produced a counterexample
SOUND_LEVELS = {"L2_smt", "L3_lean"}


def sound_verify(system: dict, cert: str, timeout_ms: int = 8000) -> dict:
    """Run the sound SMT arbiter (Z3) on (system, cert).

    Returns a plain dict:
      status         : 'proved' | 'refuted' | 'unknown' | 'unsupported'
                       | 'unavailable' | 'error'
      sound          : whether a 'proved' here is a real guarantee (z3 ⇒ True)
      level          : 'L2_smt' if soundly proved, else None
      counterexample : {var: value} when refuted, else None
      backend        : which backend produced the verdict
      detail         : backend diagnostics (per-condition status, cbf constant, …)
    """
    try:
        r = get_backend("z3").verify(system, cert, timeout_ms=timeout_ms)
    except Exception as e:  # defensive: backend.verify is already isolated, but never raise
        return {"status": "error", "sound": False, "level": None, "backend": "z3",
                "counterexample": None, "detail": {"exception": f"{type(e).__name__}: {e}"}}
    level = "L2_smt" if (r.status == "proved" and r.sound) else None
    return {"status": r.status, "sound": bool(r.sound), "level": level,
            "backend": r.backend, "counterexample": r.counterexample,
            "detail": r.detail}


def is_sound_level(level) -> bool:
    return level in SOUND_LEVELS


# ── self-test: a poly cert z3 can decide, zero tokens ──
if __name__ == "__main__":
    # x1' = -x1, h = 1 - x1^2 ; C = {h>=0} = [-1,1] is invariant (ḣ = 2 x1^2 >= 0… on h=0)
    sysd = {
        "state_vars": ["x1"], "f_expr": ["-x1"], "task_type": "barrier",
        "discrete": False, "X_bounds": [(-3, 3)], "X_u_expr": "x1 >= 2",
        "cert_gt": "1 - x1^2",
    }
    print("poly barrier:", sound_verify(sysd, "1 - x1^2"))
    # transcendental → unsupported (falls back to Lean/LLM)
    syst = {**sysd, "f_expr": ["-x1 + 0*x1"], "cert_gt": "1 - sin(x1)**2"}
    print("transcendental:", {k: sound_verify(syst, "1 - sin(x1)**2")[k]
                              for k in ("status", "level")})
