"""
selector.py — the routing brain. Maps a problem's feature vector to an ORDERED
ladder of backends. This is where "selection == acceleration" lives: the cheapest
applicable backend runs first and the agent stops at the first conclusive verdict,
so a sound proof is obtained without paying for the whole pool.

v0 is a transparent rule table (below); it exposes the same route() signature a
learned policy (trained on core200 outcomes) will later implement, so upgrading
the policy never touches the agent or backends.

Rule table
----------
  always:                 sampling           (cheap unsound falsifier gate)
  NN certificate:         crown → milp → dreal
  polynomial (decidable): z3 → dreal → lean
  transcendental:         dreal → lean       (z3 cannot do these soundly)
  rational / piecewise:   dreal → lean       (z3 gated off; dReal handles them)
  parametric (∀n):        … → lean first among sound  (family-level guarantee)
"""
from __future__ import annotations

from verif_agent.features import extract_features, feature_summary


def route(feats: dict) -> dict:
    """Return {'ladder': [backend names], 'rationale': str}."""
    ladder = ["sampling"]
    why = ["sampling: cheap falsifier gate (always first)"]

    if feats.get("has_cert") and feats.get("dim", 0) and feats.get("nn_cert"):
        ladder += ["crown", "milp", "dreal"]
        why.append("NN certificate → CROWN (fast bound) → MILP (exact ReLU) → dReal")
    elif feats["decidable_real"]:
        sound = ["z3", "interval", "dreal", "lean"]
        why.append("polynomial/decidable → Z3 (complete NRA) → interval → dReal → Lean")
    elif feats["transcendental"]:
        # interval BnB is the in-house sound transcendental solver; dReal if present
        sound = (["interval", "dreal", "lean"] if feats.get("dim", 99) <= 4
                 else ["dreal", "lean"])
        why.append("transcendental → interval BnB (sound, ≤4D) → dReal → Lean; Z3 unsound here")
    else:  # rational / piecewise / unknown
        sound = (["interval", "dreal", "lean"] if feats.get("dim", 99) <= 4
                 else ["dreal", "lean"])
        why.append("rational/piecewise → interval BnB → dReal → Lean")

    if not feats.get("nn_cert"):
        # parametric families want the family-level (Lean) guarantee earlier
        if feats.get("parametric") and "lean" in sound:
            sound = ["lean"] + [b for b in sound if b != "lean"]
            why.append("parametric (∀n) → Lean promoted (family-level guarantee)")
        ladder += sound

    return {"ladder": ladder, "rationale": "; ".join(why),
            "features": feature_summary(feats)}


def route_system(system: dict, cert: str | None = None) -> dict:
    feats = extract_features(system, cert)
    feats["nn_cert"] = bool(system.get("cert_nn") or system.get("dynamics_nn"))
    r = route(feats)
    r["feature_vector"] = feats
    return r
