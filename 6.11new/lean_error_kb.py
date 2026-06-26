"""
lean_error_kb.py — the Lean-error knowledge base as usable LLM knowledge.

Two roles:
  1. classify(diag)  — the failure classifier from the escalation design: match a
     real compiler diagnostic to a KB entry, returning its route (L1/L2/L3) and a
     concrete fix. This is what decides repair vs. rewrite vs. regenerate-barrier.
  2. error_kb_block() — a compact text block injected into the Lean writer / repair
     prompt so the model has the taxonomy up front.

Grounded in real diagnostics (see lean_error_harvest.py). Zero dependencies.
"""
import json
import os

_KB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean_error_kb.json")


def load_kb():
    with open(_KB_PATH, encoding="utf-8") as f:
        return json.load(f)


_ENTRIES = sorted(load_kb()["entries"], key=lambda e: e.get("priority", 99))


def classify(diag: str):
    """Return the best-matching KB entry for a compiler diagnostic, or None.

    Entries are tried in priority order (most specific first), so e.g. a
    transcendental `linarith failed` matches the transcendental entry before the
    generic nonlinear one. `requires_any` adds a context guard (the diag must also
    mention one of the listed tokens).
    """
    if not diag:
        return None
    for e in _ENTRIES:
        if not any(sig in diag for sig in e["signatures"]):
            continue
        req = e.get("requires_any")
        if req and not any(tok in diag for tok in req):
            continue
        return e
    return None


def route_for(diag: str) -> dict:
    """Classifier output for the orchestrator: {route, id, title, fix}.

    Falls back to L2 (rewrite strategy) for an unrecognized error — safer than
    L1 (re-repairing a failure we don't understand tends to loop)."""
    e = classify(diag)
    if not e:
        return {"route": "L2", "id": "unknown", "title": "unrecognized diagnostic",
                "fix": "Diagnostic not in KB. Rewrite the proof with a different, "
                       "simpler strategy; re-read the printed goal state carefully."}
    return {"route": e["route"], "id": e["id"], "title": e["title"], "fix": e["fix"],
            "lemmas": e.get("lemmas", [])}


def repair_hint(diag: str) -> str:
    """A targeted hint string to append to the repair prompt for this diagnostic."""
    r = route_for(diag)
    lem = (" Useful lemmas: " + ", ".join(r["lemmas"])) if r.get("lemmas") else ""
    return (f"[error class: {r['id']} | escalation: {r['route']}] {r['title']}.\n"
            f"How to fix: {r['fix']}{lem}")


def error_kb_block() -> str:
    """Compact taxonomy block for the Lean writer/repair system prompt."""
    kb = load_kb()
    out = ["Lean 4 compiler-error guide (match the diagnostic, apply the fix):"]
    for e in sorted(kb["entries"], key=lambda x: x.get("priority", 99)):
        out.append(f"- [{e['route']}] {e['title']}: {e['fix']}")
    return "\n".join(out)


# ── self-test / demo: classify the diagnostics we harvested (zero token) ──
if __name__ == "__main__":
    samples = {
        "log goal": "error: linarith failed to find a contradiction\nhx : 0 < x\na : x - 1 < Real.log x\n⊢ False",
        "poly goal": "error: linarith failed to find a contradiction\nx y : ℝ\na : x ^ 2 + y ^ 2 < 2 * x * y\n⊢ False",
        "bad name": "error(lean.unknownIdentifier): Unknown constant `Real.log_le_sub_one_of_poss`",
        "sorry": "warning: declaration uses 'sorry'",
        "instances": "error(lean.synthInstanceFailed): failed to synthesize instance of type class\n  HAdd ℝ ℝ ?m.4",
        "timeout": "error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (1) has been reached",
        "bad import": "error: object file '.../Mathlib/Does/Not/Exist.olean' of module Mathlib.Does.Not.Exist does not exist",
    }
    for name, diag in samples.items():
        r = route_for(diag)
        print(f"{name:12s} -> {r['route']:3s}  {r['id']}")
