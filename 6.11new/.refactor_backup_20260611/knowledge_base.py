#!/usr/bin/env python3
"""
knowledge_base.py — inequality / solved-case knowledge base (prototype).

Stores solved barrier-synthesis cases with lightweight features and retrieves
the top-k most similar ones to inject as few-shot hints into the Proposer.
The KB is a plain JSON file so it can be inspected and hand-edited.

Entry schema:
{
  "id": "darboux",
  "dim": 2,
  "system_class": "polynomial, quadratic",   # free text, matched by keyword
  "ode": "...",                              # display string
  "h": "...",                                # successful barrier expression
  "lie_derivative": "...",
  "key_steps": "...",                        # inequality tricks that closed the proof
  "source": "pipeline-v4"
}
"""
import json
import os
import re

KB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "barrier_kb.json")

_STOPWORDS = {"the", "and", "with", "system", "of", "in", "on", "a", "an"}


def _tokens(text: str) -> set:
    return {w for w in re.findall(r"[a-zA-Z_]+", (text or "").lower()) if w not in _STOPWORDS}


class KnowledgeBase:
    def __init__(self, path: str = KB_PATH):
        self.path = path
        self.entries = []
        if os.path.exists(path):
            try:
                with open(path, encoding="utf-8") as f:
                    self.entries = json.load(f)
            except (OSError, json.JSONDecodeError):
                self.entries = []

    def save(self):
        with open(self.path, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, ensure_ascii=False, indent=2)

    def add_case(self, case: dict):
        """Insert or replace by id, then persist."""
        cid = case.get("id")
        self.entries = [e for e in self.entries if e.get("id") != cid]
        self.entries.append(case)
        self.save()

    def retrieve(self, system: dict, k: int = 2) -> list:
        """Score entries by feature overlap with the query system."""
        q_dim = len(system.get("state_vars", []))
        q_tok = _tokens(system.get("name", "")) | _tokens(system.get("ode", "")) | _tokens(
            system.get("system_class", ""))
        scored = []
        for e in self.entries:
            score = 0
            if e.get("dim") == q_dim:
                score += 3
            overlap = _tokens(e.get("system_class", "")) | _tokens(e.get("ode", ""))
            score += len(q_tok & overlap)
            if score > 0:
                scored.append((score, e))
        scored.sort(key=lambda t: -t[0])
        return [e for _, e in scored[:k]]

    def few_shot_block(self, system: dict, k: int = 2) -> str:
        """Format retrieved cases as a prompt block; empty string if no match."""
        cases = self.retrieve(system, k)
        if not cases:
            return ""
        lines = ["[Reference: previously solved similar systems — use the *form* of h and the inequality tricks as inspiration, do not copy blindly]"]
        for i, e in enumerate(cases, 1):
            lines.append(f"Example {i}: system {e.get('ode')}")
            lines.append(f"  successful h(x) = {e.get('h')}")
            if e.get("key_steps"):
                lines.append(f"  key inequality steps: {e.get('key_steps')}")
        return "\n".join(lines)
