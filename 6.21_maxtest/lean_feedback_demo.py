#!/usr/bin/env python3
"""
lean_feedback_demo.py — minimal, self-contained demonstration of the
LLM ⇄ Lean4 feedback loop, with ZERO API token cost.

The real loop lives in lean_proof.py (generate_lean_proof): it asks the LLM for
Lean code, compiles it, and on failure feeds the compiler diagnostics back to
the LLM for a repair round. Here we replace the LLM with two PRE-BAKED replies
so the whole loop runs against a real `lake env lean` compile without spending
any tokens — one failing attempt, then a fixed one.

Run:  python3 lean_feedback_demo.py
"""

import os
import re
import subprocess
import textwrap

# The fully-built Lean project on this machine (mathlib + tactics compiled).
# (The paper4/ project's own .lake deps — aesop etc. — are not built, so we
#  point at ~/lean which has a complete toolchain+mathlib build.)
LEAN_PROJECT = os.path.expanduser("~/lean")

# ── The "LLM" — replaced by a fixed transcript so this costs 0 tokens. ──────
# In production these strings come from call_api(...) in lean_proof.py.
SIMULATED_LLM_REPLIES = [
    # Attempt 1: a plausible but WRONG proof. `linarith` is a linear tactic and
    # cannot discharge a nonlinear (quadratic) goal — it will fail to compile.
    textwrap.dedent("""\
        ```lean
        import Mathlib.Data.Real.Basic
        import Mathlib.Tactic

        -- Barrier verification condition reduced to a polynomial inequality:
        --   B(x,y) = x^2 + y^2  is a valid certificate  ⇐  x^2 + y^2 ≥ 2*x*y
        example (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by
          linarith
        ```"""),
    # Attempt 2: the repair the LLM produces AFTER reading the Lean feedback.
    # `nlinarith` with the square-nonneg hint is the standard fix.
    textwrap.dedent("""\
        ```lean
        import Mathlib.Data.Real.Basic
        import Mathlib.Tactic

        -- Repaired after Lean feedback: the goal is nonlinear, so switch to
        -- nlinarith and supply the dominating square (x - y)^2 ≥ 0.
        example (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by
          nlinarith [sq_nonneg (x - y)]
        ```"""),
]


def extract_lean_code(text: str) -> str:
    """Pull the Lean code out of a fenced ```lean ... ``` block (as the LLM emits)."""
    blocks = re.findall(r"```(?:lean4?)?\s*\n(.*?)```", text, re.S)
    return "\n\n".join(b.strip() for b in blocks) if blocks else text.strip()


def lean_compile_check(code: str, tag: str, timeout: int = 300) -> tuple:
    """Compile `code` with `lake env lean` inside LEAN_PROJECT.

    Returns (ok, diagnostics):
      ok  = True   compiled cleanly (exit 0, no `sorry`/errors)
      ok  = False  compiler reported errors (diagnostics carries them)
      ok  = None   toolchain missing (lake not on PATH)
    """
    path = os.path.join(LEAN_PROJECT, f"_check_{tag}.lean")
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(code)
        proc = subprocess.run(
            ["lake", "env", "lean", path], cwd=LEAN_PROJECT,
            capture_output=True, text=True, timeout=timeout,
        )
        diag = (proc.stdout + "\n" + proc.stderr).strip()
        return proc.returncode == 0, diag
    except subprocess.TimeoutExpired:
        return False, f"lean compilation timed out after {timeout}s"
    except FileNotFoundError:
        return None, "lake not found on PATH — skipping compile check"
    finally:
        try:
            os.remove(path)
        except OSError:
            pass


def build_repair_feedback(diag: str) -> str:
    """Turn raw Lean compiler output into the message handed back to the LLM.

    This is the heart of the 'feedback to the model' design: the compiler is the
    ground-truth oracle, and its diagnostics (error kind + open goal state) are
    injected verbatim into the next prompt so the model repairs against facts,
    not guesses.
    """
    return (
        "The Lean 4 code FAILED to compile. Below are the exact compiler "
        "diagnostics (error class, hypotheses, and the open goal `⊢ ...`).\n"
        "Read the goal state carefully, then output the FULL corrected Lean 4 "
        "code block.\n\n"
        "----- lean diagnostics -----\n"
        f"{diag}\n"
        "----------------------------"
    )


def run_loop(max_rounds: int = 3) -> bool:
    print("=" * 64)
    print("  LLM ⇄ Lean4 feedback loop  (compilation is REAL, LLM is mocked)")
    print(f"  project: {LEAN_PROJECT}")
    print("=" * 64)

    history_feedback = None
    for rnd in range(max_rounds):
        # 1. "Ask the LLM." Real loop: call_api(system, history). Here: transcript.
        if rnd >= len(SIMULATED_LLM_REPLIES):
            print("\n[!] Ran out of simulated replies without success.")
            return False
        reply = SIMULATED_LLM_REPLIES[rnd]
        code = extract_lean_code(reply)

        print(f"\n┌─ round {rnd + 1}: LLM proposes ─────────────────────────────")
        for line in code.splitlines():
            print(f"│ {line}")
        print("└" + "─" * 50)

        # 2. Compile and get ground-truth feedback from Lean.
        ok, diag = lean_compile_check(code, tag=f"demo{rnd}")

        if ok:
            print("\n  ✅ Lean accepted the proof — compile exit 0, no errors.")
            print("  The certificate is now machine-checked. Loop done.")
            return True
        if ok is None:
            print(f"\n  ⚠️  {diag}")
            return False

        # 3. Failure → format diagnostics as the next prompt for the LLM.
        print("\n  ❌ Lean rejected it. Feedback that goes back to the model:")
        history_feedback = build_repair_feedback(diag)
        for line in history_feedback.splitlines():
            print(f"     {line}")
        # In the real loop this string is appended to `history` and the model is
        # called again; here the next SIMULATED_LLM_REPLIES entry is its "answer".

    print("\n[!] Exhausted repair rounds without a clean compile.")
    return False


if __name__ == "__main__":
    success = run_loop()
    raise SystemExit(0 if success else 1)
