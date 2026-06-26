#!/usr/bin/env python3
"""
lean_error_harvest.py — compile deliberately-broken Lean snippets and capture the
REAL compiler diagnostics, so the error knowledge base is grounded in what Lean
actually prints (not LLM guesses). Zero API tokens — only local `lake env lean`.

Output: prints, for each category, the first ~6 diagnostic lines. Feed these into
lean_error_kb.json's `signature` fields. Re-run after a toolchain bump to refresh.
"""
import os
import subprocess

LEAN_PROJECT = os.path.expanduser("~/lean")

PRELUDE = "import Mathlib.Data.Real.Basic\nimport Mathlib.Analysis.SpecialFunctions.Log.Basic\nimport Mathlib.Tactic\n"

SNIPPETS = {
    "tactic_failed_nonlinear":
        PRELUDE + "example (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by linarith\n",
    "tactic_failed_transcendental":
        PRELUDE + "example (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by nlinarith\n",
    "unknown_identifier":
        PRELUDE + "example (x : ℝ) : x = x := Real.log_le_sub_one_of_poss\n",
    "unknown_tactic":
        PRELUDE + "example : True := by trivvial\n",
    "unsolved_goals":
        PRELUDE + "example (x : ℝ) : x = 0 := by skip\n",
    "type_mismatch":
        PRELUDE + "def f : ℝ := \"hello\"\n",
    "import_not_found":
        "import Mathlib.Does.Not.Exist\nexample : True := trivial\n",
    "missing_real_instances":
        "import Mathlib.Tactic.Linarith\nexample (x y : ℝ) : x + y = y + x := by ring\n",
    "declaration_uses_sorry":
        PRELUDE + "example (x : ℝ) : x = x + 1 := by sorry\n",
    "heartbeat_timeout":
        PRELUDE + "set_option maxHeartbeats 1 in\nexample (x y : ℝ) : x^2 + y^2 ≥ 2*x*y := by nlinarith [sq_nonneg (x - y)]\n",
}


def compile_snippet(name, code):
    path = os.path.join(LEAN_PROJECT, f"_err_{name}.lean")
    with open(path, "w", encoding="utf-8") as f:
        f.write(code)
    try:
        proc = subprocess.run(["lake", "env", "lean", path], cwd=LEAN_PROJECT,
                              capture_output=True, text=True, timeout=300)
        diag = (proc.stdout + proc.stderr).strip()
        return proc.returncode, diag
    finally:
        try:
            os.remove(path)
        except OSError:
            pass


def main():
    for name, code in SNIPPETS.items():
        rc, diag = compile_snippet(name, code)
        # strip the temp-file path prefix for readability
        lines = [ln.split(".lean:", 1)[-1] if ".lean:" in ln else ln
                 for ln in diag.splitlines()][:6]
        print(f"\n### {name}  (exit {rc})")
        for ln in lines:
            print("   " + ln)


if __name__ == "__main__":
    main()
