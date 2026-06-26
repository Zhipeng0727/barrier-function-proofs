"""
lean_proof.py — Lean 4 formalization concern, isolated from the synthesis loop.

Extracts fenced Lean code from an LLM reply, compiles it with `lake env lean` in
the paper4 project, and runs the generate-then-repair loop. Keeping this out of
the orchestrator lets run_barrier_synthesis_v4 stay focused on Proposer->verify->Refuter.
"""

import os
import re
import subprocess
import time as _time

from runtime_state import LEAN_PROJECT, call_api

# Set by call_log.init_run() — when non-None, every lean_compile_check is
# appended to the run's lean.jsonl with full code + diagnostic.
_LEAN_LOG_FN = None
from barrier_core import lean4_system, _task_framework
from lean_error_kb import error_kb_block, repair_hint

# ─────────────────────────────────────────────
# Certificate-family proof skeletons (v5).
# Free-form Lean generation hits Mathlib-lemma-name roulette; a family-matched
# skeleton with the right lemma names raises first-compile rates substantially.
# ─────────────────────────────────────────────
_TEMPLATES = {
    "log": """-- skeleton: log-family certificate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Polyrith
-- key lemmas: Real.log_le_sub_one_of_pos (log x <= x - 1 for x > 0),
--             Real.add_one_le_exp, Real.log_pos / Real.log_neg, Real.log_mul,
--             Real.sq_nonneg, abs_le
-- pattern: rewrite the verification condition so every log appears via
--          z := Real.log x, then close polynomial parts with nlinarith [sq_nonneg z]""",
    "trig": """-- skeleton: trigonometric / energy certificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Polyrith
-- key lemmas: Real.neg_one_le_cos, Real.cos_le_one, Real.neg_one_le_sin,
--             Real.sin_le_one, Real.sin_sq_add_cos_sq, Real.abs_sin_le_abs (|sin y| <= |y|... use Real.abs_sin_le_one + Real.sin_le when needed)
-- pattern: bound 1 - cos q in [0, 2], then nlinarith with sq_nonneg of the momenta""",
    "exp": """-- skeleton: exp / hyperbolic certificate
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sinh -- (or .Cosh / .Trigonometric.Hyperbolic as available)
import Mathlib.Tactic.Polyrith
-- key lemmas: Real.exp_pos, Real.add_one_le_exp (1 + y <= exp y),
--             Real.exp_log, Real.cosh_pos, Real.sinh_strictMono
-- pattern: substitute z := Real.exp x or z := Real.sinh x, prove the polynomial
--          inequality in z with nlinarith [Real.exp_pos x]""",
    "entropy": """-- skeleton: KL / entropy certificate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Polyrith
-- key lemmas: Real.log_le_sub_one_of_pos  (the Gibbs / log-sum core: log z <= z - 1),
--             Real.sum_le_sum, Finset.sum_nonneg
-- pattern: KL decrease always reduces to sum_i w_i * (log z_i) <= sum_i w_i * (z_i - 1)""",
    "piecewise": """-- skeleton: min/max/saturation certificate
import Mathlib.Data.Real.Basic  -- REQUIRED: ℝ algebra/order instances (HMul/Neg/...); without it
                                -- `def f (x : ℝ) := -5*x` fails type-class synthesis before any tactic runs
import Mathlib.Order.MinMax     -- min/max order lemmas
import Mathlib.Tactic           -- nlinarith / polyrith / rcases (do NOT use the bare `import Mathlib` umbrella — broken here)
-- key lemmas: min_le_left/right, le_max_left/right, max_le_iff, le_min_iff, abs_le
-- pattern: rcases on the active branch (le_total a b), then a polynomial goal per branch""",
    "poly": """-- skeleton: polynomial certificate
import Mathlib.Data.Real.Basic  -- REQUIRED: ℝ algebra/order instances (HMul/Neg/...); without it
                                -- `def f (x : ℝ) := -5*x` fails type-class synthesis before any tactic runs
import Mathlib.Tactic           -- nlinarith / polyrith / positivity (do NOT use the bare `import Mathlib` umbrella — broken here)
-- pattern: the verification condition is a polynomial inequality —
--          try nlinarith [sq_nonneg (x1 + x2), sq_nonneg (x1 - x2), sq_nonneg x1, sq_nonneg x2]
--          (add the squares whose expansion dominates the cross terms), or polyrith""",
}


def _cert_family(cert: str) -> str:
    c = (cert or "").lower()
    if re.search(r"\blog\(.*/.*\)|xhat|kl", c) or ("log(" in c and "*log(" in c):
        return "entropy"
    if "log" in c:
        return "log"
    if re.search(r"\bsin\b|\bcos\b|\bsin\(|\bcos\(", c):
        return "trig"
    if re.search(r"exp|sinh|cosh|tanh|atanh|asinh", c):
        return "exp"
    if re.search(r"\bmin\(|\bmax\(|\babs\(|\bsat\(", c):
        return "piecewise"
    return "poly"

def extract_lean_code(text: str) -> str:
    blocks = re.findall(r"```(?:lean4?)?\s*\n(.*?)```", text, re.S)
    return "\n\n".join(b.strip() for b in blocks) if blocks else text.strip()


def has_sorry(diag: str) -> bool:
    """True if the compiler emitted the `declaration uses 'sorry'` warning.
    Matched on the warning text (both quote styles) so a lemma name containing
    the substring 'sorry' never trips it."""
    d = diag or ""
    return ("uses 'sorry'" in d) or ("uses `sorry`" in d)


def lean_compile_check(code: str, tag: str, timeout: int = 300,
                       strict_sorry: bool = True, audit: bool = True,
                       state_vars=None) -> tuple:
    """Compile `code` inside the paper4 lake project. Returns (ok, diagnostics).

    strict_sorry (default True): a file with a `sorry` type-checks and EXITS 0 but
    is NOT proved. In strict mode such a result is `ok=False` (soundness: a barrier
    certificate is only 'formalized' when fully proved). Set False to accept
    sorry-bearing skeletons (the older lenient behavior).

    audit (default True): L4 soundness gate (lean_soundness.audit). A file can
    compile sorry-free yet prove nothing — by declaring `axiom Real`/bridge axioms,
    or stating a trivial theorem. When audit catches that, ok flips to False and the
    reason is appended to the diagnostics so the repair loop sees it. Set False to
    get the raw compile verdict (e.g. for skeleton mining)."""
    path = os.path.join(LEAN_PROJECT, f"_check_{tag}.lean")
    _lt0 = _time.time()
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(code)
        proc = subprocess.run(
            ["lake", "env", "lean", path], cwd=LEAN_PROJECT,
            capture_output=True, text=True, timeout=timeout,
        )
        diag = (proc.stdout + "\n" + proc.stderr).strip()
        ok = proc.returncode == 0
        if ok and strict_sorry and has_sorry(diag):
            ok = False
            diag = (diag + "\n[strict] compiled with exit 0 but contains `sorry` — "
                    "treated as NOT proved.").strip()
        if ok and audit:
            try:
                from lean_soundness import audit as _l4_audit
                verdict = _l4_audit(code, LEAN_PROJECT, tag, state_vars=state_vars,
                                    run_print_axioms=True, timeout=min(timeout, 240))
                if not verdict["sound"]:
                    ok = False
                    diag = (diag + "\n[L4 unsound] " + verdict["level"] + ": "
                            + " ".join(verdict["reasons"])
                            + " — a compiling, sorry-free file that assumes axioms or "
                              "states a trivial theorem is NOT a formal proof. Remove all "
                              "`axiom` declarations, use Mathlib's ℝ (do not re-declare it), "
                              "and state the actual barrier/Lyapunov inequality.").strip()
                elif verdict["warn"]:
                    diag = (diag + "\n[L4 note] " + " ".join(verdict["warn"][:3])).strip()
            except Exception as _e:
                diag = (diag + f"\n[L4 audit skipped: {_e}]").strip()
        _lean_elapsed = round(_time.time() - _lt0, 3)
        if _LEAN_LOG_FN:
            try:
                _LEAN_LOG_FN(tag=tag, code=code, ok=ok,
                             diagnostic=diag[:4000], elapsed_s=_lean_elapsed)
            except Exception:
                pass
        return ok, diag[:4000]
    except subprocess.TimeoutExpired:
        _lean_elapsed = round(_time.time() - _lt0, 3)
        if _LEAN_LOG_FN:
            try:
                _LEAN_LOG_FN(tag=tag, code=code, ok=False,
                             diagnostic=f"timed out after {timeout}s",
                             elapsed_s=_lean_elapsed)
            except Exception:
                pass
        return False, f"lean compilation timed out after {timeout}s"
    except FileNotFoundError:
        return None, "lake not found on PATH — skipping compile check"
    finally:
        try:
            os.remove(path)
        except OSError:
            pass


def generate_lean_proof(system: dict, final: dict, tag: str, repair_rounds: int = 2,
                        effort: str = "high") -> dict:
    fw = _task_framework(system)
    cert = final.get("h", "unknown")
    family = _cert_family(cert)
    discrete = bool(system.get("discrete"))
    decrease_line = (
        f"One-step quantity: {final.get('lie_derivative', 'unknown')}" if discrete else
        f"Lie derivative / decrease quantity: {final.get('lie_derivative', 'unknown')}")
    statement_hint = (
        "For this DISCRETE system the conditions are inequalities about the map f itself "
        "(no derivatives needed in Lean): formalize x+ = f(x) as a function and prove the "
        "one-step inequality directly." if discrete else
        "Formalize the vector field componentwise; for the decrease condition you may state "
        "it as an inequality about the explicit closed-form derivative expression (already "
        "computed above) rather than re-deriving it via HasDerivAt, if that keeps the proof compiling.")
    lean_prompt = (
        f"Please generate a Lean 4 formal proof for the following verified certificate:\n\n"
        f"Task: {fw['goal']}\n"
        f"System dynamics: {system['ode']}\n"
        f"State domain: {system['X_domain']}\n"
        + (f"Unsafe set: {system['X_u_desc']}\n" if system.get('X_u_desc') else "")
        + f"State variables: {', '.join(system['state_vars'])}\n"
        f"Certificate: {cert}\n"
        f"Certified set: {final.get('invariant_set', 'unknown')}\n"
        f"{decrease_line}\n\n"
        f"Conditions to state and prove:\n{fw['conditions']}\n\n"
        f"{statement_hint}\n\n"
        f"Recommended proof skeleton for this certificate family ({family}):\n"
        f"```lean\n{_TEMPLATES[family]}\n```\n\n"
        f"{error_kb_block()}\n\n"
        f"The code will be compiled with `lake env lean` against Mathlib4 — it must compile. "
        f"IMPORTANT: do NOT use `import Mathlib` (the full umbrella import is broken in this "
        f"environment); import only the specific modules you need (the skeleton lists good "
        f"candidates; drop any import that fails to resolve). "
        f"The proof MUST be `sorry`-free: a file containing `sorry` type-checks but is "
        f"NOT a proof and will be REJECTED (strict mode). Close every goal with "
        f"nlinarith/polyrith/positivity/etc.\n"
        f"Output ONLY a single Lean 4 code block."
    )
    history = [{"role": "user", "content": lean_prompt}]
    record = {"attempts": [], "code": None, "compile_ok": None}

    for attempt in range(1, repair_rounds + 2):
        reply, elapsed = call_api(lean4_system(system), history,
                                  effort=effort, label=f"lean4-writer#{attempt}")
        code = extract_lean_code(reply)
        ok, diag = lean_compile_check(code, tag)
        record["attempts"].append({"attempt": attempt, "compile_ok": ok,
                                   "diagnostics": diag[:1500], "elapsed_s": elapsed})
        record["code"] = code
        record["compile_ok"] = ok
        print(f"  [Lean4] attempt {attempt}: compile {'OK' if ok else ('SKIPPED' if ok is None else 'FAILED')}")
        if ok or ok is None or attempt == repair_rounds + 1:
            break
        history.append({"role": "assistant", "content": reply})
        history.append({"role": "user", "content":
                        f"The code failed to compile. Compiler diagnostics:\n{diag}\n\n"
                        f"{repair_hint(diag)}\n\n"
                        f"Fix the errors and output the full corrected Lean 4 code block."})
    return record
