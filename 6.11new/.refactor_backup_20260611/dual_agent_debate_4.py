#!/usr/bin/env python3
"""
dual_agent_debate_4_claude.py — iterated barrier-synthesis pipeline (v4) for Claude API.

CHANGED from dual_agent_debate_4.py:
  - Uses Anthropic Messages API format instead of OpenAI Responses API
  - Default model changed to claude-sonnet-4-6 for Anthropic compatibility
  - Only uses aigocode provider with Anthropic endpoint

Changes vs dual_agent_debate_3.py (which stays untouched, for A/B comparison):
  1. Local-first verification: sympy/scipy checks run BEFORE the LLM Refuter.
     Numerically broken proposals never reach the (expensive) Refuter; precise
     numeric counterexamples are fed straight back to the Proposer.
  2. Token accounting: every call records input/output tokens from the
     Responses API `usage` field; totals land in the result JSON.
  3. Compact context: the Refuter is stateless; the Proposer receives a bounded
     summary of past attempts instead of the full conversation history.
  4. Counterexample cache: violation points found in any turn are re-checked
     against every new proposal locally (zero tokens) before any API call.
  5. Reasoning-effort ladder: medium -> high -> xhigh, escalating on failure.
  6. Lean4 compile loop: generated code is compiled with `lake env lean` in the
     paper4 project; on error the diagnostics are fed back for repair.
  7. Optional knowledge-base few-shot injection (knowledge_base.py) and
     auto-recording of solved cases.
  8. External datasets via dataset_loader.py (--dataset / --entry-id).
"""
import argparse
import datetime
import json
import os
import re
import subprocess
import time

import numpy as np

from dual_agent_debate_3 import (
    API_CONFIG as _ORIGINAL_API_CONFIG, SYSTEMS, HAS_SYMPY, HAS_SCIPY,
    proposer_system, refuter_system, lean4_system,
    verify_symbolic, verify_trajectory, plot_barrier,
    parse_json_response, _parse_B_expr,
)
from knowledge_base import KnowledgeBase

# Backend selector: "anthropic" (Claude) or "openai" (codex/GPT). Override with
# env PROVIDER=... or the --provider CLI flag. Both backends hit the SAME aigocode
# relay, just a different endpoint/protocol (see PROVIDERS below). The active
# backend's model is synced into API_CONFIG["model"] by select_provider().
PROVIDER = os.environ.get("PROVIDER", "anthropic")
API_CONFIG = _ORIGINAL_API_CONFIG.copy()

if HAS_SYMPY:
    import sympy as sp
if HAS_SCIPY:
    from scipy.integrate import solve_ivp

import requests

LEAN_PROJECT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # paper4/
EFFORT_LADDER = ["high", "high", "high"]

# Both backends go through the same aigocode relay; they differ only in endpoint
# (Messages vs Responses API), key, protocol (api_type) and default model. Pick one
# with PROVIDER / --provider — this is a SELECTOR for A/B comparison, NOT failover.
PROVIDERS = {
    "anthropic": {
        "name": "aigocode-claude",
        "base_url": "https://api.aigocode.app/v1/messages",
        "api_key": os.environ.get(
            "AIGOCODE_ANTHROPIC_KEY",
            "sk-a6c65bf8fdd1b0ddc6f843ee5d01d9cd72a5b422a58485ce84608c32a1abc02f"),
        "api_type": "anthropic",
        "model": os.environ.get("ANTHROPIC_MODEL", "claude-sonnet-4-6"),
    },
    "openai": {
        "name": "aigocode-codex",
        "base_url": "https://api.aigocode.app/v1/responses",
        "api_key": os.environ.get(
            "AIGOCODE_OPENAI_KEY",
            "sk-e59f1aa0852e153fdd55aa650fa4bec803322b845e6c3229daad670b717979fa"),
        "api_type": "openai",
        "model": os.environ.get("OPENAI_MODEL", "gpt-5.5"),
    },
}

# Claude has no `reasoning.effort` knob like OpenAI; instead it takes an extended-
# thinking token budget. We translate the shared EFFORT_LADDER level -> budget here.
# (missing level = thinking disabled). max_tokens is bumped to leave room for the
# answer on top of the thinking budget.
ANTHROPIC_THINKING_BUDGET = {"medium": 2048, "high": 4096, "xhigh": 6144}


def select_provider(name: str):
    """Activate a backend by key ('anthropic' or 'openai') and sync its model."""
    global PROVIDER
    if name not in PROVIDERS:
        raise SystemExit(f"unknown provider {name!r}; choose from {list(PROVIDERS)}")
    PROVIDER = name
    API_CONFIG["model"] = PROVIDERS[name]["model"]
    return PROVIDERS[name]


def active_provider():
    return PROVIDERS[PROVIDER]


select_provider(PROVIDER)  # initialise API_CONFIG["model"] from the default backend

# ─────────────────────────────────────────────
# Token-accounted API call
# ─────────────────────────────────────────────
TOKENS = {"input": 0, "output": 0, "calls": []}


def reset_tokens():
    TOKENS["input"] = 0
    TOKENS["output"] = 0
    TOKENS["calls"] = []


def call_api(system_prompt: str, messages: list, retries: int = 5,
             effort: str = None, label: str = "") -> tuple:
    """Returns (text, elapsed_s). Token usage is accumulated in TOKENS.
    Fails over to the next entry in PROVIDERS when the current one keeps erroring.
    CHANGED: Support both Anthropic and OpenAI API formats."""
    effort = effort or os.environ.get("OPENAI_REASONING_EFFORT", "medium")
    _t0 = time.time()

    text = ""
    usage = {}
    last_err = None
    for attempt in range(1, retries + 2):
        provider = active_provider()
        api_type = provider.get("api_type", "openai")

        # Build payload based on API type
        if api_type == "anthropic":
            # Anthropic Messages API format
            budget = ANTHROPIC_THINKING_BUDGET.get(effort)
            payload = {
                "model": API_CONFIG["model"],
                "system": system_prompt,
                "messages": messages,
                "max_tokens": (budget + 4096) if budget else 4096,
                "stream": True,
            }
            if budget:
                # extended thinking: map effort level -> thinking token budget
                payload["thinking"] = {"type": "enabled", "budget_tokens": budget}
            headers = {
                "Authorization": f"Bearer {provider['api_key']}",
                "Content-Type": "application/json",
                "anthropic-version": "2023-06-01",
            }
        else:
            # OpenAI Responses API format
            payload = {
                "model": API_CONFIG["model"],
                "instructions": system_prompt,
                "input": messages,
                "max_output_tokens": 2048,
                "reasoning": {"effort": effort},
                "store": False,
                "stream": True,
            }
            headers = {
                "Authorization": f"Bearer {provider['api_key']}",
                "Content-Type": "application/json",
            }

        text, usage, last_err = "", {}, None
        try:
            resp = requests.post(
                provider["base_url"], headers=headers, json=payload,
                timeout=API_CONFIG["timeout"], verify=False, stream=True,
            )
            if not resp.ok:
                last_err = f"HTTP {resp.status_code}: {resp.text[:200]}"
            else:
                for line in resp.iter_lines():
                    if not line:
                        continue
                    line = line.decode("utf-8") if isinstance(line, bytes) else line
                    if not line.startswith("data:"):
                        continue
                    data_str = line[len("data:"):].strip()
                    if data_str == "[DONE]":
                        break
                    try:
                        chunk = json.loads(data_str)
                    except json.JSONDecodeError:
                        continue

                    # Parse based on API type
                    if api_type == "anthropic":
                        event_type = chunk.get("type", "")
                        if event_type == "content_block_delta":
                            delta = chunk.get("delta", {})
                            if delta.get("type") == "text_delta":
                                text += delta.get("text", "")
                        elif event_type == "message_delta":
                            usage_delta = chunk.get("usage", {})
                            if usage_delta:
                                usage["output_tokens"] = usage_delta.get("output_tokens", 0)
                        elif event_type == "message_start":
                            msg = chunk.get("message", {})
                            msg_usage = msg.get("usage", {})
                            if msg_usage:
                                usage["input_tokens"] = msg_usage.get("input_tokens", 0)
                        elif event_type == "error":
                            last_err = f"stream error: {str(chunk.get('error', {}))[:200]}"
                    else:
                        # OpenAI format
                        event_type = chunk.get("type", "")
                        if event_type == "response.output_text.delta":
                            text += chunk.get("delta", "")
                        elif event_type in ("response.failed", "error"):
                            err_obj = chunk.get("response", {}).get("error") or chunk.get("error") or {}
                            last_err = f"stream error: {str(err_obj)[:200]}"
                        elif event_type == "response.completed":
                            response_obj = chunk.get("response", {})
                            usage = response_obj.get("usage", {}) or {}
                            if not text:
                                for item in response_obj.get("output", []):
                                    for content in item.get("content", []):
                                        if content.get("type") == "output_text":
                                            text += content.get("text", "")
                # an aborted/empty stream (relay flakiness) must be retried too
                if not text and not last_err:
                    last_err = "empty response (stream ended without output)"
        except requests.RequestException as e:
            last_err = type(e).__name__

        if text and not last_err:
            break
        if attempt > retries:
            raise RuntimeError(f"API failed after {retries + 1} attempts: {last_err}")
        # single active backend (selector, not failover) — just back off and retry
        wait = min(attempt * 12, 60)
        print(f"  [Retry {attempt}/{retries}] {last_err} (provider {provider['name']}), retrying in {wait}s...")
        time.sleep(wait)

    elapsed = round(time.time() - _t0, 3)
    rec = {
        "label": label,
        "effort": effort,
        "input_tokens": usage.get("input_tokens", 0),
        "output_tokens": usage.get("output_tokens", 0),
        "elapsed_s": elapsed,
    }
    TOKENS["input"] += rec["input_tokens"]
    TOKENS["output"] += rec["output_tokens"]
    TOKENS["calls"].append(rec)
    print(f"  [Tokens] {label or 'call'} ({effort}): in={rec['input_tokens']} out={rec['output_tokens']}")
    return text.strip(), elapsed


# ─────────────────────────────────────────────
# Counterexample cache
# ─────────────────────────────────────────────
def _pt_to_array(pt: dict, state_vars: list) -> np.ndarray:
    return np.array([float(pt[v]) for v in state_vars])


def precheck_cache(system: dict, h_str: str, cache: dict) -> list:
    """Re-check a new h against previously found violation points. Zero tokens.
    Returns a list of human-readable failure strings (empty = pass)."""
    if not HAS_SYMPY:
        return []
    state_vars = system["state_vars"]
    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return [f"h expression unparseable: {h_str}"]
    sym_list = [syms[v] for v in state_vars]
    try:
        h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")
    except Exception as e:
        return [f"h cannot be lambdified: {e}"]

    fails = []
    for pt in cache.get("xu_points", []):
        x = _pt_to_array(pt, state_vars)
        try:
            hv = float(h_func(*x))
        except Exception:
            continue
        if hv >= 0:
            fails.append(f"Condition 1 fails at known unsafe point {pt}: h = {hv:.5g} (must be < 0)")

    # escape points: only relevant if the new C still contains them
    if HAS_SCIPY and system.get("f_expr") and cache.get("escape_points"):
        try:
            f_sym = [sp.sympify(fe.replace("^", "**"),
                                locals={**syms, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
                     for fe in system["f_expr"]]
            f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]
        except Exception:
            return fails

        def ode_rhs(t, state):
            return [float(fi(*state)) for fi in f_funcs]

        for pt in cache.get("escape_points", [])[:5]:
            x0 = _pt_to_array(pt, state_vars)
            try:
                if float(h_func(*x0)) < 0:
                    continue  # point no longer inside C, not a counterexample for new h
                sol = solve_ivp(ode_rhs, [0, 15.0], x0.tolist(), max_step=0.05,
                                rtol=1e-6, atol=1e-8)
                if not sol.success:
                    continue
                h_traj = np.array(h_func(*sol.y), dtype=float)
                if float(np.min(h_traj)) < -1e-3:
                    fails.append(
                        f"Known escaping trajectory still escapes: x0={pt}, min h(x(t)) = {float(np.min(h_traj)):.5g}")
            except Exception:
                continue
    return fails


def harvest_cache(cache: dict, sym_result: dict, traj_result: dict):
    for pt in sym_result.get("cond1_violations", []) or []:
        if pt not in cache["xu_points"]:
            cache["xu_points"].append(pt)
    for v in (traj_result.get("violations", []) or []):
        pt = v.get("x0")
        if pt and pt not in cache["escape_points"]:
            cache["escape_points"].append(pt)


# ─────────────────────────────────────────────
# Non-triviality guard: reject empty / degenerate invariant sets
# ─────────────────────────────────────────────
def nontrivial_C_check(system: dict, h_str: str, n: int = 5000, min_pts: int = 5) -> str:
    """Reject barriers whose invariant set C = {x in X : h(x) >= 0} is empty or
    near-empty inside the domain (e.g. h = -1). Conditions hold vacuously on an
    empty set, so such 'solutions' are degenerate cheats. Returns a failure string
    (empty = OK)."""
    if not HAS_SYMPY:
        return ""
    state_vars = system["state_vars"]
    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return ""  # parse failure is handled elsewhere
    sym_list = [syms[v] for v in state_vars]
    try:
        h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")
    except Exception:
        return ""
    bounds = system.get("X_bounds", [(-3, 3)] * len(state_vars))
    rng = np.random.default_rng(7)
    pts = np.column_stack([rng.uniform(lo, hi, n) for lo, hi in bounds])
    try:
        h_vals = np.broadcast_to(np.array(h_func(*pts.T), dtype=float), n)
    except Exception:
        return ""
    inside = int(np.count_nonzero(np.isfinite(h_vals) & (h_vals >= 0)))
    if inside < min_pts:
        return (f"Invariant set C = {{x in X : h(x) >= 0}} is empty/degenerate: only "
                f"{inside}/{n} sampled domain points satisfy h(x) >= 0. The conditions "
                f"hold only vacuously — propose a NON-trivial h whose C has real volume "
                f"inside the domain (h must be positive on a meaningful region).")
    return ""


# ─────────────────────────────────────────────
# Local verification bundle (runs BEFORE the Refuter)
# ─────────────────────────────────────────────
def local_verify(system: dict, h_str: str, cache: dict) -> dict:
    out = {"cache_fails": [], "symbolic": {}, "trajectory": {}, "passed": False, "feedback": ""}

    out["cache_fails"] = precheck_cache(system, h_str, cache)
    trivial_fail = nontrivial_C_check(system, h_str)
    if trivial_fail:
        out["cache_fails"].append(trivial_fail)

    sym_result, traj_result = {}, {}
    sym_ok = traj_ok = None
    if HAS_SYMPY and system.get("f_expr"):
        _t = time.time()
        sym_result = verify_symbolic(system, h_str)
        sym_result["elapsed_s"] = round(time.time() - _t, 3)
        sym_ok = sym_result.get("symbolic_valid")
    if HAS_SCIPY and HAS_SYMPY and system.get("f_expr"):
        _t = time.time()
        traj_result = verify_trajectory(system, h_str)
        traj_result["elapsed_s"] = round(time.time() - _t, 3)
        traj_ok = traj_result.get("trajectory_valid")

    out["symbolic"] = sym_result
    out["trajectory"] = traj_result
    harvest_cache(cache, sym_result, traj_result)

    out["passed"] = (not out["cache_fails"]) and (sym_ok is not False) and (traj_ok is not False)
    if out["passed"]:
        return out

    parts = list(out["cache_fails"])
    if sym_ok is False:
        if not sym_result.get("cond1_ok", True):
            parts.append(f"Condition 1 failed: max h on X_u = {sym_result.get('cond1_max_h_in_Xu')} (must be < 0).")
            if sym_result.get("cond1_violations"):
                parts.append(f"Violation points: {sym_result['cond1_violations']}")
        if not sym_result.get("cond2_ok", True):
            parts.append(
                f"Condition 2 (Nagumo) failed: min hdot on boundary = {sym_result.get('cond2_min_lie_on_boundary')} "
                f"(must be >= 0). Lie derivative = {sym_result.get('lie_derivative')}")
            if sym_result.get("cond2_violations"):
                parts.append(f"Violation points: {sym_result['cond2_violations']}")
    if traj_ok is False:
        parts.append(
            f"Trajectory check failed: min h along trajectories from inside C = {traj_result.get('min_h_on_trajs')} "
            f"(must stay >= 0).")
        for v in (traj_result.get("violations") or [])[:2]:
            parts.append(f"  escaping trajectory: x0={v['x0']}, min h={v['min_h']} at t={v['t_violation']}")
    if sym_result.get("error"):
        parts.append(f"Symbolic verification error: {sym_result['error']}")
    out["feedback"] = "\n".join(parts)
    return out


# ─────────────────────────────────────────────
# Compact Proposer context
# ─────────────────────────────────────────────
def build_proposer_msg(system: dict, attempts: list, cache: dict, kb_block: str,
                       refuter_critique: str = None, enlargement_hint: str = None) -> str:
    base = (
        f"Please propose a barrier function h(x) for the following system "
        f"such that the invariant set C = {{x in X : h(x) >= 0}} is as large as possible:\n\n"
        f"System: {system['ode']}\n"
        f"State domain: {system['X_domain']}\n"
        f"Unsafe set: {system['X_u_desc']}"
    )
    sections = [base]
    if kb_block:
        sections.append(kb_block)
    if attempts:
        lines = ["[Your previous attempts and why each failed — do NOT repeat these mistakes]"]
        for a in attempts[-4:]:
            lines.append(f"- h = {a['h']}\n  failure: {a['failure'][:600]}")
        sections.append("\n".join(lines))
    cex = cache.get("xu_points", []) + cache.get("escape_points", [])
    if cex:
        sections.append(
            "[Known counterexample points — your new h MUST handle all of them]\n" +
            json.dumps(cex[:10], ensure_ascii=False))
    if refuter_critique:
        sections.append(f"[Verifier critique of the last proposal]\n{refuter_critique[:1500]}")
    if enlargement_hint:
        sections.append(
            f"[The last h was VALID. Suggestion to enlarge the invariant set]\n{enlargement_hint}\n"
            f"Only adjust it if you can keep both conditions satisfied; otherwise return the valid h unchanged.")
    sections.append("Output the JSON object in the required format.")
    return "\n\n".join(sections)


# ─────────────────────────────────────────────
# Lean 4 compile loop
# ─────────────────────────────────────────────
def extract_lean_code(text: str) -> str:
    blocks = re.findall(r"```(?:lean4?)?\s*\n(.*?)```", text, re.S)
    return "\n\n".join(b.strip() for b in blocks) if blocks else text.strip()


def lean_compile_check(code: str, tag: str, timeout: int = 300) -> tuple:
    """Compile `code` inside the paper4 lake project. Returns (ok, diagnostics)."""
    path = os.path.join(LEAN_PROJECT, f"_check_{tag}.lean")
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(code)
        proc = subprocess.run(
            ["lake", "env", "lean", path], cwd=LEAN_PROJECT,
            capture_output=True, text=True, timeout=timeout,
        )
        diag = (proc.stdout + "\n" + proc.stderr).strip()
        return proc.returncode == 0, diag[:4000]
    except subprocess.TimeoutExpired:
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
    lean_prompt = (
        f"Please generate a Lean 4 formal proof for the following verified barrier function:\n\n"
        f"System dynamics: {system['ode']}\n"
        f"State domain: {system['X_domain']}\n"
        f"Unsafe set: {system['X_u_desc']}\n"
        f"State variables: {', '.join(system['state_vars'])}\n"
        f"Barrier function: h(x) = {final.get('h', 'unknown')}\n"
        f"Invariant set: C = {{x in X : h(x) >= 0}} = {final.get('invariant_set', 'unknown')}\n"
        f"Lie derivative: hdot = {final.get('lie_derivative', 'unknown')}\n\n"
        f"The code will be compiled with `lake env lean` against Mathlib4 — it must compile. "
        f"IMPORTANT: do NOT use `import Mathlib` (the full umbrella import is broken in this "
        f"environment); import only the specific modules you need, e.g. "
        f"`import Mathlib.Analysis.Calculus.Deriv.Basic`. "
        f"Prefer `sorry`-free proofs via nlinarith/polyrith/positivity where possible; "
        f"a compiling skeleton with explicit `sorry` for genuinely hard steps is acceptable.\n"
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
                        f"Fix the errors and output the full corrected Lean 4 code block."})
    return record


# ─────────────────────────────────────────────
# Main synthesis loop (v4)
# ─────────────────────────────────────────────
def run_barrier_synthesis_v4(system_key: str, turns: int = 5, output_dir: str = None,
                             system: dict = None, delay: float = 1.0, use_kb: bool = True,
                             do_plot: bool = True, do_lean: bool = True,
                             lean_repair: int = 2) -> dict:
    system = system or SYSTEMS[system_key]
    out_dir = output_dir or os.path.join(os.path.dirname(os.path.abspath(__file__)), system_key)
    os.makedirs(out_dir, exist_ok=True)
    prefix = os.path.join(out_dir, f"v4_{system_key}")

    kb = KnowledgeBase() if use_kb else None
    kb_block = kb.few_shot_block(system) if kb else ""
    if kb_block:
        print(f"[KB] injected {kb_block.count('Example ')} reference case(s)")

    reset_tokens()
    pipeline_start = time.time()
    print(f"\n{'='*60}\nSystem: {system['name']}\nDynamics: {system['ode']}\n"
          f"Model: {API_CONFIG['model']} | max turns: {turns}\n{'='*60}")

    result = {
        "pipeline": "v4",
        "system": system,
        "timestamp": datetime.datetime.now().isoformat(),
        "model": API_CONFIG["model"],
        "rounds": [],
        "final_barrier": None,
        "solved": False,
        "refuter_calls": 0,
        "lean4": None,
    }

    cache = {"xu_points": [], "escape_points": []}
    attempts = []          # [{h, failure}]
    refuter_critique = None
    enlargement_hint = None
    effort_idx = 0

    for turn in range(1, turns + 1):
        effort = EFFORT_LADDER[min(effort_idx, len(EFFORT_LADDER) - 1)]
        print(f"\n{'─'*50}\nTurn {turn}  (reasoning effort: {effort})\n{'─'*50}")

        user_msg = build_proposer_msg(system, attempts, cache, kb_block if turn == 1 else "",
                                      refuter_critique, enlargement_hint)
        refuter_critique = enlargement_hint = None

        print("[Proposer] generating...")
        reply_a, t_prop = call_api(proposer_system(system), [{"role": "user", "content": user_msg}],
                                   effort=effort, label=f"proposer#{turn}")
        proposal = parse_json_response(reply_a)
        h_str = proposal.get("h", "")
        print(f"  h = {h_str}")

        round_rec = {"turn": turn, "effort": effort, "proposal": proposal,
                     "proposer_elapsed_s": t_prop}
        result["rounds"].append(round_rec)

        if not h_str:
            attempts.append({"h": "(unparseable)", "failure": "output was not valid JSON with an 'h' field"})
            effort_idx += 1
            continue

        # ── local verification FIRST (zero tokens) ──
        print("[Local verification] cache + symbolic + trajectory...")
        lv = local_verify(system, h_str, cache)
        round_rec["local_verification"] = {
            "passed": lv["passed"], "cache_fails": lv["cache_fails"],
            "symbolic": lv["symbolic"], "trajectory": lv["trajectory"],
        }
        if not lv["passed"]:
            print(f"  local FAIL:\n{lv['feedback']}")
            attempts.append({"h": h_str, "failure": lv["feedback"] or "local verification failed"})
            effort_idx += 1
            time.sleep(delay)
            continue
        print("  local PASS — escalating to LLM Refuter")

        # ── LLM Refuter only for locally-passing candidates ──
        refuter_msg = (
            f"Please verify whether the following barrier function is correct:\n\n"
            f"System: {system['ode']}\nState domain: {system['X_domain']}\n"
            f"Unsafe set: {system['X_u_desc']}\nProposed h(x) = {h_str}\n"
            f"Claimed invariant set: {proposal.get('invariant_set', 'unknown')}\n\n"
            f"Local numerical checks (sampling + trajectories) already PASSED. Focus on what "
            f"sampling can miss: rigorous inequality reasoning, behaviour near boundary/corner "
            f"cases, and degenerate points. If valid, also analyze enlargement."
        )
        result["refuter_calls"] += 1
        try:
            reply_b, t_ref = call_api(refuter_system(system), [{"role": "user", "content": refuter_msg}],
                                      effort=EFFORT_LADDER[min(effort_idx + 1, len(EFFORT_LADDER) - 1)],
                                      label=f"refuter#{turn}")
        except RuntimeError as e:
            # relay outage mid-run: keep the locally-verified candidate instead of losing the turn
            print(f"  [Refuter] unavailable after retries ({e}); keeping locally-verified h.")
            result["final_barrier"] = proposal
            result["solved"] = True
            result["refuter_verdict"] = "unavailable (network) — local checks only"
            round_rec["refutation"] = {"verdict": "unavailable", "error": str(e)}
            break
        refutation = parse_json_response(reply_b)
        round_rec["refutation"] = refutation
        round_rec["refuter_elapsed_s"] = t_ref

        if refutation.get("verdict") == "valid":
            print(f"\nTurn {turn}: Refuter confirmed VALID — stopping.")
            result["final_barrier"] = proposal
            result["solved"] = True
            if kb:
                kb.add_case({
                    "id": system_key, "dim": len(system["state_vars"]),
                    "system_class": (system.get("meta") or {}).get("system_class", ""),
                    "ode": system["ode"], "h": h_str,
                    "lie_derivative": lv["symbolic"].get("lie_derivative", ""),
                    "key_steps": (proposal.get("condition2_check") or "")[:800],
                    "source": "pipeline-v4",
                })
                print("[KB] solved case recorded")
            break
        else:
            print(f"  Refuter verdict: invalid — {str(refutation.get('flaw'))[:200]}")
            refuter_critique = json.dumps(
                {k: refutation.get(k) for k in ("flaw", "counterexample", "suggestion")},
                ensure_ascii=False)
            attempts.append({"h": h_str, "failure": f"LLM refuter: {str(refutation.get('flaw'))[:400]}"})
            effort_idx += 1
        time.sleep(delay)

    if not result["final_barrier"] and result["rounds"]:
        result["final_barrier"] = result["rounds"][-1]["proposal"]
        print("\nMax turns reached without a confirmed barrier; keeping the last proposal.")

    final = result["final_barrier"] or {}
    h_final = final.get("h", "")

    if do_plot and h_final:
        try:
            plot_barrier(system, system_key, h_final, prefix)
        except Exception as e:
            print(f"  [Plot] skipped: {e}")

    if do_lean and h_final and result["solved"]:
        print(f"\n{'─'*50}\n[Lean4 Writer] generate + compile loop\n{'─'*50}")
        result["lean4"] = generate_lean_proof(system, final, tag=re.sub(r"\W+", "_", system_key)[:40],
                                              repair_rounds=lean_repair)
        if result["lean4"]["code"]:
            with open(f"{prefix}.lean", "w", encoding="utf-8") as f:
                f.write(f"-- v4 pipeline, compile_ok={result['lean4']['compile_ok']}\n"
                        f"-- System: {system['name']}\n\n{result['lean4']['code']}")

    result["timing"] = {"total_elapsed_s": round(time.time() - pipeline_start, 3)}
    result["tokens"] = {"input": TOKENS["input"], "output": TOKENS["output"],
                        "calls": TOKENS["calls"]}

    out_path = f"{prefix}.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    print(f"\nSolved: {result['solved']} | turns used: {len(result['rounds'])} | "
          f"refuter calls: {result['refuter_calls']} | "
          f"tokens in/out: {TOKENS['input']}/{TOKENS['output']} | "
          f"total: {result['timing']['total_elapsed_s']}s")
    print(f"Results saved: {out_path}")
    return result


# ─────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(description="Barrier synthesis pipeline v4")
    parser.add_argument("--system", default="darboux", help=f"Built-in system: {', '.join(SYSTEMS)}")
    parser.add_argument("--dataset", default=None, help="Path to external dataset (.json/.jsonl)")
    parser.add_argument("--entry-id", default=None, help="Entry id within --dataset")
    parser.add_argument("--turns", type=int, default=5)
    parser.add_argument("--provider", default=None, choices=list(PROVIDERS),
                        help="Backend: 'anthropic' (Claude) or 'openai' (codex/GPT)")
    parser.add_argument("--model", default=None)
    parser.add_argument("--no-kb", action="store_true", help="Disable knowledge-base few-shot")
    parser.add_argument("--no-lean", action="store_true", help="Skip Lean4 phase")
    parser.add_argument("--no-plot", action="store_true")
    parser.add_argument("--lean-repair", type=int, default=2, help="Max Lean repair rounds")
    args = parser.parse_args()

    if args.provider:
        select_provider(args.provider)
    if args.model:
        API_CONFIG["model"] = args.model  # explicit override wins over provider default

    if args.dataset:
        from dataset_loader import load_dataset
        entries, skipped = load_dataset(
            args.dataset,
            call_fn=lambda s, m: call_api(s, m, effort="medium", label="dataset-convert"))
        if skipped:
            print(f"[Dataset] skipped {len(skipped)} entries (first 3: {skipped[:3]})")
        wanted = [(eid, sysd) for eid, sysd in entries
                  if args.entry_id is None or eid == args.entry_id]
        if not wanted:
            raise SystemExit(f"entry id {args.entry_id!r} not found; available: {[e for e, _ in entries][:20]}")
        eid, system = wanted[0]
        key = re.sub(r"\W+", "_", eid)[:50]
        run_barrier_synthesis_v4(key, turns=args.turns, system=system,
                                 use_kb=not args.no_kb, do_plot=not args.no_plot,
                                 do_lean=not args.no_lean, lean_repair=args.lean_repair)
    else:
        run_barrier_synthesis_v4(args.system, turns=args.turns,
                                 use_kb=not args.no_kb, do_plot=not args.no_plot,
                                 do_lean=not args.no_lean, lean_repair=args.lean_repair)


if __name__ == "__main__":
    main()
