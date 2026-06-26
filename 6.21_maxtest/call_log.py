"""
call_log.py — structured logging for all LLM calls and Lean compilation checks.

Directory layout per run:
    logs/
      run_{YYYYMMDD}_{HHMMSS}_{tag}/
        meta.json       # run config (provider, model, flags, recipe count)
        calls.jsonl     # every API call: label, prompt, response, tokens, timing
        lean.jsonl      # every Lean check: tag, code, diagnostic, ok

Usage:
    from call_log import init_run
    init_run(tag="untested", provider="glm", model="glm-4.7", budget=200000)
    # ... hooks are auto-installed in runtime_state and lean_proof
    # all subsequent call_api / lean_compile_check calls are logged

No internal imports — hooks are installed into runtime_state / lean_proof
at init_run() time so those modules stay import-clean.
"""

import json
import os
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS_DIR = os.path.join(HERE, "logs")

_RUN_DIR = None
_CALL_SEQ = 0
_LEAN_SEQ = 0


def init_run(tag="", **meta):
    """Create a run directory, write meta.json, install hooks. Returns run_dir."""
    global _RUN_DIR, _CALL_SEQ, _LEAN_SEQ

    ts = time.strftime("%Y%m%d_%H%M%S")
    parts = ["run", ts]
    if tag:
        parts.append(tag)
    name = "_".join(parts)

    _RUN_DIR = os.path.join(LOGS_DIR, name)
    os.makedirs(_RUN_DIR, exist_ok=True)
    _CALL_SEQ = 0
    _LEAN_SEQ = 0

    with open(os.path.join(_RUN_DIR, "meta.json"), "w") as f:
        json.dump({"ts": ts, "tag": tag, "run_dir": _RUN_DIR, **meta},
                  f, indent=2, ensure_ascii=False)

    import runtime_state
    runtime_state._CALL_LOG_FN = log_call
    import lean_proof
    lean_proof._LEAN_LOG_FN = log_lean

    print(f"  [log] run dir: {_RUN_DIR}")
    return _RUN_DIR


def current_run_dir():
    return _RUN_DIR


def log_call(*, label, system_prompt, messages, response,
             provider, model, tokens_in, tokens_out, elapsed_s, error=None):
    if not _RUN_DIR:
        return
    global _CALL_SEQ
    _CALL_SEQ += 1
    rec = {
        "seq": _CALL_SEQ,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "label": label,
        "provider": provider,
        "model": model,
        "system_prompt": system_prompt,
        "messages": messages,
        "response": response,
        "tokens_in": tokens_in,
        "tokens_out": tokens_out,
        "elapsed_s": elapsed_s,
        "error": error,
    }
    with open(os.path.join(_RUN_DIR, "calls.jsonl"), "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")


def log_lean(*, tag, code, ok, diagnostic, elapsed_s):
    if not _RUN_DIR:
        return
    global _LEAN_SEQ
    _LEAN_SEQ += 1
    rec = {
        "seq": _LEAN_SEQ,
        "ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "tag": tag,
        "code": code,
        "ok": ok,
        "diagnostic": diagnostic,
        "elapsed_s": elapsed_s,
    }
    with open(os.path.join(_RUN_DIR, "lean.jsonl"), "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
