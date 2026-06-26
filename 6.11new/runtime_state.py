"""
runtime_state.py — single source of truth for process-wide mutable state + the
LLM transport, plus optional-dependency guards and runtime constants.

Everything here is "live" at runtime: the one canonical mutable API_CONFIG dict,
the active PROVIDER backend key, the static PROVIDERS catalog, the TOKENS usage
accumulator, and call_api (the only network transport). The ONLY mutators of
provider/token state live here too (select_provider / active_provider /
reset_tokens), so the `global PROVIDER` write and its reads stay in one module.

DAG root: imports nothing internal. Other modules import FROM here, never the
reverse. Never rebind API_CONFIG / TOKENS after their one definition — mutate in
place, so every `from runtime_state import API_CONFIG` shares the same object.
"""

import json
import os
import time

import requests

# Set by call_log.init_run() — when non-None, every call_api invocation is
# appended to the run's calls.jsonl with full prompt + response.
_CALL_LOG_FN = None

# Persistent keep-alive sessions (reusing one connection is what keeps the flaky
# local proxy stable — far better than a fresh TLS handshake per call).
#  _SESSION        : honors HTTP(S)_PROXY env  → overseas relays (aigocode)
#  _SESSION_DIRECT : trust_env=False, NO proxy → China-domestic endpoints (GLM).
# A per-request proxies={} does NOT reliably override env proxies in requests;
# only trust_env=False does, hence a separate session.
_SESSION = requests.Session()
_SESSION_DIRECT = requests.Session()
_SESSION_DIRECT.trust_env = False

try:
    import sympy as sp  # noqa: F401  (bound for the guard side-effect / parity)
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False

try:
    from scipy.integrate import solve_ivp  # noqa: F401
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False

# ─────────────────────────────────────────────
# Secrets: load KEY=VALUE lines from a gitignored `.secrets.env` next to this
# file into os.environ (without overriding already-set vars). Keeps API keys out
# of source/git while letting `python3 webapp/server.py` just work.
# ─────────────────────────────────────────────
def _load_secrets():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".secrets.env")
    try:
        with open(path, encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))
    except FileNotFoundError:
        pass


_load_secrets()

# ─────────────────────────────────────────────
# API configuration (single canonical mutable dict)
# ─────────────────────────────────────────────
# Only `timeout` and `model` are consumed by call_api; `model` is always
# overwritten by the active provider via select_provider(). Defined ONCE here;
# mutate in place (never rebind) so every importer shares this same dict.
API_CONFIG = {
    "model": os.environ.get("OPENAI_MODEL", "gpt-5.5"),
    "timeout": int(os.environ.get("API_TIMEOUT_MS", "120000")) // 1000,
}

# Backend selector: "anthropic" (Claude) or "openai" (codex/GPT). Override with
# env PROVIDER=... or the --provider CLI flag. Both backends hit the SAME aigocode
# relay, just a different endpoint/protocol (see PROVIDERS below). The active
# backend's model is synced into API_CONFIG["model"] by select_provider().
PROVIDER = os.environ.get("PROVIDER", "glm")

# Lake project used to compile LLM-written Lean. MUST be a project whose .lake
# deps (mathlib + aesop + batteries ...) are fully built, else every `lake env
# lean` fails on a missing .olean. Override with env LEAN_PROJECT; default to the
# fully-built ~/lean (paper4's own .lake deps are not built in this environment).
LEAN_PROJECT = os.path.expanduser(
    os.environ.get("LEAN_PROJECT")
    or os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # fallback: paper4/
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
    # Zhipu GLM — cheaper backend. OpenAI chat/completions protocol (api_type
    # "chat", distinct from the openai *Responses* API above). Key from env only
    # (GLM_API_KEY, e.g. via .secrets.env); never hardcoded.
    "glm": {
        "name": "zhipu-glm",
        "base_url": os.environ.get(
            "GLM_BASE_URL", "https://open.bigmodel.cn/api/paas/v4/chat/completions"),
        "api_key": os.environ.get("GLM_API_KEY", ""),
        "api_type": "chat",
        "model": os.environ.get("GLM_MODEL", "glm-4-flash"),
        # open.bigmodel.cn is a China-domestic endpoint — connect DIRECT, bypassing
        # the local Clash proxy (which flaps and breaks TLS to it). Override with
        # GLM_DIRECT=0 if you actually need the proxy to reach it.
        "direct": os.environ.get("GLM_DIRECT", "1") != "0",
        # GLM-5.x are reasoning models. With thinking ENABLED they spend 1600+
        # reasoning chunks / ~40s on even a trivial proof (measured: 6.3s disabled
        # vs 41.5s enabled, IDENTICAL output), and that long silent reasoning phase
        # is what makes the connection drop mid-generation. The escalation loop
        # (L1/L2/L3) already supplies quality recovery, so default thinking OFF for
        # speed + reliability. Set GLM_THINKING=enabled to turn it back on.
        "thinking": os.environ.get("GLM_THINKING", "disabled"),
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

# ─────────────────────────────────────────────
# Token-accounted API transport
# ─────────────────────────────────────────────
TOKENS = {"input": 0, "output": 0, "calls": []}


def reset_tokens():
    TOKENS["input"] = 0
    TOKENS["output"] = 0
    TOKENS["calls"] = []


def call_api(system_prompt: str, messages: list, retries: int = 8,
             effort: str = None, label: str = "", provider: str = None) -> tuple:
    """Returns (text, elapsed_s). Token usage is accumulated in TOKENS.
    Fails over to the next entry in PROVIDERS when the current one keeps erroring.
    Supports Anthropic / OpenAI-Responses / OpenAI-chat (GLM) API formats.

    provider: optional backend key ('glm'/'openai'/'anthropic') for THIS call only —
    used for model-escalation (e.g. fall back to the stronger gpt-5.5 when GLM can't
    crack a hard obstruction) WITHOUT mutating the global PROVIDER, so it is safe to
    interleave with concurrent default-provider calls."""
    if provider is not None and provider not in PROVIDERS:
        raise ValueError(f"unknown provider {provider!r}")
    effort = effort or os.environ.get("OPENAI_REASONING_EFFORT", "medium")
    _t0 = time.time()

    text = ""
    usage = {}
    last_err = None
    for attempt in range(1, retries + 2):
        prov = PROVIDERS[provider] if provider else active_provider()
        # model is synced into API_CONFIG only for the active provider; an overridden
        # provider must use ITS OWN model, not the active one.
        model = prov["model"] if provider else API_CONFIG["model"]
        api_type = prov.get("api_type", "openai")

        # Build payload based on API type
        if api_type == "anthropic":
            # Anthropic Messages API format
            budget = ANTHROPIC_THINKING_BUDGET.get(effort)
            payload = {
                "model": model,
                "system": system_prompt,
                "messages": messages,
                "max_tokens": (budget + 4096) if budget else 4096,
                "stream": True,
            }
            if budget:
                # extended thinking: map effort level -> thinking token budget
                payload["thinking"] = {"type": "enabled", "budget_tokens": budget}
            headers = {
                "Authorization": f"Bearer {prov['api_key']}",
                "Content-Type": "application/json",
                "anthropic-version": "2023-06-01",
            }
        elif api_type == "chat":
            # OpenAI chat/completions format (Zhipu GLM). system goes in-band as
            # the first message; no Responses-style `instructions`/`reasoning`.
            payload = {
                "model": model,
                "messages": [{"role": "system", "content": system_prompt}] + messages,
                # GLM-5.x are reasoning models: with thinking on, reasoning_content
                # burns 1600+ chunks before the answer. Default OFF (see provider
                # config) for speed + connection stability; headroom kept generous
                # so an enabled run still has room for the answer after reasoning.
                "max_tokens": 8192,
                "stream": True,   # direct GLM streams (long non-stream POSTs get reset)
                "thinking": {"type": prov.get("thinking", "disabled")},
            }
            headers = {
                "Authorization": f"Bearer {prov['api_key']}",
                "Content-Type": "application/json",
            }
        else:
            # OpenAI Responses API format
            payload = {
                "model": model,
                "instructions": system_prompt,
                "input": messages,
                "max_output_tokens": 2048,
                "reasoning": {"effort": effort},
                "store": False,
                "stream": True,
            }
            headers = {
                "Authorization": f"Bearer {prov['api_key']}",
                "Content-Type": "application/json",
            }

        text, usage, last_err = "", {}, None
        # GLM chat: STREAM when connecting DIRECT. A long non-streaming POST to
        # open.bigmodel.cn sends zero bytes during generation, so the idle
        # connection gets reset mid-flight (~60s in) → ConnectionError on exactly
        # the heavy Lean-writer calls. Streaming keeps bytes flowing and is robust
        # (measured: nonstream FAIL@65s vs stream OK 3678 chunks). The old
        # non-stream choice only applied to the PROXIED relay (which drops SSE);
        # direct GLM bypasses that relay, so stream there.
        stream_mode = (api_type != "chat") or bool(prov.get("direct"))
        try:
            # domestic endpoints (GLM) use the trust_env=False session → truly no proxy;
            # overseas relays use the proxy-honoring session.
            sess = _SESSION_DIRECT if prov.get("direct") else _SESSION
            resp = sess.post(
                prov["base_url"], headers=headers, json=payload,
                timeout=API_CONFIG["timeout"], verify=False, stream=stream_mode,
            )
            if not resp.ok:
                last_err = f"HTTP {resp.status_code}: {resp.text[:200]}"
            elif not stream_mode:
                # non-streaming chat (GLM): parse the whole JSON body at once. We read
                # message.content only; reasoning_content (GLM-5.x thinking) is ignored.
                data = resp.json()
                msg = (data.get("choices") or [{}])[0].get("message", {}) or {}
                text = msg.get("content") or ""
                u = data.get("usage") or {}
                usage["input_tokens"] = u.get("prompt_tokens", 0)
                usage["output_tokens"] = u.get("completion_tokens", 0)
                if not text:
                    last_err = f"empty content (finish={(data.get('choices') or [{}])[0].get('finish_reason')})"
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
                    elif api_type == "chat":
                        # OpenAI chat/completions streaming (GLM): deltas in
                        # choices[0].delta.content; usage in a trailing chunk.
                        for ch in chunk.get("choices", []):
                            text += (ch.get("delta", {}) or {}).get("content") or ""
                        u = chunk.get("usage")
                        if u:
                            usage["input_tokens"] = u.get("prompt_tokens", 0)
                            usage["output_tokens"] = u.get("completion_tokens", 0)
                        if chunk.get("error"):
                            last_err = f"stream error: {str(chunk.get('error'))[:200]}"
                    else:
                        # OpenAI Responses format
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
        # Transient transport flakiness (local relay drops SSL / empties) → retry
        # fast; genuine errors (rate limit / HTTP) → exponential back off.
        le = last_err or ""
        transient = any(k in le for k in ("SSL", "Connection", "Timeout", "empty"))
        wait = 2 if transient else min(attempt * 6, 30)
        print(f"  [Retry {attempt}/{retries}] {last_err} (provider {prov['name']}), retrying in {wait}s...")
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
    if _CALL_LOG_FN:
        try:
            _CALL_LOG_FN(label=label, system_prompt=system_prompt,
                         messages=messages, response=text,
                         provider=prov["name"], model=model,
                         tokens_in=rec["input_tokens"],
                         tokens_out=rec["output_tokens"],
                         elapsed_s=elapsed, error=None)
        except Exception:
            pass
    return text.strip(), elapsed


# Seed API_CONFIG['model'] from the default backend (import-time side effect).
select_provider(PROVIDER)
