#!/usr/bin/env python3
"""
server.py — zero-dependency web front-end for the barrier-synthesis pipeline so a
small group can try it. Pure Python stdlib (http.server + threads + SSE); no pip.

Design (see webapp/README.md):
  • Lean must run where mathlib is built → this server runs on YOUR machine.
  • API key stays server-side (env). Group members only get a URL (via cloudflared).
  • Long-running job → background thread + Server-Sent Events streaming the live
    pipeline log (the same print() lines) to the browser.
  • Guardrails: a shared password (APP_PASSWORD) gates the public URL; a small
    worker pool runs MAX_CONCURRENT jobs at once and queues the rest (with live
    position feedback); DAILY_RUN_CAP bounds total spend; free-form input is
    turn-capped. Curated examples are the main path.

Run:   python3 webapp/server.py            # then open http://localhost:8000
Share: cloudflared tunnel --url http://localhost:8000
"""
import json
import os
import queue
import sys
import threading
import time
import traceback
from contextlib import redirect_stderr, redirect_stdout
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
PIPELINE_DIR = os.path.dirname(HERE)           # 6.11new/
sys.path.insert(0, PIPELINE_DIR)

# Import the real pipeline. Importing also seeds runtime_state's provider config
# from env (AIGOCODE_ANTHROPIC_KEY / PROVIDER / ANTHROPIC_MODEL).
from barrier_core import SYSTEMS                       # noqa: E402
from dual_agent_debate_4 import run_barrier_synthesis_v4  # noqa: E402

# ── guardrails ──────────────────────────────────────────────────────────────
TURN_CAP_CURATED = 6     # max debate turns for a built-in example
TURN_CAP_CUSTOM = 4      # tighter cap for user-supplied systems (bound token burn)
PORT = int(os.environ.get("PORT", "8000"))
RUNS_DIR = os.path.join(HERE, "_runs")
os.makedirs(RUNS_DIR, exist_ok=True)

# Shared access password. Empty → no auth (local dev). Set APP_PASSWORD before
# sharing via cloudflared so a leaked URL can't burn your GLM tokens.
APP_PASSWORD = os.environ.get("APP_PASSWORD", "")

# ── concurrency: small worker pool + FIFO queue (instead of a hard "busy") ────
# Bottleneck is local Lean compilation (CPU), not the GLM calls (network wait),
# so cap how many compile at once; the rest queue. 4 running + 6 waiting ≈ 10
# people in the system at a time.
MAX_CONCURRENT = int(os.environ.get("MAX_CONCURRENT", "4"))   # runs at once
MAX_QUEUE = int(os.environ.get("MAX_QUEUE", "6"))             # waiting cap
DAILY_RUN_CAP = int(os.environ.get("DAILY_RUN_CAP", "60"))    # total runs/day

JOBS = {}                        # job_id -> Job
_JOB_SEQ = [0]
PENDING = queue.Queue()          # Job objects waiting for a worker
WAITING = []                     # job ids still queued, FIFO (for position)
STATE_LOCK = threading.Lock()    # guards WAITING + _runs_today
_runs_today = {"date": None, "count": 0}


def _quota_take():
    """Reserve one run against today's cap. Returns True if allowed."""
    today = time.strftime("%Y-%m-%d")
    with STATE_LOCK:
        if _runs_today["date"] != today:
            _runs_today["date"] = today
            _runs_today["count"] = 0
        if _runs_today["count"] >= DAILY_RUN_CAP:
            return False
        _runs_today["count"] += 1
        return True


def _position(job_id) -> int:
    """How many jobs are ahead of this one in line (0 = next to start)."""
    with STATE_LOCK:
        return WAITING.index(job_id) if job_id in WAITING else 0


class QueueWriter:
    """File-like sink: buffers text and pushes complete lines onto a queue."""
    def __init__(self, q):
        self.q = q
        self._buf = ""

    def write(self, s):
        self._buf += s
        while "\n" in self._buf:
            line, self._buf = self._buf.split("\n", 1)
            self.q.put(("log", line))
        return len(s)

    def flush(self):
        if self._buf:
            self.q.put(("log", self._buf))
            self._buf = ""


class Job:
    def __init__(self, jid, label, system_key, system_dict, turns, do_lean):
        self.id = jid
        self.label = label
        self.system_key = system_key
        self.system_dict = system_dict
        self.turns = turns
        self.do_lean = do_lean
        self.q = queue.Queue()
        self.status = "queued"
        self.result = None
        self.error = None


def _summarize(result: dict) -> dict:
    """Trim the big result dict to a JSON-safe summary for the browser."""
    lean = result.get("lean4") or {}
    fb = result.get("final_barrier") or {}
    return {
        "solved": result.get("solved"),
        "model": result.get("model"),
        "turns_used": len(result.get("rounds", [])),
        "barrier_h": fb.get("h"),
        "refuter_verdict": result.get("refuter_verdict"),
        "lean_compile_ok": lean.get("compile_ok"),
        "lean_code": (lean.get("code") or "")[:6000],
    }


def _run_job(job: Job):
    """Execute one job to completion, streaming its log onto job.q."""
    try:
        out_dir = os.path.join(RUNS_DIR, job.id)
        w = QueueWriter(job.q)
        with redirect_stdout(w), redirect_stderr(w):
            result = run_barrier_synthesis_v4(
                system_key=job.system_key,
                system=job.system_dict,
                turns=job.turns,
                output_dir=out_dir,
                do_plot=False,        # headless; skip matplotlib
                do_lean=job.do_lean,  # the headline: LLM⇄Lean4 feedback loop
                lean_repair=2,
                use_kb=True,
                refuter_gate=True,
                delay=0.5,
            )
            w.flush()
        job.result = _summarize(result)
        job.status = "done"
        job.q.put(("done", job.result))
    except Exception as e:
        job.error = f"{type(e).__name__}: {e}\n{traceback.format_exc()}"
        job.status = "error"
        job.q.put(("error", job.error))
    finally:
        job.q.put(("eof", None))


def _pool_worker():
    """One of MAX_CONCURRENT threads: pull the next queued job and run it."""
    while True:
        job = PENDING.get()
        with STATE_LOCK:
            if job.id in WAITING:
                WAITING.remove(job.id)
        job.status = "running"
        _run_job(job)


def _validate_custom(sys_in: dict):
    """Minimal validation + defaults for a user-supplied system dict."""
    req = ["name", "state_vars", "f_expr"]
    for k in req:
        if k not in sys_in:
            raise ValueError(f"custom system missing required field '{k}'")
    sv, fx = sys_in["state_vars"], sys_in["f_expr"]
    if not isinstance(sv, list) or not isinstance(fx, list) or len(sv) != len(fx):
        raise ValueError("state_vars and f_expr must be lists of equal length")
    if len(sv) > 4:
        raise ValueError("trial limited to systems with at most 4 state variables")
    bounds = sys_in.get("X_bounds") or [[-2, 2]] * len(sv)
    sys_in.setdefault("X_bounds", [tuple(b) for b in bounds])
    sys_in.setdefault("X_domain", " × ".join(f"[{b[0]},{b[1]}]" for b in bounds))
    sys_in.setdefault("X_u_expr", sys_in.get("X_u_expr", ""))
    sys_in.setdefault("ode", "; ".join(f"d{v} = {e}" for v, e in zip(sv, fx)))
    return sys_in


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):  # quieter console
        pass

    def _send(self, code, body, ctype="application/json"):
        data = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    # ── auth ──
    def _token(self):
        from urllib.parse import parse_qs, urlparse
        return (self.headers.get("X-Access-Token")
                or (parse_qs(urlparse(self.path).query).get("token") or [""])[0])

    def _authed(self):
        return (not APP_PASSWORD) or self._token() == APP_PASSWORD

    # ── routes ──
    def do_GET(self):
        path = self.path.split("?", 1)[0]
        if path == "/" or path == "/index.html":
            with open(os.path.join(HERE, "index.html"), "rb") as f:
                return self._send(200, f.read(), "text/html; charset=utf-8")
        if path == "/api/check":   # password probe for the login gate
            return self._send(200 if self._authed() else 401,
                              json.dumps({"ok": self._authed(),
                                          "auth_required": bool(APP_PASSWORD)}))
        if not self._authed():
            return self._send(401, json.dumps({"error": "需要访问口令"}))
        if path == "/api/examples":
            ex = [{"key": k, "name": v["name"], "ode": v["ode"]}
                  for k, v in SYSTEMS.items()]
            return self._send(200, json.dumps({
                "examples": ex,
                "turn_cap_curated": TURN_CAP_CURATED,
                "turn_cap_custom": TURN_CAP_CUSTOM,
            }))
        if path == "/api/stream":
            return self._stream()
        return self._send(404, json.dumps({"error": "not found"}))

    def do_POST(self):
        path = self.path.split("?", 1)[0]
        if path != "/api/run":
            return self._send(404, json.dumps({"error": "not found"}))
        if not self._authed():
            return self._send(401, json.dumps({"error": "需要访问口令"}))
        length = int(self.headers.get("Content-Length", "0"))
        try:
            body = json.loads(self.rfile.read(length) or "{}")
        except Exception:
            return self._send(400, json.dumps({"error": "invalid JSON body"}))

        do_lean = bool(body.get("do_lean", True))
        custom = body.get("custom_system")
        try:
            if custom:
                system_dict = _validate_custom(dict(custom))
                system_key = "custom"
                cap = TURN_CAP_CUSTOM
                label = system_dict["name"]
            else:
                system_key = body.get("system_key")
                if system_key not in SYSTEMS:
                    raise ValueError(f"unknown system_key '{system_key}'")
                system_dict = None
                cap = TURN_CAP_CURATED
                label = SYSTEMS[system_key]["name"]
            turns = max(1, min(int(body.get("turns", 4)), cap))
        except Exception as e:
            return self._send(400, json.dumps({"error": str(e)}))

        # queue guard: bound how many can wait, and cap total runs/day
        with STATE_LOCK:
            waiting = len(WAITING)
        if waiting >= MAX_QUEUE:
            return self._send(429, json.dumps({
                "error": f"排队人数已满({MAX_QUEUE}),请稍后再试。"}))
        if not _quota_take():
            return self._send(429, json.dumps({
                "error": f"今日试用次数已达上限({DAILY_RUN_CAP}),请明天再来。"}))

        _JOB_SEQ[0] += 1
        jid = f"job{_JOB_SEQ[0]}_{int(time.time())}"
        job = Job(jid, label, system_key, system_dict, turns, do_lean)
        JOBS[jid] = job
        with STATE_LOCK:
            WAITING.append(jid)
        PENDING.put(job)
        return self._send(200, json.dumps(
            {"job_id": jid, "turns": turns, "label": label, "do_lean": do_lean,
             "queue_pos": _position(jid)}))

    # ── SSE stream ──
    def _stream(self):
        from urllib.parse import parse_qs, urlparse
        jid = (parse_qs(urlparse(self.path).query).get("job") or [""])[0]
        job = JOBS.get(jid)
        if not job:
            return self._send(404, json.dumps({"error": "unknown job"}))
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "keep-alive")
        self.end_headers()

        def emit(kind, payload):
            self.wfile.write(
                f"data: {json.dumps({'type': kind, 'data': payload})}\n\n"
                .encode("utf-8"))
            self.wfile.flush()

        try:
            # while queued, report live queue position (a worker hasn't picked
            # it up yet, so its log queue is silent); buffered logs replay once
            # status flips to running.
            last_pos = None
            while job.status == "queued":
                pos = _position(jid)
                if pos != last_pos:
                    emit("queued", pos)
                    last_pos = pos
                time.sleep(1.0)
            while True:
                try:
                    kind, payload = job.q.get(timeout=15)
                except queue.Empty:
                    self.wfile.write(b": keep-alive\n\n")  # heartbeat
                    self.wfile.flush()
                    continue
                if kind == "eof":
                    break
                emit(kind, payload)
        except (BrokenPipeError, ConnectionResetError):
            pass


def main():
    for _ in range(max(1, MAX_CONCURRENT)):
        threading.Thread(target=_pool_worker, daemon=True).start()
    srv = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    prov = os.environ.get("PROVIDER", "glm")
    print(f"barrier-synthesis web UI  →  http://localhost:{PORT}")
    print(f"  pipeline dir : {PIPELINE_DIR}")
    print(f"  provider     : {prov} | model "
          f"{os.environ.get('GLM_MODEL') if prov == 'glm' else os.environ.get('ANTHROPIC_MODEL', 'claude-sonnet-4-6')}")
    print(f"  guardrails   : {MAX_CONCURRENT} concurrent · queue {MAX_QUEUE} · "
          f"{DAILY_RUN_CAP} runs/day")
    print(f"  access       : {'password ON' if APP_PASSWORD else 'NO PASSWORD (set APP_PASSWORD before sharing!)'}")
    print("  share it     : cloudflared tunnel --url http://localhost:%d" % PORT)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nshutting down")


if __name__ == "__main__":
    main()
