#!/usr/bin/env bash
# share.sh — one command to put the barrier-synthesis web UI online for a small
# group, on YOUR machine (Lean uses your local mathlib build), behind a password.
#
#   GLM_API_KEY=... ./webapp/share.sh
#
# Optional env: APP_PASSWORD (else auto-generated), GLM_MODEL (default glm-4.6),
#               PORT (8000), MAX_CONCURRENT (2), DAILY_RUN_CAP (60).
set -euo pipefail
cd "$(dirname "$0")/.."                       # → 6.11new/  (pipeline root)

# 凭证来源:优先用你 shell 里已 export 的环境变量;其余由 runtime_state 自动
# 从 .secrets.env 读取(GLM_API_KEY / GLM_MODEL / PROVIDER 都在那里)。
# 这里只做一次性校验:两处都没 key 才报错。
if [ -z "${GLM_API_KEY:-}" ] && ! grep -q '^GLM_API_KEY=' .secrets.env 2>/dev/null; then
  echo "找不到 GLM_API_KEY:请在 .secrets.env 里写一行 GLM_API_KEY=xxx,或 GLM_API_KEY=xxx ./webapp/share.sh"; exit 1
fi
export PROVIDER="${PROVIDER:-glm}"            # 不覆盖你显式设的 PROVIDER
# GLM_MODEL 故意不在这里写死,交给 .secrets.env;想临时换:GLM_MODEL=glm-5.1 ./webapp/share.sh
# 仅用于横幅显示的有效型号(env 优先,否则读 .secrets.env)。
SHOW_MODEL="${GLM_MODEL:-$(grep -E '^GLM_MODEL=' .secrets.env 2>/dev/null | head -1 | cut -d= -f2- | tr -d '"'"'"' ')}"

# 端口:不指定就从 8001 往后自动找一个空闲端口,避开 8000 上的测试服务器。
free_port() {
  python3 - "$1" <<'PY'
import socket, sys
start = int(sys.argv[1])
for p in range(start, start + 50):
    s = socket.socket()
    try:
        s.bind(("0.0.0.0", p)); s.close(); print(p); break
    except OSError:
        s.close()
else:
    sys.exit("没找到空闲端口")
PY
}
export PORT="${PORT:-$(free_port 8001)}"
export MAX_CONCURRENT="${MAX_CONCURRENT:-4}"   # 同时真正跑几个(吃 CPU 的是 Lean 编译)
export DAILY_RUN_CAP="${DAILY_RUN_CAP:-60}"
export APP_PASSWORD="${APP_PASSWORD:-$(LC_ALL=C tr -dc 'a-z0-9' </dev/urandom | head -c 8)}"

# cloudflared: free, no account needed for a quick tunnel.
if ! command -v cloudflared >/dev/null 2>&1; then
  echo "⏳ 未检测到 cloudflared,正在用 Homebrew 安装…"
  brew install cloudflared
fi

# Start the web server in the background.
python3 webapp/server.py &
SRV=$!
trap 'kill $SRV 2>/dev/null || true' EXIT
sleep 2

echo
echo "──────────────────────────────────────────────────────────"
echo "  访问口令 (发给同学):  $APP_PASSWORD"
echo "  本机端口:            $PORT   (本地自测 http://localhost:$PORT;8000 上的测试服务器不受影响)"
echo "  模型:                ${SHOW_MODEL:-见 .secrets.env}   并发: $MAX_CONCURRENT   每日上限: $DAILY_RUN_CAP"
echo "  下面这条 https://xxxx.trycloudflare.com 就是公网地址 ↓"
echo "──────────────────────────────────────────────────────────"
echo

# Foreground tunnel: prints the public URL; Ctrl-C stops both it and the server.
cloudflared tunnel --url "http://localhost:${PORT}"
