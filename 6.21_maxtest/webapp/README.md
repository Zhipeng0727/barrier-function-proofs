# Barrier 合成 · 内部试用 Web UI

让一个小组通过浏览器试用 barrier/Lyapunov 证书合成流水线(含 LLM⇄Lean4 编译反馈闭环)。
**纯 Python 标准库,无需 pip install。**

## 算力到底在哪(重要)

- **LLM(GLM)在智谱云端**:`runtime_state.py` 的 glm provider 指向 `open.bigmodel.cn`,
  用你的 `GLM_API_KEY` 计费。同学试用 **烧的是你的 GLM token(钱),不是你的 CPU/GPU**。
- **Lean 4 证明编译在你本机**:mathlib 完整 build 在 `~/lean`,这才是绑在你机器上、
  别人没有的资源 → 只要开着 `do_lean`,服务就必须跑在装了 mathlib build 的机器上。
- **API key 留在服务端**(读环境变量),同学只拿到 URL + 口令,看不到 key。
- **长耗时作业** → 后台 worker 池 + SSE,把 `print()` 日志实时推到浏览器。

## 护栏(都可用环境变量调)

| 变量 | 默认 | 作用 |
|---|---|---|
| `APP_PASSWORD` | 空 | 访问口令。**分享前必设**,否则链接泄露=谁都能烧你 token |
| `MAX_CONCURRENT` | 4 | 同时真正运行的作业数(吃 CPU 的是 Lean 编译);其余自动排队(显示"前面还有几个") |
| `MAX_QUEUE` | 6 | 排队上限,满了返回 429。4 跑 + 6 等 ≈ 同时 10 人 |
| `DAILY_RUN_CAP` | 60 | 每日总运行次数上限,防口令泄露被刷爆 |
| `TURN_CAP_CURATED` / `TURN_CAP_CUSTOM` | 6 / 4 | debate 轮数上限(控 token) |

每次运行的输出(Lean 文件、日志)写到 `webapp/_runs/<job_id>/`。

## 最快上线:一键脚本

```bash
GLM_API_KEY=你的key GLM_MODEL=glm-5.1 ./webapp/share.sh
```

脚本会:设默认 provider=glm、自动生成访问口令(终端打印)、**自动从 8001 起找一个空闲端口**
(避开 8000 上可能在跑的测试服务器)、需要时 `brew install cloudflared`、起服务、开隧道,
并打印 `https://xxxx.trycloudflare.com` 公网地址。把 **URL + 口令** 发给同学即可。
想固定端口就加 `PORT=8005`。你的电脑必须开机联网;关机即下线。

## 或手动启动

```bash
cd /Users/zhipeng/Desktop/paper4/6.11new
export GLM_API_KEY="..." GLM_MODEL="glm-5.1"   # 模型按需
export APP_PASSWORD="给同学的口令"
python3 webapp/server.py                        # → http://localhost:8000
cloudflared tunnel --url http://localhost:8000  # 另开一个终端
```

本机自测:浏览器开 `http://localhost:8000`,输入口令,选一个内置系统点「运行合成」。

## 端点

| 方法 | 路径 | 说明 |
|---|---|---|
| GET | `/` | UI 页面 |
| GET | `/api/check` | 口令校验(登录框用),不需要口令也可访问 |
| GET | `/api/examples` | 内置系统列表 + turns 上限(需口令) |
| POST | `/api/run` | 入队一次合成,返回 `{job_id, queue_pos}`(队列/每日满返回 429) |
| GET | `/api/stream?job=ID&token=口令` | SSE:先报排队位置,再实时日志,以 `done`/`error` 收尾 |

## ⚠️ 安全:上线/分享仓库前必做

`runtime_state.py` 里把 API key 作为**硬编码 fallback** 写死了(`AIGOCODE_ANTHROPIC_KEY`、
`AIGOCODE_OPENAI_KEY`),且已进入 git 初始提交。隧道分享给小组**只暴露网页、不暴露 key**,是安全的;
但**只要你把这个 git 仓库 push 到 GitHub / 发给别人,key 就泄露**。push 前务必:

1. 轮换(吊销重发)这两个 key;
2. 把 fallback 改成 `os.environ["AIGOCODE_ANTHROPIC_KEY"]`(无默认值),key 只走环境变量;
3. 清理 git 历史里的明文(`git filter-repo` 或重新 init)。
