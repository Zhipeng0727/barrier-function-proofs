# Barrier / Lyapunov 证书合成流水线

LLM 多智能体（Proposer 提议 / Refuter 证伪）+ 本地数值验证的证书合成流水线。
模型 A/B 对比用 `--provider` 在 anthropic(Claude) / openai(GPT) 间切换。

支持四种任务模式（2026-06-12 v5 扩展，由 system dict 的 `task_type`/`discrete` 字段分派）：

| 任务 | 条件 |
|---|---|
| barrier · 连续 | Cond1：`h<0` on X_u；Cond2：边界 `∂C` 上 `ḣ≥0`（Nagumo） |
| barrier · 离散 | Cond1 同上；Cond2：整个 C 上一步不变 `h(f(x))≥0`（离散轨迹会跳，不能只查边界） |
| lyapunov · 连续 | `V(x*)=0`、`V>0 (x≠x*)`、`V̇≤0`（psd_ok 条目放宽为 V≥0：守恒量/共识子空间） |
| lyapunov · 离散 | 同上,递减条件换 `V(f(x))-V(x)≤0` |

另有 **verify-only 模式**（`--verify-only`）：跳过 Proposer，直接本地验证数据集自带的
ground-truth 证书并走 Lean4 形式化——把数据集条目从 prove-ready 推到 lean-verified，
并把「合成能力」与「形式验证能力」两个研究问题分开。

## 代码结构

2026-06-11 重组：原来的 `dual_agent_debate_3/4.py` 两个大文件按职责拆成 4 个模块，
import 严格向下分层、无环：

```
runtime_state.py        ← DAG 根，不依赖任何内部模块
   ↑
barrier_core.py         → runtime_state
   ↑
lean_proof.py           → runtime_state, barrier_core
   ↑
dual_agent_debate_4.py  → runtime_state, barrier_core, lean_proof   （入口）
   ↑
run_benchmark.py        → dual_agent_debate_4                        （批量评测）
```

| 文件 | 职责 | 主要内容 |
|---|---|---|
| **`runtime_state.py`** | 运行时状态 + LLM 传输（唯一可变状态源） | `API_CONFIG`（单一可变 dict，原地改不 rebind）、`PROVIDER`/`PROVIDERS`、`TOKENS` token 累加器、`select_provider`/`active_provider`/`reset_tokens`、`call_api`（唯一网络出口，支持 Anthropic Messages + OpenAI Responses 两种协议、流式解析、重试）、`HAS_SYMPY`/`HAS_SCIPY` 依赖守卫、`EFFORT_LADDER`/`LEAN_PROJECT` 等常量 |
| **`barrier_core.py`** | 无状态数学/领域代码（无网络、无可变全局） | `SYSTEMS` 内置系统目录、`proposer_system`/`refuter_system`/`lean4_system` 三个提示词、`_parse_B_expr`/`_eval_Xu`/`parse_json_response` 解析、`verify_symbolic`（符号 Cond1/Cond2，Cond2 用「违反比例+深度」判据）、`verify_trajectory`（scipy 轨迹）、`precheck_cache`/`harvest_cache`/`nontrivial_C_check`、`local_verify`（本地验证总成）、`plot_barrier` 可视化 |
| **`lean_proof.py`** | Lean 4 形式化（独立可选阶段） | `extract_lean_code`、`lean_compile_check`（`lake env lean` 编译）、`generate_lean_proof`（生成→编译→带诊断修复回环） |
| **`dual_agent_debate_4.py`** | 编排 + CLI 入口 | `build_proposer_msg`（每轮拼装 Proposer 消息）、`run_barrier_synthesis_v4`（主合成循环）、`main`（命令行）。并再导出 `run_benchmark.py` 需要的 5 个名字 |
| `dataset_loader.py` | 外部数据集 → `SYSTEMS` 格式 | jsonl（dynamics 可直接解析）本地转换；koopman LaTeX 版调 `call_api` 转换一次并缓存到 `<dataset>.converted.json` |
| `knowledge_base.py` | 已解案例知识库（`barrier_kb.json`） | 按维度/系统类别关键词检索 top-k few-shot 注入 Proposer；成功案例自动入库 |
| `run_benchmark.py` | 批量评测 | 每条记录 solved/轮数/refuter 调用/token/耗时，增量写 `benchmark_results/<run>/{summary.csv,summary.json,run.log}` |

> 改任意一项时落点很清晰：**调提示词** → `barrier_core` 的三个 `*_system`；**调本地验证判据** → `barrier_core.verify_symbolic`/`local_verify`；**调 API/provider/重试** → `runtime_state`；**调主循环/停止条件** → `dual_agent_debate_4.run_barrier_synthesis_v4`；**调 Lean** → `lean_proof`。

## 运行流程（每个系统）

```
Proposer 提议 h(x)
   → 反例缓存预检 + 本地验证（symbolic + trajectory，0 token）
   → 仅当本地通过 → LLM Refuter 严格证伪
   → verdict=valid 即停；否则把紧凑批评喂回 Proposer，至多 N 轮
   → （可选）对最终 barrier 生成 Lean4 证明并编译
```

Refuter 无状态（不积累历史）；Proposer 每轮只收到「失败尝试摘要 + 反例点列表 + 最近批评」；
reasoning effort 走 `EFFORT_LADDER`，失败一轮升一级。

## 用法

```bash
# 单个内置系统（darboux/ex5/duffing/vanderpol/lorenz/coupled/bb_linear/bb_trig）
python3 dual_agent_debate_4.py --system darboux --turns 5

# 数据集单条
python3 dual_agent_debate_4.py --dataset /Users/zhipeng/lean/data/invariant_dataset.jsonl --entry-id B2-001

# 选后端（A/B 对比）：anthropic=Claude，openai=GPT
python3 dual_agent_debate_4.py --system darboux --provider anthropic

# 批量评测（Lean 默认关，加 --lean 打开）
python3 run_benchmark.py --dataset /Users/zhipeng/lean/data/invariant_dataset.jsonl --limit 10
python3 run_benchmark.py --dataset /Users/zhipeng/lean/data/koopman_nopoly_extension.json --limit 5 --provider openai --name codex_koopman_5
```

常用开关（`dual_agent_debate_4.py`）：`--provider {anthropic,openai}` / `--model 覆盖模型` /
`--turns N` / `--no-kb 关知识库` / `--no-lean 跳过 Lean` / `--no-plot` / `--lean-repair N`。

`run_benchmark.py` 额外有：`--dataset`(必填) / `--limit` / `--start` / `--name 运行名` /
`--lean`(批量默认关 Lean，此开关打开)。`--provider` 默认 `openai`。

## 提供商与环境变量

`PROVIDERS` 是 **A/B 选择器，不是故障切换**：两个后端都走同一个 aigocode 中转，只是端点/协议/模型不同。
`call_api` 出错时只重试**当前**后端、不会自动切换。

| provider | 端点 | 协议 | 默认模型 |
|---|---|---|---|
| `anthropic` | `api.aigocode.app/v1/messages` | Anthropic Messages | `claude-sonnet-4-6` |
| `openai` | `api.aigocode.app/v1/responses` | OpenAI Responses | `gpt-5.5` |

环境变量：
- `PROVIDER`（默认 `anthropic`；`run_benchmark.py` 的 `--provider` 默认 `openai`）
- `AIGOCODE_ANTHROPIC_KEY` / `AIGOCODE_OPENAI_KEY`（各后端密钥；代码内有默认值，建议用环境变量覆盖）
- `ANTHROPIC_MODEL` / `OPENAI_MODEL`（覆盖各后端默认模型）
- `OPENAI_REASONING_EFFORT`（设了就固定 effort，不走阶梯）
- `API_TIMEOUT_MS`（请求超时毫秒，默认 120000）

## 数据集现状

- **`../data/lean4_core200_diverse_manifest_v5.json`（主数据集，2026-06-12）**：200 条
  （77 Lyapunov + 123 barrier；27 离散；7 条参数化 ∀n 条目；每条带 ground-truth 证书与
  `verif_cond_class` 标注）。loader 本地可解析 ~55 条（含全部 `machine` 字段条目），
  其余在首次跑 benchmark 时 LLM 转换并缓存到 `<dataset>.converted.json`；
  hybrid/switched 条目跳过并记录原因。由 `../data/build_v5.py` 从 v4 重建，
  浏览页 `../data/lean4_dataset_diverse_v5.html`。
- `invariant_dataset.jsonl`（旧）：200 条中 77 条可直接跑 barrier 任务；跳过原因记录在 benchmark summary 里
- `koopman_nopoly_extension.json`：47 条 LaTeX 描述，首次跑 benchmark 时 LLM 自动转换并缓存

## v5 新开关

- `dual_agent_debate_4.py` / `run_benchmark.py`：`--verify-only`（验证 ground-truth 证书 + Lean）、
  `--no-refuter-gate`（关闭多项式快路）。`run_benchmark.py` 另有 `--task {barrier,lyapunov}` 过滤。
- **Refuter 门控（默认开）**：候选证书与动力学均为多项式、且本地验证零违例时跳过 LLM Refuter
  （多项式情形采样可靠性高，Refuter 增益小——省 token 的主开关）；超越函数证书一律走 Refuter。
- Lean 生成按证书族注入骨架模板（log / trig / exp-双曲 / KL-熵 / min-max 分段 / 多项式),
  见 `lean_proof.py` 的 `_TEMPLATES`。

## Lean 环境注意

`import Mathlib` 全量导入会因 `/Users/zhipeng/lean/.lake/packages` 里 Aesop 未构建而失败，
Lean prompt 已约束模型只用具体模块导入。如需修复全量导入，在 `/Users/zhipeng/lean` 下跑
`lake exe cache get && lake build`。

## 建议的迭代路径

1. 先在 jsonl 的 77 条上跑基线（`--limit 20` 起步），看 solved 率、平均轮数、token 分布
2. 对失败条目分类：数值性失败（条件真不满足）vs 论证性失败（h 对但 Refuter 不通过）
3. 论证性失败多 → 充实知识库（`barrier_kb.json` 可手动加不等式技巧条目）；
   数值性失败多 → 考虑接入 SMT（dReal/Z3，`/Users/zhipeng/lean/SMT` 已有脚本）做精确反例
