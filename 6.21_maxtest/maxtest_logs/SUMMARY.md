# Max 订阅交互测试 — 记录

**日期**: 2026-06-21
**方式(合规)**: 由 Claude Code(跑在 Max 订阅上)在交互会话里**手动**当 Proposer 提候选 barrier;
仅调用本地零-token 验证器 `barrier_core.local_verify`(symbolic Cond1/Cond2 + trajectory)。
**未**使用任何自动化脚本调用 Max 凭证、**未**发任何 LLM 网络请求 → 不触及订阅自动化禁令。
逐轮原始记录见 `darboux.jsonl` / `bb_linear.jsonl`。

## 系统 1: darboux(连续 barrier)— 3 轮收敛
- X_u = {x1 + x2² ≤ 0};条件 Cond1: h<0 on X_u;Cond2: ḣ≥0 on ∂C={h=0}。
- **r1** `h=-(x1+x2²)` → Cond1 FAIL(符号反,max h on X_u=+1.99)。
- **r2** `h=x1+x2²` → Cond1 PASS,Cond2 FAIL(x2<0 边界处 ḣ<0;非 Darboux 多项式)。
- **r3** `h=-2x1²/3+5x1/6+x2²-5/12` → **PASS**。
  - 该 h 是系统的 Darboux 多项式,cofactor c=-2x2,即 ḣ=c·h ⇒ 边界上 ḣ=0≥0,Cond2 自动满足。
  - (用 sympy 解 D p = c·p 找到,见会话。)

## 系统 2: bb_linear(连续 barrier,稳定线性系统)— 1 轮
- f = (-5x1-4x2, -x1-2x2);X_u = {x1²+x2² > 9}。
- **r1** `h=9-x1²-x2²` → **PASS**(Cond1/Cond2/trajectory 全过)。
  - ḣ=10x1²+10x1x2+4x2²,矩阵 [[10,5],[5,4]] 正定(det=15) ⇒ 全域 ḣ≥0;h 恰在 X_u 上<0。

## 结论
- 本地验证回路(Cond1/Cond2 反例点反馈 → 修正)工作正常,反馈信息足以驱动收敛。
- darboux 体现"需要结构(Darboux 多项式)"的难例;bb_linear 体现可一步推出的易例。
- 这是合规的小规模交互验证;**批量跑 core200 仍需走 API(付费),不能用 Max。**
