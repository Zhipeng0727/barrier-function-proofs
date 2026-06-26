"""max_fullflow.py — 按 run_barrier_synthesis_v4 的真实步骤跑单系统全流程。
合规:把 call_api(LLM)那一格换成"我手填的输出"(proposer JSON / Lean code),
其余每一环都调流水线的真函数:local_verify / _refuter_gate / lean_compile_check。
全程零网络、零 token、不碰 Max 凭证。日志写 maxtest_logs/fullflow_<sys>.json。
"""
import sys, json, time, os
import barrier_core as bc
from dual_agent_debate_4 import _refuter_gate
from lean_proof import lean_compile_check, _cert_family, _TEMPLATES, has_sorry

SYS = "bb_linear"
system = bc.SYSTEMS[SYS]
log = {"system": SYS, "stages": []}
def stage(name, **kw):
    rec = {"stage": name, "ts": time.strftime("%H:%M:%S"), **kw}
    log["stages"].append(rec); 
    print(f"\n=== [{name}] ==="); 
    return rec

# ── Stage 1: Proposer (我) ──────────────────────────────
proposer_out = {            # 我（替 call_api）产出的提议 JSON
    "h": "9 - x1**2 - x2**2",
    "lie_derivative": "10*x1**2 + 10*x1*x2 + 4*x2**2",
    "invariant_set": "C = {x1**2 + x2**2 <= 9}",
    "reasoning": "stable linear sys; sublevel set of |x|^2 inside radius-3 safe ball; "
                 "hdot is a PD quadratic form (matrix [[10,5],[5,4]], det=15>0).",
}
h_str = proposer_out["h"]
stage("Proposer", role="me (LLM substitute)", output=proposer_out)
print(json.dumps(proposer_out, ensure_ascii=False, indent=2))

# ── Stage 2: 本地验证 (真函数) ──────────────────────────
lv = bc.local_verify(system, h_str, {"xu_points": [], "escape_points": []})
sym = lv["symbolic"]
st = stage("local_verify", passed=lv["passed"],
           cond1_ok=sym.get("cond1_ok"), cond2_ok=sym.get("cond2_ok"),
           cond1_max_h_in_Xu=sym.get("cond1_max_h_in_Xu"),
           trajectory_valid=lv["trajectory"].get("trajectory_valid"))
print(f"passed={lv['passed']}  cond1_ok={sym.get('cond1_ok')}  cond2_ok={sym.get('cond2_ok')}  "
      f"traj={lv['trajectory'].get('trajectory_valid')}")

# ── Stage 3: Refuter gate (真函数) ─────────────────────
gated = _refuter_gate(system, h_str, lv)
stage("refuter_gate", auto_accept=gated,
      meaning="clean polynomial + local pass -> LLM Refuter skipped (token saver)")
print(f"_refuter_gate -> {gated}  ({'auto-accept, Refuter SKIPPED' if gated else 'would call LLM Refuter'})")

# 为演示，我再手动扮演一次 Refuter（即使 gate 已跳过它）
manual_refuter = {
    "verdict": "valid",
    "reasoning": "Cond1 is definitional: 9-|x|^2<0 ⇔ |x|^2>9 = X_u. "
                 "Cond2: hdot=10x1²+10x1x2+4x2², form matrix PD (det 15>0) ⇒ ≥0 ∀x, "
                 "so in particular on ∂C. No counterexample exists.",
    "flaw": None,
}
stage("Refuter(manual demo)", role="me (LLM substitute)", output=manual_refuter)
print(f"manual Refuter verdict = {manual_refuter['verdict']}")

# ── Stage 4: Lean4 writer + compile (我写码 + 真编译) ───
final = {"h": h_str, "lie_derivative": proposer_out["lie_derivative"],
         "invariant_set": proposer_out["invariant_set"]}
family = _cert_family(h_str)
print(f"cert family -> {family}  (template injected: _TEMPLATES['{family}'])")

lean_code = r'''import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Positivity

namespace BBLinear
-- System: x1' = -5 x1 - 4 x2 ,  x2' = -x1 - 2 x2
def f1 (x1 x2 : ℝ) : ℝ := -5*x1 - 4*x2
def f2 (x1 x2 : ℝ) : ℝ := -x1 - 2*x2
-- Barrier certificate h(x) = 9 - x1^2 - x2^2
def h (x1 x2 : ℝ) : ℝ := 9 - x1^2 - x2^2
-- Lie derivative  hdot = ∂h/∂x1 * f1 + ∂h/∂x2 * f2  with ∂h/∂x1=-2x1, ∂h/∂x2=-2x2
def hdot (x1 x2 : ℝ) : ℝ := (-2*x1) * f1 x1 x2 + (-2*x2) * f2 x1 x2

-- Condition 1: h < 0 on the unsafe set X_u = { x1^2 + x2^2 > 9 }
theorem cond1 (x1 x2 : ℝ) (hu : x1^2 + x2^2 > 9) : h x1 x2 < 0 := by
  unfold h; nlinarith [hu]

-- Condition 2 (Nagumo): hdot ≥ 0 on ∂C = { h = 0 }
-- (the quadratic form 10 x1^2 + 10 x1 x2 + 4 x2^2 is positive semidefinite)
theorem cond2 (x1 x2 : ℝ) : hdot x1 x2 ≥ 0 := by
  unfold hdot f1 f2
  nlinarith [sq_nonneg (2*x1 + x2), sq_nonneg x2, sq_nonneg (x1 + x2), sq_nonneg x1]
end BBLinear
'''
t0 = time.time()
ok, diag = lean_compile_check(lean_code, tag="fullflow_bb_linear")
el = round(time.time() - t0, 1)
stage("lean_compile_check", attempt=1, compile_ok=ok, elapsed_s=el,
      sorry_free=(not has_sorry(diag or "")), diagnostic=(diag or "")[:800])
print(f"compile_ok={ok}  ({el}s)  sorry_free={not has_sorry(diag or '')}")
if diag: print("--- diagnostics ---\n" + diag[:800])

log["solved"] = bool(lv["passed"])
log["lean_compile_ok"] = ok
os.makedirs("maxtest_logs", exist_ok=True)
with open("maxtest_logs/fullflow_bb_linear.json", "w", encoding="utf-8") as f:
    json.dump(log, f, ensure_ascii=False, indent=2)
print("\n[saved] maxtest_logs/fullflow_bb_linear.json")
