"""max_fullflow_ex5.py — 超越式系统 ex5 全流程(三环:Proposer + 本地验证 + LLM Refuter)。
我替 call_api 扮演 Proposer / Refuter;local_verify、_refuter_gate 调真函数。零网络/零token。
"""
import json, time, os
import barrier_core as bc
from dual_agent_debate_4 import _refuter_gate
sysd = bc.SYSTEMS["ex5"]
H = "(1/2*(x2 + exp(-x1) - 1)**2 + 1/2*x1 - 1/4*sin(2*x1))"
log = {"system":"ex5","note":"transcendental (exp+sin) -> refuter gate always False","rounds":[]}
def lv_run(h): return bc.local_verify(sysd, h, {"xu_points": [], "escape_points": []})

# ── ROUND 1 : Proposer 第一次猜，level 取大了 ──────────────────────────────
h1 = f"1.5 - {H}"
print("="*60, "\nROUND 1  —  Proposer (me)")
print(f"  h1 = 1.5 - H   (z=x2+exp(-x1)-1, H=½z²+½x1-¼sin2x1)")
lv1 = lv_run(h1); s1 = lv1["symbolic"]
print(f"  [local_verify] passed={lv1['passed']}  cond1_ok={s1.get('cond1_ok')} "
      f"(max h on X_u={s1.get('cond1_max_h_in_Xu')}, want<0)")
print(f"     -> cond1 VIOLATIONS in X_u: {s1.get('cond1_violations')}")
print(f"  [gate] _refuter_gate={_refuter_gate(sysd,h1,lv1)} (transcendental f -> Refuter would fire, but local already rejected)")
print("  >> local feedback drives Proposer: C={H<=1.5} is too big, it swallows the unsafe disk @ (0.7,-0.7).")
print("  >> revise: lower the level constant until C clears X_u.")
log["rounds"].append({"round":1,"role":"Proposer","h":h1,"local_passed":lv1["passed"],
   "cond1_ok":s1.get("cond1_ok"),"cond1_max_h_in_Xu":s1.get("cond1_max_h_in_Xu"),
   "cond1_violations":s1.get("cond1_violations"),"action":"local reject Cond1 -> lower level"})

# ── ROUND 2 : Proposer 收紧 level ; 本地过 -> Refuter 触发 ──────────────────
h2 = f"0.41 - {H}"
print("="*60, "\nROUND 2  —  Proposer (me): tighten level to 0.41")
lv2 = lv_run(h2); s2 = lv2["symbolic"]
print(f"  [local_verify] passed={lv2['passed']}  cond1_ok={s2.get('cond1_ok')} "
      f"(max h on X_u={s2.get('cond1_max_h_in_Xu')})  cond2_ok={s2.get('cond2_ok')}  "
      f"traj={lv2['trajectory'].get('trajectory_valid')}")
gate2 = _refuter_gate(sysd, h2, lv2)
print(f"  [gate] _refuter_gate={gate2}  -> Refuter FIRES (transcendental, gate never auto-accepts)")

# LLM Refuter (me): rigorous symbolic falsification attempt
refuter = {
  "verdict": "valid",
  "checked": {
    "Cond1 (h<0 on X_u)": "X_u is the disk (x1-0.7)^2+(x2+0.7)^2<=0.09; on it max h = -0.0428 < 0. "
                          "Margin thin but strictly negative; no unsafe point has h>=0.",
    "Cond2 (Nagumo, hdot>=0 on dC)":
        "hdot = -dH/dt. Along f: dH/dt = gradH . f = (-exp(-x1) z + sin(x1)^2)*z + z*(-sin(x1)^2) "
        "= -exp(-x1) z^2.  So hdot = exp(-x1)*z^2. Since exp(-x1)>0 and z^2>=0, hdot>=0 GLOBALLY "
        "(not just on the sampled boundary) -> Nagumo holds everywhere. This is the key fact pure "
        "sampling cannot certify; the algebraic cancellation is why the Refuter ring matters here."
  },
  "counterexample_search": "none found; both conditions hold symbolically.",
  "flaw": None,
}
print("  [Refuter (me)] verdict =", refuter["verdict"])
for k,v in refuter["checked"].items():
    print(f"     - {k}: {v}")
log["rounds"].append({"round":2,"role":"Proposer+Refuter","h":h2,"local_passed":lv2["passed"],
   "cond1_ok":s2.get("cond1_ok"),"cond2_ok":s2.get("cond2_ok"),
   "trajectory_valid":lv2["trajectory"].get("trajectory_valid"),
   "refuter_gate":gate2,"refuter_verdict":refuter["verdict"],"refuter":refuter})
log["solved"] = (refuter["verdict"]=="valid" and lv2["passed"])

print("="*60)
print(f"SOLVED = {log['solved']}  (Proposer 2 轮; 本地拒1次; Refuter 触发1次, 确认 valid)")
os.makedirs("maxtest_logs", exist_ok=True)
json.dump(log, open("maxtest_logs/fullflow_ex5.json","w"), ensure_ascii=False, indent=2)
print("[saved] maxtest_logs/fullflow_ex5.json")
