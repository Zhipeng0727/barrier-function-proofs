"""max_interactive.py — 合规交互测试驱动。
我(Claude Code on Max)当 Proposer 手动提 h(x);此脚本只调用本地零-token 验证器
(barrier_core.local_verify),不发任何网络请求、不碰 Max 凭证。
每轮追加到 maxtest_logs/<system>.jsonl 作为交互记录。
"""
import sys, json, time, os
import barrier_core as b

LOGDIR = os.path.join(os.path.dirname(__file__), "maxtest_logs")
os.makedirs(LOGDIR, exist_ok=True)

def run(sysname, h_str, note=""):
    system = b.SYSTEMS[sysname]
    res = b.local_verify(system, h_str, cache={"xu_points": [], "escape_points": []})
    sym = res.get("symbolic", {})
    rec = {
        "ts": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "system": sysname, "h": h_str, "note": note,
        "passed": res["passed"],
        "cache_fails": res.get("cache_fails", []),
        "cond1_ok": sym.get("cond1_ok"), "cond2_ok": sym.get("cond2_ok"),
        "cond1_max_h_in_Xu": sym.get("cond1_max_h_in_Xu"),
        "cond1_violations": sym.get("cond1_violations"),
        "cond2_violations": sym.get("cond2_violations"),
        "cond2_viol_ratio": sym.get("cond2_viol_ratio") or sym.get("viol_ratio"),
        "trajectory_valid": res.get("trajectory", {}).get("trajectory_valid"),
    }
    with open(os.path.join(LOGDIR, f"{sysname}.jsonl"), "a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    # human-readable echo
    print(f"[{sysname}] h = {h_str}")
    print(f"  PASSED       : {res['passed']}")
    print(f"  cache_fails  : {res.get('cache_fails')}")
    print(f"  cond1_ok     : {sym.get('cond1_ok')}  (max h on X_u = {sym.get('cond1_max_h_in_Xu')}, want <0)")
    print(f"  cond1_viol   : {sym.get('cond1_violations')}")
    print(f"  cond2_ok     : {sym.get('cond2_ok')}")
    print(f"  cond2_viol   : {sym.get('cond2_violations')}")
    print(f"  traj_valid   : {res.get('trajectory', {}).get('trajectory_valid')}")
    return res["passed"]

if __name__ == "__main__":
    sysname, h_str = sys.argv[1], sys.argv[2]
    note = sys.argv[3] if len(sys.argv) > 3 else ""
    ok = run(sysname, h_str, note)
    sys.exit(0 if ok else 1)
