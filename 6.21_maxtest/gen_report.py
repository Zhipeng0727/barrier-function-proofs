# -*- coding: utf-8 -*-
"""生成单文件 HTML 报告:agent 架构(论文级 SVG 结构图) + 结构性问题 + core200 v5 数据集分布。"""
import json, html, os
from collections import Counter

DATE = "2026-06-21"
MAN = "/Users/zhipeng/Desktop/paper4/data/lean4_core200_diverse_manifest_v5.json"
d = json.load(open(MAN)); E = d["core200"]; N = len(E)

# ──────────────────────────────────────────────────────────────
#  SVG 架构图  ——  沿用既有 house style(参见 2026年6月15日 agent 工作总结)
#  约定: viewBox 820 宽 · rx=7 细描边 · 浅底+同色描边 · .st/.ss 双层文字
#        单 chevron 箭头(#888) · 全宽 stage 条 + chip 池 · soundness 标在块上
# ──────────────────────────────────────────────────────────────
# (fill, stroke, title_color, sub_color)
KIND = dict(
    stage=("#eef3f8","#3a6ea5","#1a1a1a","#555"),   # LLM / 处理阶段(蓝)
    sound=("#eef6f0","#2e7d52","#1f5c3c","#2e7d52"), # 确定性/sound(绿)
    dec  =("#fbf4e6","#9a6a00","#7a5400","#9a6a00"), # 决策门(琥珀)
    unsnd=("#fbf4e6","#9a6a00","#7a5400","#9a6a00"), # 不 sound 终态(琥珀)
    risk =("#f7ecec","#a23b3b","#7c2b2b","#a23b3b"), # 风险终态(红)
    lean =("#f3f0f7","#7a5fa3","#4a3670","#7a5fa3"), # Lean 后置(淡紫)
    io   =("#f0f0ee","#bbbbbb","#1a1a1a","#555"),    # 数据/IO(灰)
)

def _st(x,y,t,col="#1a1a1a",anchor="start",sz=13):
    return f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-size="{sz}" font-weight="600" fill="{col}">{html.escape(t)}</text>'
def _ss(x,y,t,col="#555",anchor="start",sz=11):
    return f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-size="{sz}" fill="{col}">{html.escape(t)}</text>'

def bar(x,y,w,h,title,sub,kind,dash=False,badge=None):
    fill,stroke,tc,sc = KIND[kind]
    da=' stroke-dasharray="5 4"' if dash else ''
    s=f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="7" fill="{fill}" stroke="{stroke}"{da}/>'
    if sub:
        s+=_st(x+18,y+h/2-2,title,tc)+_ss(x+18,y+h/2+13,sub,sc)
    else:
        s+=_st(x+18,y+h/2+4,title,tc)
    if badge:
        bw=30; bx=x+w-bw-12; by=y+h/2-9
        s+=(f'<rect x="{bx}" y="{by}" width="{bw}" height="18" rx="4" fill="{stroke}"/>'
            f'<text x="{bx+bw/2}" y="{by+13}" text-anchor="middle" font-size="11" font-weight="700" fill="#fff">{badge}</text>')
    return s

def pill(cx,y,w,h,title,sub=None,kind="io"):
    fill,stroke,tc,sc=KIND[kind]; x=cx-w/2
    s=f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="7" fill="{fill}" stroke="{stroke}"/>'
    if sub: s+=_st(cx,y+h/2-1,title,tc,"middle")+_ss(cx,y+h/2+13,sub,sc,"middle")
    else:   s+=_st(cx,y+h/2+4,title,tc,"middle")
    return s

def chip(x,y,w,h,lines,kind):
    fill,stroke,tc,sc=KIND[kind]; cx=x+w/2
    s=f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="7" fill="{fill}" stroke="{stroke}"/>'
    s+=_st(cx,y+20,lines[0],tc,"middle")
    for i,t in enumerate(lines[1:]):
        s+=_ss(cx,y+38+i*14,t,sc,"middle")
    return s

def ln(x1,y1,x2,y2,label=None,lx=None,ly=None,anchor="start",col="#888"):
    s=f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{col}" stroke-width="1.5" marker-end="url(#ar)"/>'
    if label: s+=_ss(lx if lx is not None else (x1+x2)/2, ly if ly is not None else (y1+y2)/2, label, "#555", anchor)
    return s
def elbow(pts,label=None,lx=None,ly=None,col="#888",dash=False):
    da=' stroke-dasharray="5 4"' if dash else ''
    p="M "+" L ".join(f"{a} {b}" for a,b in pts)
    s=f'<path d="{p}" fill="none" stroke="{col}" stroke-width="1.5" marker-end="url(#ar)"{da}/>'
    if label: s+=_ss(lx,ly,label,"#555")
    return s

def build_svg():
    g=['<svg viewBox="0 0 820 560" xmlns="http://www.w3.org/2000/svg" font-family="-apple-system,PingFang SC,Microsoft YaHei,sans-serif" style="width:100%;height:auto">']
    g.append('<defs><marker id="ar" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
             '<path d="M2 1L8 5L2 9" fill="none" stroke="#888" stroke-width="1.5" stroke-linecap="round"/></marker></defs>')
    X,W,CX=150,520,410
    # input
    g.append(pill(CX,14,300,32,"输入：动力系统 + _task_framework（4 类：barrier/lyapunov × 连续/离散）"))
    g.append(ln(CX,46,CX,60))
    # ① Proposer
    g.append(bar(X,62,W,40,"① Proposer (LLM)","→ h(x), ḣ, invariant set C ｜ KB few-shot + 反例点 + 上轮 critique","stage"))
    g.append(ln(CX,102,CX,116))
    # ② Local verify (sound? 仅数值)
    g.append(bar(X,118,W,46,"② 本地验证 · 0-token 确定性","Cond1: h<0 on Xu ｜ Cond2: ḣ≥0 (band+CBF) ｜ trajectory ｜ ⟂ discrete/lyapunov","sound"))
    g.append(ln(CX,164,CX,178,"PASS",CX+8,174))
    # ③ gate (唯一决策点)
    g.append(bar(X,180,W,44,"③ refuter_gate（唯一门控）","clean poly ？  YES → 自动接受(跳过验证)   NO → LLM Refuter","dec"))
    g.append(ln(CX,224,CX,242,"NO",CX+8,237))
    # ④ Refuter
    g.append(bar(X,244,W,40,"④ Refuter (LLM · 无状态证伪门)","valid 直接置 solved（非 sound）；invalid → critique 回灌","stage"))
    g.append(ln(CX,284,CX,300))
    # solved 终态池(按证据等级)
    g.append('<rect x="40" y="302" width="740" height="92" rx="9" fill="#fbfbfa" stroke="#ddd"/>')
    g.append(_ss(54,320,"solved 终态（按证据等级标注 —— 只有 L3 机器可检）","#555"))
    g.append(chip(70,326,210,58,["auto-accept (clean poly)","L0 · 仅采样","不 sound"],"unsnd"))
    g.append(chip(305,326,210,58,["Refuter valid","L1 · LLM 认可","不 sound"],"dec"))
    g.append(chip(540,326,210,58,["network-err → solved","L0 · local-only ⚠","验证失败却置位"],"risk"))
    # gate YES → auto-accept chip ; refuter valid → mid ; refuter network → right
    g.append(elbow([(200,224),(175,326)],col="#9a6a00"))
    g.append(_ss(206,300,"YES","#9a6a00"))
    g.append(ln(CX,300,410,326))
    g.append(elbow([(640,284),(645,326)],col="#a23b3b"))
    g.append(_ss(650,300,"network-err","#a23b3b"))
    # pool → Lean
    g.append(ln(CX,394,CX,410))
    g.append(bar(X,412,W,46,"⑤ Lean 形式化（后置 · 可选）","lean_compile_check 编译+无sorry → repair；失败不回灌 solved；桥 axiom 化","lean",dash=True,badge="L3"))
    g.append(ln(CX,458,CX,474))
    g.append(pill(CX,476,360,32,"AgentResult：solved · verify_level · cert · lean_ok"))
    # 反馈回路(左侧)：local FAIL / refuter invalid → Proposer
    fb="#a23b3b"
    g.append(f'<path d="M150 141 L70 141" fill="none" stroke="{fb}" stroke-width="1.4" stroke-dasharray="5 4"/>')
    g.append(f'<path d="M150 264 L70 264" fill="none" stroke="{fb}" stroke-width="1.4" stroke-dasharray="5 4"/>')
    g.append(f'<path d="M70 264 L70 82 L150 82" fill="none" stroke="{fb}" stroke-width="1.4" stroke-dasharray="5 4" marker-end="url(#ar)"/>')
    g.append(_ss(78,135,"local FAIL：反例点",fb))
    g.append(_ss(78,258,"invalid：critique",fb))
    g.append(_ss(76,74,"harvest cex + critique · effort++",fb))
    # 图例
    lx,ly2=60,540
    for name,k in [("处理阶段(LLM)","stage"),("确定性/0-token","sound"),("决策门","dec"),
                   ("不 sound 终态","unsnd"),("风险终态","risk"),("Lean 后置(L3)","lean")]:
        f,s,_,_=KIND[k]
        g.append(f'<rect x="{lx}" y="{ly2-10}" width="14" height="14" rx="3" fill="{f}" stroke="{s}"/>')
        g.append(_ss(lx+20,ly2+1,name,"#444")); lx+=28+len(name)*12.2
    g.append('</svg>')
    return "".join(g)

ARCH_SVG = build_svg()

# ──────────────────────────────────────────────────────────────
#  数据集分布
# ──────────────────────────────────────────────────────────────
def cnt(key):
    return Counter((e.get(key) if e.get(key) not in ("",None) else "(blank)") for e in E)

def bars(counter, total=N, top=None, order=None):
    items = counter.most_common(top) if order is None else [(k,counter.get(k,0)) for k in order]
    mx = max(v for _,v in items) or 1
    rows=""
    for k,v in items:
        pct=100*v/total; w=100*v/mx
        rows+=(f'<div class="row"><span class="lbl">{html.escape(str(k))}</span>'
               f'<span class="barwrap"><span class="bar" style="width:{w:.1f}%"></span></span>'
               f'<span class="num">{v}<small>{pct:.0f}%</small></span></div>')
    return rows

task_fam=Counter(("Barrier (B)" if e["group"].startswith("B") else "Lyapunov (L)") for e in E)
task=cnt("task"); vcc=cnt("verif_cond_class"); poly=cnt("verif_cond_poly")
time_d=cnt("time_domain"); src=cnt("source_kind")
ctrl=Counter(("controlled" if (e.get("controller") or "").strip() else "autonomous") for e in E)
def dimb(n):
    n=int(n); return {1:"1D",2:"2D",3:"3D"}.get(n,"4–5D" if n<=5 else "6–8D" if n<=8 else "≥9D")
dim=Counter(dimb(e["dim"]) for e in E)
tt=Counter((("B" if e["group"].startswith("B") else "L"), e["time_domain"]) for e in E)
tt_rows="".join(f'<tr><td>{"Barrier" if k[0]=="B" else "Lyapunov"}</td><td>{html.escape(k[1])}</td>'
                f'<td class="r">{v}</td></tr>' for k,v in sorted(tt.items(),key=lambda x:-x[1]))

PROBLEMS=[
 ("red","🔴 1. Refuter gate 方向反了(健全性)","干净多项式——唯一能 sound 判定的一类(SOS / Positivstellensatz / nlinarith / z3)——被 gate <b>自动接受、跳过一切检查</b>;超越式反而进 LLM。最容易严格验证的情形得到的验证最少。应改成<b>路由到 sound 后端</b>而非跳过。"),
 ("red","🔴 2. 用 LLM 当验收 oracle 不 sound","非 poly 路径里 <code>refutation.verdict==\"valid\"</code> 直接置 solved。LLM Refuter 作为<b>证伪器</b>有价值,但它的 \"valid\" 判定不该单独让 solved 成立——会幻觉式认可。两个不 sound 的合取仍不 sound。"),
 ("red","🔴 3. 网络故障被升级成成功","<code>except RuntimeError</code> 路径:Refuter API 不可达 → 照样 <code>solved=True</code>(\"local checks only\")。验证步骤<b>失败</b>反而产出成功。至少应是独立状态,benchmark 不得计入。"),
 ("orange","🟠 4. cond2 的 band+CBF 松弛是好过滤、坏终判","在 0≤h&lt;ε band 采样,对 C∈{0,1,2,5,10,25,50} 试 ḣ+C·h≥−noise,任一过且\"违反&lt;1%或不深\"即过。会放过小测度真泄漏;且把被认证性质从 Nagumo 悄悄换成 exponential-CBF,solved 含义未记录。"),
 ("orange","🟠 5. Lean 那条 sound 路也有洞","生成证明用 <code>axiom nagumo_barrier_invariance</code>,微积分桥被<b>公理化</b>;且 lean_compile_check 只查\"编译+无sorry\",<b>不查定理陈述是否真是该类型条件</b>。不是端到端形式验证。"),
 ("yellow","🟡 6. 收敛:Refuter 无状态 + 紧凑 critique → 可能震荡","反例缓存只挡 Cond1 重复,挡不住 Cond2/Refuter-flaw 重复提议。唯一防卡死是 effort ladder,无\"禁止重提已驳回证书\"去重。"),
 ("yellow","🟡 7. 没区分 Refuter 真 bug vs 幻觉 bug","误判(把对的判 invalid)让 Proposer 追不存在的 bug,白烧轮数。无交叉校验(如把声称的反例丢回 local_verify 确认)。"),
 ("green","🟢 8. 全局可变状态挡并行","TOKENS / API_CONFIG 进程级可变 dict;core200 批量并行会 race,限制吞吐。"),
]
prob_html="".join(f'<div class="prob {c}"><div class="ph">{html.escape(t)}</div><div class="pb">{b}</div></div>' for c,t,b in PROBLEMS)
LEVELS='''<table class="lv"><tr><th>等级</th><th>含义</th><th>当前覆盖</th></tr>
<tr><td>L0</td><td>仅数值采样</td><td>poly gate 自动接受 / 网络降级 <span class="warn">← 不该算 solved</span></td></tr>
<tr><td>L1</td><td>采样 + LLM Refuter "valid"</td><td>非 poly 路径(数据集 75%)</td></tr>
<tr><td>L2</td><td>sound 自动后端 (z3/SOS/nlinarith)</td><td><span class="miss">缺 — gate 该去这里</span></td></tr>
<tr><td>L3</td><td>Lean 编译+无sorry+陈述校验+无公理</td><td>部分(桥被 axiom 化, 陈述未校验)</td></tr></table>'''

doc=f'''<!doctype html><html lang="zh"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Agent 架构分析与数据集分布 · {DATE}</title>
<style>
:root{{--ink:#1a1a1a;--mut:#666;--line:#e3e3e0;--bg:#fbfbfa;--card:#fff;--accent:#3a6ea5}}
*{{box-sizing:border-box}}
body{{margin:0;font:15px/1.65 -apple-system,"PingFang SC",Segoe UI,Roboto,sans-serif;color:var(--ink);background:var(--bg)}}
.wrap{{max-width:1080px;margin:0 auto;padding:32px 24px 80px}}
header{{border-bottom:2px solid var(--ink);padding-bottom:16px;margin-bottom:28px}}
h1{{font-size:25px;margin:0 0 6px}}
.meta{{color:var(--mut);font-size:13px}}
h2{{font-size:19px;margin:38px 0 14px;padding-left:10px;border-left:4px solid var(--accent)}}
.card{{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:18px 20px;margin:14px 0;box-shadow:0 1px 2px rgba(20,30,60,.04)}}
.figcap{{font-size:12.5px;color:var(--mut);text-align:center;margin-top:8px}}
.prob{{border-left:4px solid;border-radius:8px;padding:12px 16px;margin:10px 0}}
.prob.red{{border-color:#e03131;background:#fff5f5}} .prob.orange{{border-color:#e8590c;background:#fff8f1}}
.prob.yellow{{border-color:#f08c00;background:#fffbf0}} .prob.green{{border-color:#2f9e44;background:#f4fbf6}}
.ph{{font-weight:650;margin-bottom:3px}} .pb{{font-size:14px;color:#333}}
code{{background:#eef1f7;padding:1px 5px;border-radius:4px;font-size:13px}}
.grid{{display:grid;grid-template-columns:1fr 1fr;gap:14px}}
@media(max-width:760px){{.grid{{grid-template-columns:1fr}}}}
.dist h3{{font-size:14px;margin:0 0 10px;color:var(--mut);font-weight:600}}
.row{{display:flex;align-items:center;gap:8px;margin:4px 0;font-size:13px}}
.lbl{{flex:0 0 150px;text-align:right;color:#333}}
.barwrap{{flex:1;background:#eef1f7;border-radius:4px;height:16px;overflow:hidden}}
.bar{{display:block;height:100%;background:#3a6ea5;border-radius:4px}}
.num{{flex:0 0 64px;color:var(--mut)}} .num small{{margin-left:5px;opacity:.7}}
table{{border-collapse:collapse;width:100%;font-size:13px;margin-top:6px}}
th,td{{border:1px solid var(--line);padding:6px 10px;text-align:left}} td.r{{text-align:right;font-variant-numeric:tabular-nums}}
th{{background:#f0f3f9}}
.warn{{background:#ffe3e3;color:#c92a2a;font-size:12px;padding:1px 6px;border-radius:4px}}
.miss{{background:#fff3bf;color:#a6791f;font-size:12px;padding:1px 6px;border-radius:4px}}
.kpi{{display:flex;gap:10px;flex-wrap:wrap;margin:6px 0}}
.kpi div{{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:8px 14px;font-size:13px}}
.kpi b{{font-size:18px;color:var(--accent)}}
.note{{font-size:13px;color:var(--mut);margin-top:6px}}
</style></head><body><div class="wrap">

<header>
<h1>Barrier/Lyapunov 合成 Agent —— 架构分析与数据集分布</h1>
<div class="meta">生成日期 {DATE} · 代码 6.11new(v5) · 数据集 core200 manifest v5 (N={N}) · 仅静态分析,未跑批量</div>
</header>

<h2>① Agent 架构</h2>
<div class="card">{ARCH_SVG}
<div class="figcap">图 1. 合成 Agent 数据流(忠实于 <code>run_barrier_synthesis_v4</code>)。橙色虚线为 CEGIS 反馈回路;红色 L0 终态表示 solved 在不 sound 的证据下置位;Lean(L3)后置且失败不回灌 solved。</div></div>

<h2>② 结构性问题(按严重度)</h2>
{prob_html}
<div class="card"><h3 style="margin-top:0">建议:给每个 solved 标注验证等级,benchmark 不塌成一个布尔</h3>
{LEVELS}
<p class="note">优先级:② 网络故障不准置 solved(最小改动最高收益) → ① gate 改为路由到 L2 sound 后端 → solved 带 verify_level 字段。</p></div>

<h2>③ core200 v5 数据集分布(实时计算)</h2>
<div class="kpi">
<div><b>{N}</b> 条 (+20 legacy)</div>
<div>Barrier <b>{task_fam["Barrier (B)"]}</b> · Lyapunov <b>{task_fam["Lyapunov (L)"]}</b></div>
<div>非多项式条件 <b>{poly.get(False,0)}</b> ({100*poly.get(False,0)//N}%)</div>
<div>受控 <b>{ctrl["controlled"]}</b> · 自治 <b>{ctrl["autonomous"]}</b></div>
<div>参数化 ∀n <b>{len(d["summary"]["parametric_entries"])}</b></div>
<div>证书形式唯一 <b>{d["summary"]["certificate_forms_unique"]}</b></div>
</div>
<div class="grid">
<div class="card dist"><h3>验证条件类 verif_cond_class</h3>{bars(vcc)}</div>
<div class="card dist"><h3>时间域 time_domain</h3>{bars(time_d)}</div>
<div class="card dist"><h3>任务细分 task</h3>{bars(task)}</div>
<div class="card dist"><h3>维数 dim</h3>{bars(dim, order=["1D","2D","3D","4–5D","6–8D","≥9D"])}</div>
<div class="card dist"><h3>来源 source_kind</h3>{bars(src)}</div>
<div class="card dist"><h3>受控 vs 自治</h3>{bars(ctrl)}</div>
</div>
<div class="card"><h3 style="margin:0 0 4px;color:var(--mut);font-size:14px">task × time_domain 交叉</h3>
<table><tr><th>任务族</th><th>时间域</th><th class="r">数量</th></tr>{tt_rows}</table>
<p class="note">离散 27 条:22 为 barrier(Cond2=整集一步不变)、仅 5 为 lyapunov。time-varying/hybrid 18 条全在 hard-structure-barrier,而 _task_framework 目前只有 barrier/lyapunov × 连续/离散四类,<b>无 time-varying 分支</b>。</p></div>

<h2>④ 分布 × 架构的对照要点</h2>
<div class="card"><ol style="margin:0;padding-left:20px">
<li><b>75% 验证条件非多项式</b> → poly 快速路只覆盖 25%,四分之三必走 LLM Refuter,放大"LLM 当 oracle 不 sound"的暴露面。</li>
<li><b>离散 barrier 22 条</b> → 需确认 verify_symbolic_discrete 对其全按"整集"而非"边界"采样。</li>
<li><b>维数长尾到 16D(≥9D 共 16 条)</b> → verify_trajectory 的 scipy 积分 25s 预算在高维大量超时降级为 None,高维条目实际只剩符号采样一层。</li>
<li><b>time-varying/hybrid 18 条无对应任务类</b> → _task_framework 需补分支。</li>
</ol></div>

<footer style="margin-top:40px;color:var(--mut);font-size:12px;border-top:1px solid var(--line);padding-top:12px">
本文档由 6.21_maxtest/gen_report.py 生成 · 数据源 lean4_core200_diverse_manifest_v5.json · {DATE}
</footer>
</div></body></html>'''

out=f"/Users/zhipeng/Desktop/paper4/6.21_maxtest/{DATE}_agent架构分析与数据集分布.html"
open(out,"w",encoding="utf-8").write(doc)
print("written:",out,"|",os.path.getsize(out),"bytes")
