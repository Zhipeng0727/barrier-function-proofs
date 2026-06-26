#!/usr/bin/env python3
"""
dataset_loader.py — load external datasets into the SYSTEMS-dict schema used by
dual_agent_debate_4.py.

Three formats are supported:
  1. invariant_dataset.jsonl  (/Users/zhipeng/lean/data) — `dynamics` is already a
     parseable expression list like "[-1*x1, -2*x2]"; converted locally, no LLM.
  2. koopman_nopoly_extension.json — systems described in LaTeX prose; converted
     once via an LLM call and cached in <dataset>.converted.json next to it.
  3. lean4_core200_diverse_manifest_v4/v5.json — top-level dict with a `core200`
     list; equation-style dynamics ("dx1/dt = ..." / "x1[k+1] = ...") parsed
     locally where possible (incl. named variables, closed-loop controller
     substitution, time-varying autonomization), LLM fallback with cache for
     indexed/vector/prose notation. v5 entries may carry a `machine` dict with
     ready-to-use expressions which is trusted directly.

A converted entry looks like a SYSTEMS value:
  { name, ode, state_vars, f_expr, X_domain, X_u_desc, X_u_expr, X_bounds,
    task_type, discrete, equilibrium, psd_ok, simplex, cert_gt, meta }
"""
import hashlib
import json
import os
import re

import sympy as sp


# ── Xu expression normalization ──────────────────────────────────────────

def normalize_xu(xu: str, state_vars: list):
    """Normalize dataset Xu notation into a sympy-parseable inequality string.
    Handles: ||x|| >= c, |expr|, ^, implicit multiplication, `log x1`,
    ball([c...], r), trailing prose comments. Returns None if unparseable."""
    s = xu.strip()

    # trailing prose comment, e.g. "x1 > 2  (past the wall)" — balance-aware,
    # so nested parens like "(... at (2,0))" are handled
    if s.endswith(")"):
        depth, i = 0, len(s) - 1
        while i >= 0:
            if s[i] == ")":
                depth += 1
            elif s[i] == "(":
                depth -= 1
                if depth == 0:
                    break
            i -= 1
        if i >= 0 and re.search(r"[a-zA-Z]{3,}\s+[a-zA-Z]", s[i:]):
            s = s[:i].strip()

    # ball([c1,c2,...], r) -> sum (xi-ci)^2 <= r^2
    m = re.fullmatch(r"ball\(\s*\[([^\]]+)\]\s*,\s*([\d.eE+-]+)\s*\)", s)
    if m:
        centers = [c.strip() for c in m.group(1).split(",")]
        r = float(m.group(2))
        terms = " + ".join(f"({v} - ({c}))**2" for v, c in zip(state_vars, centers))
        s = f"{terms} <= {r**2}"

    # ||x|| op c  ->  x1**2+...+xn**2 op c**2
    m = re.fullmatch(r"\|\|x\|\|\s*(>=|<=|>|<)\s*([\d.eE+-]+)", s)
    if m:
        op, c = m.group(1), float(m.group(2))
        sq = " + ".join(f"{v}**2" for v in state_vars)
        s = f"{sq} {op} {c**2}"

    s = re.sub(r"\|([^|]+)\|", r"Abs(\1)", s)          # |expr| -> Abs(expr)
    s = s.replace("^", "**")
    s = re.sub(r"\b(log|sin|cos|exp|tan|sqrt|sinh|cosh|tanh|asin|acos|atan|asinh|acosh|atanh)\s+([a-zA-Z]\w*)",
               r"\1(\2)", s)  # log x1 -> log(x1)
    s = re.sub(r"(\d)\s+([a-zA-Z(])", r"\1*\2", s)     # 0.5 x2 -> 0.5*x2

    syms = {v: sp.Symbol(v) for v in state_vars}
    try:
        expr = sp.sympify(s, locals=syms)
        if not (expr.is_Relational or expr.func in (sp.Or, sp.And)):
            return None
        used = {str(a) for a in expr.free_symbols}
        if not used.issubset(set(state_vars)):
            return None  # stray symbols like `energy`
    except Exception:
        return None
    return s


# ── format 1: jsonl with parseable dynamics ──────────────────────────────

def _split_top_level(s: str) -> list:
    """Split on commas not nested inside brackets/parens."""
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def convert_jsonl_record(rec: dict):
    """Returns (system_dict, None) or (None, skip_reason)."""
    dim = int(rec.get("dim") or 0)
    dyn = (rec.get("dynamics") or "").strip()
    if not dyn or dim <= 0:
        return None, "missing dynamics/dim"
    if rec.get("time_domain") == "discrete":
        return None, "discrete-time system (pipeline is continuous-time)"

    f_expr = _split_top_level(dyn.strip("[]"))
    if len(f_expr) != dim:
        return None, f"dynamics has {len(f_expr)} components, dim={dim}"

    state_vars = [f"x{i+1}" for i in range(dim)]
    syms = {v: sp.Symbol(v) for v in state_vars}
    try:
        for fe in f_expr:
            sp.sympify(fe.replace("^", "**"), locals={**syms, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
    except Exception as e:
        return None, f"unparseable dynamics: {e}"

    xu = (rec.get("Xu") or "").strip()
    if not xu:
        return None, "no unsafe set Xu (barrier task needs one)"
    xu_expr = normalize_xu(xu, state_vars)
    if xu_expr is None:
        return None, f"unparseable Xu: {xu[:60]}"

    system = {
        "name": rec.get("id", "jsonl-entry"),
        "ode": ", ".join(f"d{v}/dt = {fe}" for v, fe in zip(state_vars, f_expr)),
        "state_vars": state_vars,
        "f_expr": f_expr,
        "X_domain": rec.get("domain") or f"[-3,3]^{dim}",
        "X_u_desc": xu,
        "X_u_expr": xu_expr,
        "X_bounds": [(-3, 3)] * dim,
        "meta": {k: rec.get(k) for k in ("id", "layer", "group", "task", "cert_class", "source") if k in rec},
    }
    return system, None


# ── format 2: LaTeX prose json, LLM-converted with cache ─────────────────

_CONVERT_PROMPT = """Convert the following dynamical-system description into a strict JSON object
for numerical verification. Output ONLY the JSON, no markdown.

Required fields:
  "state_vars": list of variable names, use x1, x2, ... in equation order
  "f_expr": list of python/sympy expressions for dx_i/dt, using only x1..xn,
            numeric constants and exp/sin/cos/tan/log/sqrt/Abs. Power as **.
  "X_domain": short human-readable description of the state domain X
  "X_u_desc": short human-readable description of the unsafe set X_u
  "X_u_expr": ONE sympy-parseable inequality (or several joined with |) defining X_u,
              e.g. "x1 + x2**2 <= 0". If the description gives no unsafe set, invent a
              reasonable one consistent with the stated safety question and say so in X_u_desc.
  "X_bounds": list of [lo, hi] numeric sampling bounds per state variable (compact box
              covering the interesting region, e.g. [[-2,2],[-2,2]])

Description:
{desc}
"""


def _entry_hash(rec: dict) -> str:
    return hashlib.md5(json.dumps(rec, sort_keys=True, ensure_ascii=False).encode()).hexdigest()[:12]


def convert_prose_record(rec: dict, call_fn, cache: dict):
    """call_fn(system_prompt, messages) -> text. Returns (system, None) or (None, reason)."""
    key = _entry_hash(rec)
    if key in cache:
        cached = cache[key]
        return (cached, None) if isinstance(cached, dict) else (None, str(cached))

    desc = json.dumps({k: rec.get(k) for k in
                       ("title", "system", "domain", "dim", "system_class", "equilibrium") if rec.get(k)},
                      ensure_ascii=False, indent=1)
    try:
        reply = call_fn(
            "You are a precise translator from mathematical system descriptions to machine-checkable JSON.",
            [{"role": "user", "content": _CONVERT_PROMPT.format(desc=desc)}],
        )
        text = reply[0] if isinstance(reply, tuple) else reply
        m = re.search(r"\{.*\}", text, re.S)
        conv = json.loads(m.group(0) if m else text)
        state_vars = conv["state_vars"]
        syms = {v: sp.Symbol(v) for v in state_vars}
        for fe in conv["f_expr"]:
            sp.sympify(fe.replace("^", "**"), locals={**syms, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
        system = {
            "name": rec.get("title", key)[:80],
            "ode": ", ".join(f"d{v}/dt = {fe}" for v, fe in zip(state_vars, conv["f_expr"])),
            "state_vars": state_vars,
            "f_expr": conv["f_expr"],
            "X_domain": conv.get("X_domain", ""),
            "X_u_desc": conv.get("X_u_desc", ""),
            "X_u_expr": conv.get("X_u_expr", "False"),
            "X_bounds": [tuple(b) for b in conv["X_bounds"]],
            "meta": {"title": rec.get("title"), "group": rec.get("group"),
                     "system_class": rec.get("system_class"),
                     "poly_failure_mechanism": rec.get("poly_failure_mechanism")},
        }
        cache[key] = system
        return system, None
    except Exception as e:
        reason = f"conversion failed: {e}"
        cache[key] = reason
        return None, reason


# ── format 3: core200 manifest (v4/v5) ───────────────────────────────────

_SP_FUNCS = {"exp": sp.exp, "sin": sp.sin, "cos": sp.cos, "tan": sp.tan,
             "log": sp.log, "sqrt": sp.sqrt, "Abs": sp.Abs,
             "sinh": sp.sinh, "cosh": sp.cosh, "tanh": sp.tanh,
             "asinh": sp.asinh, "acosh": sp.acosh, "atanh": sp.atanh,
             "atan": sp.atan, "atan2": sp.atan2,
             "Min": sp.Min, "Max": sp.Max}


def _norm_expr(s: str) -> str:
    """Normalize manifest math notation toward sympy syntax."""
    s = s.strip().replace("^", "**").replace("·", "*").replace("−", "-")
    s = re.sub(r"\bmin\(", "Min(", s)
    s = re.sub(r"\bmax\(", "Max(", s)
    s = re.sub(r"\|([^|]+)\|", r"Abs(\1)", s)
    s = re.sub(r"\b(log|exp|sin|cos|tan|sqrt|sinh|cosh|tanh|asin|acos|atan|asinh|acosh|atanh)\s+([a-zA-Z]\w*)",
               r"\1(\2)", s)
    s = re.sub(r"(\d)\s+([a-zA-Z(])", r"\1*\2", s)
    return s


def _try_sympify(s: str, allowed_vars: list):
    syms = {v: sp.Symbol(v, real=True) for v in allowed_vars}
    try:
        expr = sp.sympify(s, locals={**syms, **_SP_FUNCS})
    except Exception:
        return None
    if not {str(a) for a in expr.free_symbols}.issubset(set(allowed_vars)):
        return None
    return expr


def _parse_controller(controller: str, state_vars: list) -> dict:
    """Parse 'u=expr' / 'u1=..., u2=...' controller strings into a substitution
    map {u_name: expr_str}. Returns {} when the text is not clean assignments
    (witness prose, clip/sat with symbolic bounds, ...)."""
    subs = {}
    for part in _split_top_level(controller):
        m = re.match(r"^\s*(u\d*)\s*=\s*(.+)$", part.strip())
        if not m:
            return {}
        rhs = _norm_expr(m.group(2))
        if _try_sympify(rhs, state_vars) is None:
            return {}
        subs[m.group(1)] = rhs
    return subs


def _expand_index_ranges(dyn: str) -> str:
    """Expand 'dxi/dt=-(i-1)*xi for i=2..5' into concrete clauses."""
    parts = _split_top_level(dyn)
    out = []
    for p in parts:
        m = re.match(r"^(.*?)[,\s]+for\s+i\s*=\s*(\d+)\s*\.\.\s*(\d+)\s*$", p.strip())
        if not m:
            out.append(p)
            continue
        template, lo, hi = m.group(1), int(m.group(2)), int(m.group(3))
        for i in range(lo, hi + 1):
            clause = re.sub(r"([a-zA-Z_])i\b", rf"\g<1>{i}", template)  # xi -> x3
            clause = re.sub(r"\bi\b", str(i), clause)                    # bare i -> 3
            out.append(clause)
    return ", ".join(out)


def _parse_equation_dynamics(rec: dict):
    """Locally parse equation-style dynamics. Returns
    (state_vars, f_expr, discrete, extras) or (None, reason, None, None).
    extras = {'time_varying': bool} — caller autonomizes by appending t."""
    dyn = (rec.get("dynamics") or "").strip()
    if not dyn:
        return None, "missing dynamics", None, None
    parts = _split_top_level(_expand_index_ranges(dyn))
    eqs, defs = [], {}
    discrete = None
    for p in parts:
        p = p.strip()
        m = re.match(r"^d\s*([a-zA-Z_]\w*)\s*/\s*dt\s*=\s*(.+)$", p)
        if m:
            eqs.append((m.group(1), m.group(2)))
            discrete = False if discrete is None else discrete
            continue
        m = re.match(r"^([a-zA-Z_]\w*)\s*\[\s*k\s*\+\s*1\s*\]\s*=\s*(.+)$", p)
        if m:
            eqs.append((m.group(1), re.sub(r"\[\s*k\s*\]", "", m.group(2))))
            discrete = True
            continue
        m = re.match(r"^([a-zA-Z_]\w*)\s*=\s*(.+)$", p)  # helper definition clause
        if m and m.group(1) not in ("u",):
            defs[m.group(1)] = m.group(2)
            continue
        return None, f"unparseable dynamics clause: {p[:60]}", None, None
    if not eqs:
        return None, "no differential/difference equations found", None, None

    state_vars = [v for v, _ in eqs]
    if len(set(state_vars)) != len(state_vars):
        return None, "duplicate state variable on LHS", None, None
    dim = rec.get("dim")
    if dim and len(state_vars) != int(dim) and not rec.get("parametric"):
        return None, f"parsed {len(state_vars)} equations but dim={dim} (indexed/vector notation)", None, None

    # helper-definition substitution (e.g. sat(y)=..., H=...) — textual, innermost-first
    f_expr = []
    ctrl_subs = _parse_controller(rec.get("controller", "") or "", state_vars)
    time_varying = False
    for _, rhs in eqs:
        s = rhs
        for _ in range(3):
            for name, val in defs.items():
                s = re.sub(rf"\b{re.escape(name)}\b(?!\()", f"({val})", s)
        for uname, uval in ctrl_subs.items():
            s = re.sub(rf"\b{re.escape(uname)}\b", f"({uval})", s)
        s = _norm_expr(s)
        if _try_sympify(s, state_vars) is not None:
            f_expr.append(s)
            continue
        if _try_sympify(s, state_vars + ["t"]) is not None:   # explicit time dependence
            f_expr.append(s)
            time_varying = True
            continue
        if re.search(r"\bu\d*\b", s):
            return None, "control input u present but controller field not substitutable", None, None
        return None, f"unparseable RHS: {s[:60]}", None, None
    return state_vars, f_expr, bool(discrete), {"time_varying": time_varying}


def _parse_domain_bounds(rec: dict, state_vars: list):
    """Heuristic sampling box from the manifest `domain` string.
    Returns (bounds, simplex_flag)."""
    dom = (rec.get("domain") or "").strip()
    n = len(state_vars)
    if "simplex" in dom.lower() or "Δ" in dom or "Delta" in dom:
        return [(0.02, 0.96)] * n, True
    m = re.fullmatch(r"[\[(]\s*(-?[\d.]+)\s*,\s*(-?[\d.]+|∞|inf)\s*[\])]", dom)
    if m and n == 1:
        lo = float(m.group(1))
        hi = 4.0 if m.group(2) in ("∞", "inf") else float(m.group(2))
        lo = lo + 0.05 if dom.startswith("(") and lo == 0 else lo
        return [(lo, hi)], False
    m = re.match(r"\[\s*(-?[\d.]+)\s*,\s*(-?[\d.]+)\s*\]\s*(?:\*\*|\^)?\s*(\d*)", dom)
    if m:
        return [(float(m.group(1)), float(m.group(2)))] * n, False

    # product domains: (-1,1)×R, (-π,π)^5×R^5, ...
    if "×" in dom or " x " in dom:
        factors = re.split(r"×|\s+x\s+", dom)
        bounds = []
        ok = True
        for fac in factors:
            fac = fac.strip()
            m = re.match(r"^[\[(]\s*(-?[\d.]+|-?pi|-?π)\s*,\s*(-?[\d.]+|pi|π|∞|oo)\s*[\])]"
                         r"\s*(?:\^|\*\*)?\s*(\d*)$", fac)
            if m:
                conv = {"pi": 3.1416, "π": 3.1416, "-pi": -3.1416, "-π": -3.1416,
                        "∞": 4.0, "oo": 4.0}
                lo = conv.get(m.group(1), None)
                lo = float(m.group(1)) if lo is None else lo
                hi = conv.get(m.group(2), None)
                hi = float(m.group(2)) if hi is None else hi
                k = int(m.group(3) or 1)
                # open interval at a singular edge: shrink inward so sampling
                # and trajectories stay where the dynamics are real
                if fac.startswith("("):
                    lo += 0.05 * max(1.0, abs(lo))
                if fac.endswith(")"):
                    hi -= 0.05 * max(1.0, abs(hi))
                bounds.extend([(lo, hi)] * k)
                continue
            m = re.match(r"^R(?:\^|\*\*)?(\d*)$", fac)
            if m:
                bounds.extend([(-3.0, 3.0)] * int(m.group(1) or 1))
                continue
            m = re.match(r"^R_?\{?>\s*0\}?(?:\^|\*\*)?(\d*)$", fac)
            if m:
                bounds.extend([(0.05, 4.0)] * int(m.group(1) or 1))
                continue
            ok = False
            break
        if ok and len(bounds) == n:
            return bounds, False

    if re.search(r"R_?\{?>\s*0|\(0\s*,\s*∞\)|positive orthant|R_\{>=0\}|R_\{≥0\}", dom):
        return [(0.05, 4.0)] * n, False
    m = re.fullmatch(r"[\[(]\s*(-?[\d.]+)\s*,\s*(-?[\d.]+)\s*[\])](?:\^|\*\*)?(\d*)", dom)
    if m and (int(m.group(3) or 1) == n or n == 1):
        lo, hi = float(m.group(1)), float(m.group(2))
        if dom.startswith("("):
            lo += 0.05 * max(1.0, abs(lo))
        if dom.endswith(")"):
            hi -= 0.05 * max(1.0, abs(hi))
        return [(lo, hi)] * n, False
    return [(-3.0, 3.0)] * n, False


def _parse_equilibrium(rec: dict, state_vars: list):
    s = (rec.get("X0_or_equilibrium") or "").strip()
    if not s:
        return None
    if "origin" in s.lower():
        return [0.0] * len(state_vars)
    m = re.fullmatch(r"x\*?\s*=\s*(-?[\d.]+)(?:\s*\(.*\)?)?", s)
    if m:  # "x=1" -> all components
        return [float(m.group(1))] * len(state_vars)
    m = re.fullmatch(rf"({'|'.join(map(re.escape, state_vars))})\*?\s*=\s*(-?[\d.]+).*", s)
    if m and len(state_vars) == 1:
        return [float(m.group(2))]
    m = re.fullmatch(r"x\*?\s*=\s*\(([^)]+)\).*", s)
    if m:
        try:
            vals = [float(v) for v in m.group(1).split(",")]
            if len(vals) == len(state_vars):
                return vals
        except ValueError:
            pass
    m = re.match(r"(?:x1\*?|x\*)\s*=\s*(-?[\d.]+)", s)
    if m and len(state_vars) == 1:
        return [float(m.group(1))]
    return None


def _normalize_certificate(cert: str, state_vars: list, return_defs: bool = False):
    """'B=1.5-H, H=0.5*p^2+1-cos(theta)' -> single sympy-ready expression string.
    Returns None when local normalization fails (indexed sums, free params...).
    With return_defs=True returns (expr_or_None, defs) so Xu normalization can
    reuse helper definitions like H."""
    defs = {}
    if not cert or not cert.strip():
        return (None, defs) if return_defs else None
    parts = _split_top_level(cert.replace(";", ","))
    main = None
    for p in parts:
        p = p.strip()
        m = re.match(r"^([a-zA-Z_]\w*)\s*=\s*(.+)$", p)
        if m is None:
            if main is None:
                main = p  # bare expression without "B=" prefix
            continue
        name, rhs = m.group(1), m.group(2)
        if main is None and name in ("B", "V", "h", "W"):
            main = rhs
        else:
            defs[name] = rhs
    if main is None:
        return (None, defs) if return_defs else None
    # strip trailing prose ("for annulus rotation", " (AKP)") — the paren form
    # must be whitespace-separated so function calls like log(y) survive
    main = re.sub(r"\s+(for|on|with|where)\s+[a-zA-Z].*$", "", main)
    main = re.sub(r"\s+\([a-zA-Z][a-zA-Z\s-]*\)\s*$", "", main)
    s = main
    for _ in range(3):
        for name, val in defs.items():
            s = re.sub(rf"\b{re.escape(name)}\b(?!\()", f"({val})", s)
    # polar aliases for 2D (r/theta are conventions, not state vars)
    if len(state_vars) == 2 and "r" not in state_vars:
        a, b = state_vars
        if re.search(r"\br\b", s):
            s = re.sub(r"\br\s*(?:\*\*2|\^2|²)", f"({a}**2 + {b}**2)", s)
            s = re.sub(r"\br\b", f"sqrt({a}**2 + {b}**2)", s)
        if re.search(r"\btheta\b", s) and "theta" not in state_vars:
            s = re.sub(r"\btheta\b", f"atan2({b}, {a})", s)
    s = _norm_expr(s)
    out = s if _try_sympify(s, state_vars) is not None else None
    return (out, defs) if return_defs else out


_HYBRID_MARKERS = re.compile(r"\bmode\b|\bswitch|piecewise|\bif\b|\belse\b|sigma\(t\)|σ\(t\)", re.I)


def _normalize_manifest_xu(xu: str, state_vars: list, defs: dict = None):
    """Manifest Xu notation -> sympy-parseable condition. Handles set braces,
    unicode operators, 1D interval unions, polar aliases (r/theta for 2D),
    ||x|| norms and helper definitions from the certificate."""
    s = (xu or "").strip()
    if not s:
        return None
    s = re.sub(r"^X?u\s*=\s*", "", s, flags=re.I)
    s = (s.replace("≥", ">=").replace("≤", "<=").replace("∪", " | ").replace("∩", " & ")
          .replace("∞", "oo").replace("π", "pi").replace("−", "-"))

    def _debrace(m):
        inner = m.group(1)
        if "|" in inner.split(">")[0].split("<")[0] and ":" not in inner:
            pass
        if ":" in inner:
            inner = inner.split(":", 1)[1]
        return "(" + inner + ")"
    s = re.sub(r"\{([^{}]*)\}", _debrace, s)

    for name, val in (defs or {}).items():
        s = re.sub(rf"\b{re.escape(name)}\b(?!\()", f"({_norm_expr(val)})", s)

    # ||x|| norms (plain state norm only)
    sumsq = " + ".join(f"{v}**2" for v in state_vars)
    s = re.sub(r"\|\|x\|\|\s*(?:\*\*2|\^2|²)", f"({sumsq})", s)
    m = re.search(r"\|\|x\|\|\s*(>=|<=|>|<)\s*([\d.eE+-]+)", s)
    if m:
        s = s.replace(m.group(0), f"({sumsq}) {m.group(1)} {float(m.group(2))**2}")

    # 1D interval unions: (0,1/10] | [10,oo)
    if len(state_vars) == 1:
        v = state_vars[0]

        def _iv(m):
            lo_br, lo, hi, hi_br = m.groups()
            conds = []
            if lo.lstrip("-") != "oo":
                conds.append(f"({v} {'>' if lo_br == '(' else '>='} {lo})")
            if hi.lstrip("-") != "oo":
                conds.append(f"({v} {'<' if hi_br == ')' else '<='} {hi})")
            return "(" + " & ".join(conds) + ")" if conds else "True"
        s = re.sub(r"([\[(])\s*(-?oo|-?[\d./]+)\s*,\s*(-?oo|-?[\d./]+)\s*([\])])", _iv, s)

    # polar aliases for 2D systems (r, theta are conventions, not state vars)
    if len(state_vars) == 2:
        a, b = state_vars
        if re.search(r"\br\b", s) and "r" not in state_vars:
            s = re.sub(r"\br\s*(?:\*\*2|\^2|²)", f"({a}**2 + {b}**2)", s)
            s = re.sub(r"\br\b", f"sqrt({a}**2 + {b}**2)", s)
        if re.search(r"\btheta\b", s) and "theta" not in state_vars:
            s = re.sub(r"\btheta\b", f"atan2({b}, {a})", s)

    s = _norm_expr(s)
    syms = {v: sp.Symbol(v, real=True) for v in state_vars}
    try:
        expr = sp.sympify(s, locals={**syms, **_SP_FUNCS})
        if not (expr.is_Relational or expr.func in (sp.Or, sp.And)):
            return None
        if not {str(x) for x in expr.free_symbols}.issubset(set(state_vars)):
            return None
    except Exception:
        return None
    return s


def _find_equilibrium(state_vars: list, f_expr: list):
    """Search candidate points (all {0,1}^dim combos for small dim, plus
    all-zeros / all-ones) for f(x*) = 0."""
    syms = {v: sp.Symbol(v, real=True) for v in state_vars}
    try:
        funcs = [sp.lambdify([syms[v] for v in state_vars],
                             sp.sympify(fe, locals={**syms, **_SP_FUNCS}), "math")
                 for fe in f_expr]
    except Exception:
        return None
    n = len(state_vars)
    if n <= 6:
        from itertools import product
        candidates = [list(c) for c in product((0.0, 1.0), repeat=n)]
    else:
        candidates = [[0.0] * n, [1.0] * n]
    for cand in candidates:
        try:
            if all(abs(float(f(*cand))) < 1e-9 for f in funcs):
                return cand
        except Exception:
            continue
    return None


_MANIFEST_CONVERT_PROMPT = """Convert this benchmark entry (a dynamical system with a ground-truth certificate)
into strict JSON for numerical verification. Output ONLY the JSON object.

Required fields:
  "state_vars": ["x1", ...]  — rename any named variables (theta, p, q, s, i, c1...) to x1..xn
                               in equation order; record the mapping in "var_map".
  "f_expr": [...]            — sympy expressions for dx_i/dt (continuous) or x_i[k+1] (discrete),
                               using only x1..xn and numeric constants. Allowed functions:
                               exp,log,sin,cos,tan,sqrt,Abs,sinh,cosh,tanh,atan,atanh,asinh,Min,Max.
                               Expand indexed sums for the entry's dim. Substitute the given controller
                               (closed loop). Instantiate any free parameters with the canonical values
                               implied by the entry (record them in "params").
  "discrete": true/false
  "X_u_expr": ONE sympy-parseable inequality for the unsafe set (or "" if none).
  "X_bounds": [[lo,hi],...]  — compact sampling box respecting the domain (positive orthant: lo>0).
  "simplex": true/false      — true if the state lives on the probability simplex.
  "equilibrium": [...] or null — numeric x* (REQUIRED for lyapunov-type tasks; pick the canonical one).
  "cert_expr": the ground-truth certificate as ONE sympy expression in x1..xn (substitute helper
               definitions like H=..., expand sums, instantiate parameters).
  "var_map": {}, "params": {}

Entry:
{desc}
"""


def _machine_to_system(rec: dict, machine: dict):
    """Build a SYSTEMS dict from a trusted machine block (v5 native or LLM-produced)."""
    f_expr = machine.get("f_expr") or machine.get("map_expr")
    if not f_expr:
        return None, "machine block missing f_expr/map_expr"
    state_vars = machine.get("state_vars") or [f"x{i+1}" for i in range(len(f_expr))]
    discrete = bool(machine.get("discrete", "map_expr" in machine or
                                rec.get("time_domain") == "discrete"))
    task_raw = (rec.get("task") or "barrier").lower()
    task_type = "lyapunov" if ("lyapunov" in task_raw or "clf" in task_raw) else "barrier"
    bounds = [tuple(b) for b in machine.get("bounds") or machine.get("X_bounds") or
              [(-3.0, 3.0)] * len(state_vars)]
    xu_expr = (machine.get("xu_expr") or machine.get("X_u_expr") or "").strip()
    if task_type == "barrier" and not xu_expr:
        return None, "barrier task without usable Xu"
    cert = machine.get("cert_expr") or _normalize_certificate(rec.get("certificate", ""), state_vars)
    psd_ok = bool(machine.get("positive_semidefinite_ok")) or bool(
        re.search(r"first integral|conserved|equilibrium set|consensus|PSD",
                  (rec.get("proof_core", "") + " " + rec.get("notes", "")), re.I))
    arrow = "[k+1] =" if discrete else "/dt ="
    system = {
        "name": f"{rec.get('id','?')} {rec.get('title','')}".strip(),
        "ode": ", ".join(f"{'' if discrete else 'd'}{v}{arrow} {fe}"
                          for v, fe in zip(state_vars, f_expr)),
        "state_vars": list(state_vars),
        "f_expr": list(f_expr),
        "X_domain": rec.get("domain") or "see bounds",
        "X_u_desc": rec.get("Xu", ""),
        "X_u_expr": xu_expr or "False",
        "X_bounds": bounds,
        "task_type": task_type,
        "discrete": discrete,
        "simplex": bool(machine.get("simplex")),
        "equilibrium": machine.get("equilibrium"),
        "psd_ok": psd_ok,
        "cert_gt": cert,
        "meta": {k: rec.get(k) for k in
                 ("id", "group", "task", "time_domain", "dynamics_class", "certificate_form",
                  "verif_cond_class", "verif_cond_poly", "parametric", "source_ref")
                 if rec.get(k) is not None},
    }
    if task_type == "lyapunov" and system["equilibrium"] is None and not psd_ok:
        return None, "lyapunov task without numeric equilibrium"
    return system, None


def convert_manifest_record(rec: dict, call_fn, cache: dict):
    """core200 manifest entry -> (system, None) or (None, skip_reason).
    Local parse first; trusted `machine` block wins; LLM fallback (cached) last.
    NOTE: time_domain is a coarse GROUP label ("continuous/time-varying/hybrid"
    covers plain-continuous entries too) — actual hybrid/switched structure is
    detected from the dynamics text instead."""
    if isinstance(rec.get("machine"), dict):
        return _machine_to_system(rec, rec["machine"])

    if _HYBRID_MARKERS.search(rec.get("dynamics", "")):
        return None, "hybrid/switched mode structure not supported yet"

    parsed = _parse_equation_dynamics(rec)
    if parsed[0] is not None:
        state_vars, f_expr, discrete, extras = parsed
        if extras["time_varying"]:
            # autonomize: t becomes a state with dt/dt = 1 (continuous only)
            if discrete:
                return None, "time-varying discrete system not supported"
            state_vars = state_vars + ["t"]
            f_expr = f_expr + ["1"]
        bounds, simplex = _parse_domain_bounds(rec, state_vars)
        if state_vars and state_vars[-1] == "t":
            bounds[-1] = (0.0, 10.0)
        cert_expr, cert_defs = _normalize_certificate(rec.get("certificate", ""),
                                                      state_vars, return_defs=True)
        xu_raw = (rec.get("Xu") or "").strip()
        xu_expr = (_normalize_manifest_xu(xu_raw, state_vars, cert_defs)
                   or normalize_xu(xu_raw, state_vars)) if xu_raw else None
        equilibrium = _parse_equilibrium(rec, state_vars)
        if equilibrium is None:
            f_for_eq = ([f"({fe}) - {v}" for v, fe in zip(state_vars, f_expr)]
                        if discrete else f_expr)
            equilibrium = _find_equilibrium(state_vars, f_for_eq)
        machine = {
            "state_vars": state_vars, "f_expr": f_expr, "discrete": discrete,
            "X_u_expr": xu_expr or "", "bounds": bounds, "simplex": simplex,
            "equilibrium": equilibrium,
            "cert_expr": cert_expr,
        }
        system, reason = _machine_to_system(rec, machine)
        if system is not None:
            return system, None
        local_reason = reason
    else:
        local_reason = parsed[1]

    # LLM fallback with cache (same mechanism as prose datasets)
    key = _entry_hash(rec)
    if key in cache:
        cached = cache[key]
        if isinstance(cached, dict):
            return _machine_to_system(rec, cached)
        return None, str(cached)
    if call_fn is None:
        return None, f"local parse failed ({local_reason}); needs LLM conversion (no call_fn)"
    desc = json.dumps({k: rec.get(k) for k in
                       ("id", "title", "task", "dim", "time_domain", "domain", "dynamics",
                        "X0_or_equilibrium", "Xu", "certificate", "controller", "input_bounds",
                        "dynamics_class", "notes") if rec.get(k)},
                      ensure_ascii=False, indent=1)
    try:
        reply = call_fn(
            "You are a precise translator from mathematical system descriptions to machine-checkable JSON.",
            [{"role": "user", "content": _MANIFEST_CONVERT_PROMPT.replace("{desc}", desc)}])
        text = reply[0] if isinstance(reply, tuple) else reply
        m = re.search(r"\{.*\}", text, re.S)
        machine = json.loads(m.group(0) if m else text)
        for fe in machine["f_expr"]:
            if _try_sympify(_norm_expr(str(fe)), machine["state_vars"]) is None:
                raise ValueError(f"LLM f_expr not parseable: {fe}")
        machine["f_expr"] = [_norm_expr(str(fe)) for fe in machine["f_expr"]]
        system, reason = _machine_to_system(rec, machine)
        if system is None:
            raise ValueError(reason)
        cache[key] = machine
        return system, None
    except Exception as e:
        reason = f"conversion failed: {e} (local: {local_reason})"
        cache[key] = reason
        return None, reason


# ── unified entry point ──────────────────────────────────────────────────

def load_dataset(path: str, call_fn=None, limit: int = None):
    """Returns (entries, skipped) where entries = [(entry_id, system_dict)],
    skipped = [(entry_id, reason)]. call_fn is required for prose datasets."""
    entries, skipped = [], []

    if path.endswith(".jsonl"):
        records = []
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    records.append(json.loads(line))
        for rec in records[:limit]:
            eid = rec.get("id") or f"line{len(entries)+len(skipped)}"
            system, reason = convert_jsonl_record(rec)
            (entries.append((eid, system)) if system else skipped.append((eid, reason)))
        return entries, skipped

    with open(path, encoding="utf-8") as f:
        records = json.load(f)

    cache_path = path + ".converted.json"
    cache = {}
    if os.path.exists(cache_path):
        with open(cache_path, encoding="utf-8") as f:
            cache = json.load(f)

    # core200 manifest (v4/v5): top-level dict carrying the entry list
    if isinstance(records, dict) and ("core200" in records or "core" in records):
        manifest_records = records.get("core200") or records.get("core")
        try:
            for i, rec in enumerate(manifest_records[:limit]):
                eid = rec.get("id", f"entry{i}")
                system, reason = convert_manifest_record(rec, call_fn, cache)
                (entries.append((eid, system)) if system else skipped.append((eid, reason)))
        finally:
            with open(cache_path, "w", encoding="utf-8") as f:
                json.dump(cache, f, ensure_ascii=False, indent=1)
        return entries, skipped

    if isinstance(records, dict):
        records = list(records.values())

    try:
        for i, rec in enumerate(records[:limit]):
            eid = rec.get("id") or rec.get("title", f"entry{i}")[:50]
            if call_fn is None and _entry_hash(rec) not in cache:
                skipped.append((eid, "needs LLM conversion (no call_fn)"))
                continue
            system, reason = convert_prose_record(rec, call_fn, cache)
            (entries.append((eid, system)) if system else skipped.append((eid, reason)))
    finally:
        with open(cache_path, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, indent=1)
    return entries, skipped
