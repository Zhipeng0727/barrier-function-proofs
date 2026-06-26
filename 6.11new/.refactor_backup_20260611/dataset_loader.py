#!/usr/bin/env python3
"""
dataset_loader.py — load external datasets into the SYSTEMS-dict schema used by
dual_agent_debate_4.py.

Two formats are supported:
  1. invariant_dataset.jsonl  (/Users/zhipeng/lean/data) — `dynamics` is already a
     parseable expression list like "[-1*x1, -2*x2]"; converted locally, no LLM.
  2. koopman_nopoly_extension.json — systems described in LaTeX prose; converted
     once via an LLM call and cached in <dataset>.converted.json next to it.

A converted entry looks like a SYSTEMS value:
  { name, ode, state_vars, f_expr, X_domain, X_u_desc, X_u_expr, X_bounds }
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
    if isinstance(records, dict):
        records = list(records.values())

    cache_path = path + ".converted.json"
    cache = {}
    if os.path.exists(cache_path):
        with open(cache_path, encoding="utf-8") as f:
            cache = json.load(f)

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
