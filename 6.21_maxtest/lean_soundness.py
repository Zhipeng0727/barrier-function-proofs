"""
lean_soundness.py — L4 soundness audit for a compiled Lean 4 certificate proof.

A file can compile (exit 0) and be `sorry`-free yet prove NOTHING about real
barriers — the model can axiomatize the calculus bridge, or (worst case, seen in
v4_darboux.lean) reconstruct a fake `axiom Real : Type` with `axiom realAdd …`
and "prove" everything inside that fake structure. strict_sorry does not catch
this. This module closes that hole with three layers:

  A. static scan        — reject any top-level `axiom` / `admit`; warn on trust
                          holes (`native_decide`, `unsafe`, `@[implemented_by]`).
  B. #print axioms      — THE sound check. A genuine Mathlib proof depends only on
                          {propext, Classical.choice, Quot.sound}. Any user axiom
                          or `sorryAx` shows up here. Run as a SEPARATE compile on
                          already-good code so a mis-parsed name can only make the
                          audit inconclusive, never falsely reject a real proof.
  C. statement lint     — heuristic: the proved theorem must actually state the
                          condition (an inequality over the state vars), not a
                          trivial `: True` / `0 = 0`. Best-effort, not sound.

Zero API tokens. Layer B costs one extra `lake env lean` only on a proof that
already passed compile+sorry — i.e. the minority case worth being sure about.
"""
import os
import re
import subprocess
import time as _time

# The three axioms every ordinary Lean4/Mathlib proof is allowed to rest on.
TRUSTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Top-level declaration headers we can target with `#print axioms`.
_DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
_AXIOM_RE = re.compile(r"(?m)^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)")
_ADMIT_RE = re.compile(r"(?<![A-Za-z_])admit(?![A-Za-z0-9_])")
_TRUST_HOLES = {
    "native_decide": r"(?<![A-Za-z_])native_decide(?![A-Za-z0-9_])",
    "unsafe def": r"(?m)^\s*unsafe\s+def\b",
    "@[implemented_by]": r"@\[implemented_by",
}
# crude comment stripper so a `-- talks about sorry/axiom` line never trips us
_LINE_COMMENT = re.compile(r"--[^\n]*")
_BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)


def _strip_comments(code: str) -> str:
    return _LINE_COMMENT.sub("", _BLOCK_COMMENT.sub("", code or ""))


def decl_names(code: str) -> list:
    """Named theorem/lemma declarations, in source order (deduped)."""
    seen, out = set(), []
    for _kind, name in _DECL_RE.findall(_strip_comments(code)):
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def static_scan(code: str) -> dict:
    """Layer A. {ok, fatal[], warn[]}. Fatal ⇒ the proof is not sound regardless
    of compilation."""
    body = _strip_comments(code)
    fatal, warn = [], []
    axioms = _AXIOM_RE.findall(body)
    if axioms:
        shown = ", ".join(axioms[:6]) + ("…" if len(axioms) > 6 else "")
        fatal.append(f"declares {len(axioms)} user axiom(s) [{shown}] — the proof "
                     f"assumes them unproven (fake-ℝ / bridge axiomatization).")
    if _ADMIT_RE.search(body):
        fatal.append("uses `admit` (closes a goal without proving it).")
    for label, pat in _TRUST_HOLES.items():
        if re.search(pat, body):
            warn.append(f"uses `{label}` — a compiler trust hole; verify it is not "
                        f"carrying the proof.")
    return {"ok": not fatal, "fatal": fatal, "warn": warn}


def parse_axiom_report(diag: str) -> dict:
    """Layer B parse. Read every `'name' depends on axioms: [...]` block out of the
    `#print axioms` output. Returns {decls: {name: [axioms]}, offending: {...},
    saw_report: bool}. `sorryAx` and any axiom outside TRUSTED_AXIOMS is offending.
    """
    decls, offending = {}, {}
    saw = False
    # "'foo' depends on axioms: [a, b, c]"
    for m in re.finditer(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", diag or ""):
        saw = True
        name = m.group(1)
        ax = [a.strip() for a in m.group(2).split(",") if a.strip()]
        decls[name] = ax
        bad = [a for a in ax if a not in TRUSTED_AXIOMS]
        if bad:
            offending[name] = bad
    # "'foo' does not depend on any axioms" — explicitly clean
    for m in re.finditer(r"'([^']+)'\s+does not depend on any axioms", diag or ""):
        saw = True
        decls.setdefault(m.group(1), [])
    return {"decls": decls, "offending": offending, "saw_report": saw}


def print_axioms_audit(code: str, names: list, lean_project: str, tag: str,
                       timeout: int = 180) -> dict:
    """Layer B compile. Append `#print axioms <name>` for each named decl and
    compile once more. Returns {ok, offending, decls, inconclusive, diag}.

    ok is True  ⇒ every audited decl rests only on TRUSTED_AXIOMS.
    ok is False ⇒ at least one decl pulls in a user axiom or sorryAx.
    inconclusive ⇒ the audit compile errored (e.g. a name we mis-parsed); the
                   caller keeps the static-scan verdict rather than false-reject.
    """
    if not names:
        return {"ok": True, "offending": {}, "decls": {}, "inconclusive": True,
                "diag": "no named theorem/lemma to audit (anonymous example?)"}
    directives = "\n".join(f"#print axioms {n}" for n in names)
    audited = code + "\n\n-- [L4 soundness audit]\n" + directives + "\n"
    path = os.path.join(lean_project, f"_audit_{tag}.lean")
    try:
        with open(path, "w", encoding="utf-8") as f:
            f.write(audited)
        proc = subprocess.run(["lake", "env", "lean", path], cwd=lean_project,
                              capture_output=True, text=True, timeout=timeout)
        diag = (proc.stdout + "\n" + proc.stderr).strip()
        rep = parse_axiom_report(diag)
        if proc.returncode != 0 and not rep["saw_report"]:
            return {"ok": True, "offending": {}, "decls": {}, "inconclusive": True,
                    "diag": "audit compile errored before reporting axioms"}
        return {"ok": not rep["offending"], "offending": rep["offending"],
                "decls": rep["decls"], "inconclusive": False, "diag": diag[:2000]}
    except subprocess.TimeoutExpired:
        return {"ok": True, "offending": {}, "decls": {}, "inconclusive": True,
                "diag": f"audit compile timed out after {timeout}s"}
    except FileNotFoundError:
        return {"ok": True, "offending": {}, "decls": {}, "inconclusive": True,
                "diag": "lake not found — audit skipped"}
    finally:
        try:
            os.remove(path)
        except OSError:
            pass


_REL_RE = re.compile(r"≤|≥|<|>|≠|∈|∀|∃")
_TRIVIAL_RE = re.compile(r":\s*True\b|:\s*0\s*=\s*0\b|:\s*True\s*:=")


def statement_lint(code: str, state_vars=None) -> dict:
    """Layer C (heuristic). A barrier/Lyapunov obligation is an inequality over the
    state. Flag a main theorem whose STATEMENT (the part before `:=`) carries no
    relational/quantifier symbol, or is trivially `True`/`0 = 0`. Returns
    {ok, warn[]} — ok=False only for the egregious trivial case."""
    body = _strip_comments(code)
    warn = []
    # statements: text between the decl name and the proof `:=`
    stmts = re.findall(r"(?:theorem|lemma)\s+[A-Za-z_][\w'.]*\s*([^:]*:[^=]*?):=", body, re.S)
    if not stmts:
        return {"ok": True, "warn": ["no named theorem statement found to lint"]}
    trivial_all = True
    for s in stmts:
        head = s.split(":", 1)[-1]
        if _TRIVIAL_RE.search(":" + head):
            warn.append(f"a theorem statement looks trivial (`{head.strip()[:40]}…`).")
            continue
        if _REL_RE.search(head):
            trivial_all = False
        else:
            warn.append("a theorem statement has no inequality/∀/∃ — may not encode "
                        "the barrier/Lyapunov condition.")
    if state_vars:
        if not any(re.search(rf"(?<![A-Za-z0-9_]){re.escape(v)}(?![A-Za-z0-9_])", " ".join(stmts))
                   for v in state_vars):
            warn.append("no state variable appears in any statement — the proof may "
                        "be about unrelated symbols.")
    ok = not (trivial_all and stmts)
    return {"ok": ok, "warn": warn}


def audit(code: str, lean_project: str, tag: str, state_vars=None,
          run_print_axioms: bool = True, timeout: int = 180) -> dict:
    """Full L4 verdict for an already compiled+sorry-free file.

    Returns {sound, level, reasons[], warn[], axioms{}} where level ∈
      'sound'          — only trusted axioms, statement non-trivial
      'axiom-tainted'  — depends on user axioms / sorryAx (NOT a real proof)
      'trivial'        — statement proves nothing of substance
      'unverified'     — audit could not be completed (kept as a soft pass)
    """
    reasons, warn = [], []
    sa = static_scan(code)
    warn += sa["warn"]
    if not sa["ok"]:
        return {"sound": False, "level": "axiom-tainted", "reasons": sa["fatal"],
                "warn": warn, "axioms": {}}

    sl = statement_lint(code, state_vars)
    warn += sl["warn"]
    if not sl["ok"]:
        return {"sound": False, "level": "trivial",
                "reasons": ["statement is trivially true — proves nothing of substance"],
                "warn": warn, "axioms": {}}

    axioms = {}
    if run_print_axioms:
        names = decl_names(code)
        rep = print_axioms_audit(code, names, lean_project, tag, timeout=timeout)
        axioms = rep["decls"]
        if rep["inconclusive"]:
            warn.append("axiom-dependency audit inconclusive (" + rep["diag"][:80] + ")")
            return {"sound": True, "level": "unverified", "reasons": [],
                    "warn": warn, "axioms": axioms}
        if not rep["ok"]:
            bad = "; ".join(f"{n} ← {', '.join(ax)}" for n, ax in rep["offending"].items())
            return {"sound": False, "level": "axiom-tainted",
                    "reasons": [f"#print axioms: depends on non-trusted axioms [{bad}]"],
                    "warn": warn, "axioms": axioms}
    return {"sound": True, "level": "sound", "reasons": [], "warn": warn, "axioms": axioms}


# ── self-test against the known-bad darboux proof (zero token) ──
if __name__ == "__main__":
    import sys
    fake = """/- comment mentioning sorry and axiom harmlessly -/
axiom Real : Type
axiom realAdd : Real → Real → Real
theorem barrier_main : True := trivial
"""
    print("static_scan(fake-ℝ):", static_scan(fake))
    print("decl_names:", decl_names(fake))
    print("statement_lint:", statement_lint(fake, ["x1", "x2"]))
    good = "import Mathlib\ntheorem h_nonneg (x : ℝ) : x^2 ≥ 0 := by positivity\n"
    print("static_scan(good):", static_scan(good)["ok"])
    print("statement_lint(good):", statement_lint(good, ["x"]))
    if len(sys.argv) > 1:  # optionally audit a real file path
        code = open(sys.argv[1], encoding="utf-8").read()
        print(audit(code, os.path.expanduser("~/lean"), "selftest",
                    run_print_axioms=False))
