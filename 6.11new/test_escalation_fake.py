"""
test_escalation_fake.py — exercise the L1/L2/L3 state machine with FAKE write /
compile / propose callables. Zero API tokens, zero real Lean compiles. Verifies
routing, escalation transitions, barrier regeneration, budget and termination.

Run: python3 test_escalation_fake.py   (exit 0 = all scenarios pass)
"""
from lean_escalation import run_lean_escalation

# real diagnostic strings (so lean_error_kb.route_for routes them authentically)
D_L1 = "error(lean.unknownIdentifier): Unknown constant `Real.foo`"          # -> L1
D_L2 = ("error: linarith failed to find a contradiction\n"                   # -> L2
        "hx : 0 < x\na : x - 1 < Real.log x\n⊢ False")
D_POLY = ("error: linarith failed to find a contradiction\n"                 # -> L2
          "a : x ^ 2 + y ^ 2 < 2 * x * y\n⊢ False")
OK = (True, "")

SYS = {"name": "fake", "ode": "ẋ=…", "state_vars": ["x", "y"], "X_domain": ""}


def scripted_compiler(script):
    """Return (ok,diag) from `script` in order; repeat last when exhausted."""
    st = {"i": 0}

    def _c(_code):
        i = min(st["i"], len(script) - 1)
        st["i"] += 1
        return script[i]
    return _c


def scripted_proposer(certs):
    st = {"i": 0}

    def _p(_s, _d, _prev):
        if st["i"] >= len(certs):
            return None
        c = certs[st["i"]]
        st["i"] += 1
        return c
    return _p


def fake_writer(ctx):
    return f"-- {ctx['cert']} [{ctx['strategy']}]"


def run(script, certs=(), budget=None, cert0="x^2+y^2"):
    return run_lean_escalation(
        SYS, cert0,
        write_fn=fake_writer,
        compile_fn=scripted_compiler(script),
        propose_fn=scripted_proposer(list(certs)),
        budget={**{"inner": 3, "barriers": 3, "max_calls": 12, "repeat_l3": 2},
                **(budget or {})},
        on_event=None,
    )


def routes(res):
    return [l["route"] for l in res["levels"]]


def check(name, cond, detail=""):
    print(f"  {'PASS' if cond else 'FAIL'}  {name}" + (f"   {detail}" if detail else ""))
    assert cond, f"{name} FAILED: {detail}"


def main():
    # 1) compiles on first try
    r = run([OK])
    check("S1 first-try success", r["solved"] and r["calls"] == 1, f"calls={r['calls']}")

    # 2) L1 repair (unknown id) then success
    r = run([(False, D_L1), OK])
    check("S2 L1→OK", r["solved"] and routes(r) == ["L1", "OK"], routes(r))

    # 3) L2 rewrite (transcendental) then success
    r = run([(False, D_L2), OK])
    check("S3 L2→OK", r["solved"] and routes(r) == ["L2", "OK"], routes(r))

    # 4) L3: same error twice → regenerate barrier; new cert compiles
    r = run([(False, D_L2), (False, D_L2), OK], certs=["new_poly_cert"])
    esc_l3 = any(l for l in r["levels"]) and r["solved"]
    check("S4 L3 regenerate→OK",
          r["solved"] and r["cert"] == "new_poly_cert" and len(r["certs_tried"]) == 2,
          f"cert={r['cert']} tried={r['certs_tried']}")

    # 5) repeated distinct L2 errors exhaust inner(3) → regenerate; 2nd cert ok
    r = run([(False, D_L2), (False, D_POLY), (False, D_L1), OK],
            certs=["cert_B"], budget={"repeat_l3": 5})
    check("S5 inner-exhaust→regenerate→OK",
          r["solved"] and r["cert"] == "cert_B", f"cert={r['cert']} routes={routes(r)}")

    # 6) everything fails, no usable new cert → partial, budget respected
    r = run([(False, D_L2)], certs=[], budget={"barriers": 2, "inner": 2})
    check("S6 partial on persistent failure",
          (not r["solved"]) and r["final_level"] == "partial", f"calls={r['calls']}")

    # 7) hard call cap honored
    r = run([(False, D_L1)], certs=["a", "b", "c", "d"], budget={"max_calls": 4})
    check("S7 max_calls honored", r["calls"] <= 4, f"calls={r['calls']}")

    print("\nALL SCENARIOS PASSED ✅  (zero tokens, zero real compiles)")


if __name__ == "__main__":
    main()
