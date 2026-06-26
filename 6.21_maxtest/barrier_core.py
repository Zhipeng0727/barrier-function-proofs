"""
barrier_core.py — stateless math + domain substrate for the barrier-synthesis pipeline.

Pure, side-effect-free building blocks (no network, no mutable runtime globals):
  - System catalog:     SYSTEMS
  - Agent prompts:      proposer_system, refuter_system, lean4_system
  - Expression parsing: _parse_B_expr, _eval_Xu, parse_json_response
  - Local verification: verify_symbolic, verify_trajectory, precheck_cache,
                        harvest_cache, nontrivial_C_check, local_verify
  - Visualization:      plot_barrier

Depends only on the optional-dependency flags from runtime_state; sympy/scipy stay
lazily imported behind those guards.

Mathematical framework (continuous time, Proposition 4 / Nagumo Theorem):
  Given state domain X, unsafe set X_u ⊂ X, find h: X -> R satisfying:
    (1) h(x) < 0,  ∀x ∈ X_u
    (2) ḣ(x) >= 0,  ∀x ∈ ∂C  (Nagumo condition, only on the boundary h=0)
  Then C = {x ∈ X : h(x) >= 0} is an invariant set.
"""

import json
import time

import numpy as np

from runtime_state import HAS_SYMPY, HAS_SCIPY

if HAS_SYMPY:
    import sympy as sp
if HAS_SCIPY:
    from scipy.integrate import solve_ivp

# ─────────────────────────────────────────────
# 1. System catalog (paper framework: X, X_u, f_expr)
# ─────────────────────────────────────────────
# Each system contains:
#   state_vars : list of state variable names
#   ode        : equation description string (for display)
#   f_expr     : list of f(x) expressions evaluable by Python/sympy
#   X_domain   : description of state domain X (for display)
#   X_u_desc   : description of unsafe set X_u (for display)
#   X_u_expr   : sympy-evaluable condition expression for X_u (returns True if x ∈ X_u)
#   X_bounds   : sampling range for numerical verification [(lo,hi), ...]
SYSTEMS = {
    # ── Paper Example 4 (Darboux barrier) ──
    "darboux": {
        "name": "Darboux System (Paper Example 4)",
        "ode": "ẋ₁ = x₂ + 2x₁x₂,  ẋ₂ = -x₁ - x₂² + 2x₁²",
        "state_vars": ["x1", "x2"],
        "f_expr": ["x2 + 2*x1*x2", "-x1 - x2**2 + 2*x1**2"],
        "X_domain": "X = [-2,2] × [-2,2]",
        "X_u_desc": "X_u = {(x1,x2) ∈ X | x1 + x2**2 <= 0}",
        "X_u_expr": "x1 + x2**2 <= 0",
        "X_bounds": [(-2, 2), (-2, 2)],
    },
    # ── Paper Example 5 ──
    "ex5": {
        "name": "Nonlinear System (Paper Example 5)",
        "ode": "ẋ₁ = e^(-x₁) + x₂ - 1,  ẋ₂ = -sin²(x₁)",
        "state_vars": ["x1", "x2"],
        "f_expr": ["exp(-x1) + x2 - 1", "-sin(x1)**2"],
        "X_domain": "X = [-2,2] × [-2,2]",
        "X_u_desc": "X_u = {(x1,x2) ∈ X | (x1-0.7)² + (x2+0.7)² <= 0.09}",
        "X_u_expr": "(x1 - 0.7)**2 + (x2 + 0.7)**2 <= 0.09",
        "X_bounds": [(-2, 2), (-2, 2)],
    },
    # ── Hard system: Duffing, unsafe set is the exterior of the domain ──
    "duffing": {
        "name": "Duffing Oscillator (damped)",
        "ode": "ẋ = y,  ẏ = -0.5y - x - x³",
        "state_vars": ["x", "y"],
        "f_expr": ["y", "-0.5*y - x - x**3"],
        "X_domain": "X = [-3,3] × [-3,3]",
        "X_u_desc": "X_u = {(x,y) | |x| > 3 or |y| > 3} (complement of X, i.e., all points outside X)",
        "X_u_expr": "(x > 3) | (x < -3) | (y > 3) | (y < -3)",
        "X_bounds": [(-3, 3), (-3, 3)],
        "X_u_sample_bounds": [(-6, 6), (-6, 6)],
    },
    # ── Hard system: Van der Pol mu=2, unsafe set is the exterior of the domain ──
    "vanderpol": {
        "name": "Van der Pol mu=2 (finding invariant set inside limit cycle)",
        "ode": "ẋ = y,  ẏ = 2(1-x²)y - x",
        "state_vars": ["x", "y"],
        "f_expr": ["y", "2*(1-x**2)*y - x"],
        "X_domain": "X = [-5,5] × [-5,5]",
        "X_u_desc": "X_u = {(x,y) | |x| > 5 or |y| > 5} (complement of X, i.e., all points outside X)",
        "X_u_expr": "(x > 5) | (x < -5) | (y > 5) | (y < -5)",
        "X_bounds": [(-5, 5), (-5, 5)],
        "X_u_sample_bounds": [(-10, 10), (-10, 10)],
    },
    # ── Hard system: Lorenz rho<1, 3D, unsafe set is the exterior of the domain ──
    "lorenz": {
        "name": "Lorenz System (sigma=10, rho=0.5, beta=8/3, origin globally stable)",
        "ode": "ẋ = 10(y-x),  ẏ = x(0.5-z)-y,  ż = xy-(8/3)z",
        "state_vars": ["x", "y", "z"],
        "f_expr": ["10*(y-x)", "x*(0.5-z)-y", "x*y-(8/3)*z"],
        "X_domain": "X = [-4,4] × [-4,4] × [-4,4]",
        "X_u_desc": "X_u = {(x,y,z) | |x| > 4 or |y| > 4 or |z| > 4} (complement of X, i.e., all points outside X)",
        "X_u_expr": "(x > 4) | (x < -4) | (y > 4) | (y < -4) | (z > 4) | (z < -4)",
        "X_bounds": [(-4, 4), (-4, 4), (-4, 4)],
        "X_u_sample_bounds": [(-8, 8), (-8, 8), (-8, 8)],
    },
    # ── Hard system: coupled nonlinear, unsafe set is the exterior of the domain ──
    "coupled": {
        "name": "Coupled Nonlinear System",
        "ode": "ẋ = -x + x·y²,  ẏ = -y - x²·y",
        "state_vars": ["x", "y"],
        "f_expr": ["-x + x*y**2", "-y - x**2*y"],
        "X_domain": "X = [-2,2] × [-2,2]",
        "X_u_desc": "X_u = {(x,y) | |x| > 2 or |y| > 2} (complement of X, i.e., all points outside X)",
        "X_u_expr": "(x > 2) | (x < -2) | (y > 2) | (y < -2)",
        "X_bounds": [(-2, 2), (-2, 2)],
        "X_u_sample_bounds": [(-4, 4), (-4, 4)],
    },
    # ── BarrierBench #16: 2D stable linear system, unsafe set is the exterior of a ball ──
    "bb_linear": {
        "name": "BarrierBench Linear 2D",
        "ode": "ẋ₁ = -5x₁ - 4x₂,  ẋ₂ = -x₁ - 2x₂",
        "state_vars": ["x1", "x2"],
        "f_expr": ["-5*x1 - 4*x2", "-x1 - 2*x2"],
        "X_domain": "X = [-3,3] × [-3,3]",
        "X_u_desc": "X_u = {(x1,x2) | x1² + x2² > 9} (exterior of ball of radius 3)",
        "X_u_expr": "x1**2 + x2**2 > 9",
        "X_bounds": [(-3, 3), (-3, 3)],
        "X_u_sample_bounds": [(-6, 6), (-6, 6)],
    },
    # ── BarrierBench #17: 3D nonlinear system (with sin/cos), unsafe set is the exterior of a ball ──
    "bb_trig": {
        "name": "BarrierBench Nonlinear 3D (sin/cos)",
        "ode": "ẋ₁ = -0.5x₁ + 0.3x₂sin(x₃) - 0.1x₁²x₂,  ẋ₂ = -0.6x₂ + 0.5x₁cos(x₃) + 0.15x₃²x₁,  ẋ₃ = -0.7x₃ - 0.1x₃³",
        "state_vars": ["x1", "x2", "x3"],
        "f_expr": [
            "-0.5*x1 + 0.3*x2*sin(x3) - 0.1*x1**2*x2",
            "-0.6*x2 + 0.5*x1*cos(x3) + 0.15*x3**2*x1",
            "-0.7*x3 - 0.1*x3**3",
        ],
        "X_domain": "X = [-3.5,3.5] × [-3.5,3.5] × [-3.5,3.5]",
        "X_u_desc": "X_u = {(x1,x2,x3) | x1² + x2² + x3² > 12.25} (exterior of ball of radius 3.5)",
        "X_u_expr": "x1**2 + x2**2 + x3**2 > 12.25",
        "X_bounds": [(-3.5, 3.5), (-3.5, 3.5), (-3.5, 3.5)],
        "X_u_sample_bounds": [(-7, 7), (-7, 7), (-7, 7)],
    },
}

# ─────────────────────────────────────────────
# 2. Agent system prompts
# ─────────────────────────────────────────────
def _task_framework(system: dict) -> dict:
    """Shared task-dependent text blocks for the agent prompts (v5).
    Returns dict(goal, conditions, quantity_name)."""
    task = system.get("task_type", "barrier")
    discrete = bool(system.get("discrete"))
    if task == "lyapunov":
        eq = system.get("equilibrium")
        eq_txt = str(eq) if eq is not None else "the origin"
        decr = ("Condition D: V(f(x)) - V(x) <= 0 for all x in the domain X "
                "(one-step decrease of the map)" if discrete else
                "Condition D: Vdot(x) = ∇V(x) · f(x) <= 0 for all x in the domain X")
        return {
            "goal": (f"find a Lyapunov function V(x) certifying stability of the equilibrium x* = {eq_txt} "
                     f"for the following {'discrete-time map x+ = f(x)' if discrete else 'continuous dynamical system'}"),
            "conditions": (
                f"  Condition P0: V(x*) = 0 at the equilibrium x* = {eq_txt} (additive constants are tolerated and auto-shifted)\n"
                f"  Condition P1: V(x) > 0 for all x in X with x != x*"
                + (" (positive SEMIdefinite V is acceptable for this system: equilibrium set / first integral)"
                   if system.get("psd_ok") else "") + "\n"
                f"  {decr}"),
            "quantity_name": "Lyapunov function V(x)",
        }
    if discrete:
        return {
            "goal": ("find a barrier function h(x) for the following discrete-time map x+ = f(x) "
                     "such that C = {x in X : h(x) >= 0} is a forward-invariant set avoiding the unsafe set"),
            "conditions": (
                "  Condition 1: h(x) < 0,  ∀x ∈ X_u   (unsafe set lies in the negative region of h)\n"
                "  Condition 2: h(f(x)) >= 0,  ∀x with h(x) >= 0   (ONE-STEP invariance of the whole set C — "
                "discrete trajectories jump, so the condition is on all of C, not just the boundary)"),
            "quantity_name": "barrier function h(x)",
        }
    return {
        "goal": ("find a barrier function h(x) for the following continuous dynamical system "
                 "such that the set C = {x ∈ X : h(x) >= 0} is an invariant set"),
        "conditions": (
            "  Condition 1: h(x) < 0,  ∀x ∈ X_u   (unsafe set lies in the negative region of h)\n"
            "  Condition 2: ḣ(x) >= 0,  ∀x ∈ ∂C  (i.e., the boundary where h(x)=0, Nagumo condition)"),
        "quantity_name": "barrier function h(x)",
    }


def proposer_system(system: dict) -> str:
    fw = _task_framework(system)
    if system.get("task_type", "barrier") == "lyapunov" or system.get("discrete"):
        return f"""You are a control theory expert specializing in Lyapunov and barrier certificates.

Your task is to {fw['goal']}.

[System Information]
System name: {system['name']}
Dynamics: {system['ode']}
State domain X: {system['X_domain']}
{('Unsafe set X_u: ' + system['X_u_desc']) if system.get('X_u_desc') else ''}
State variables: {', '.join(system['state_vars'])}

The certificate need not be polynomial; you may construct it by working backwards from the proof
(log/exp/trig/entropy/energy forms are all acceptable).

[Required Conditions]
{fw['conditions']}

[Output Format] Output strictly the following JSON (no markdown code blocks):
{{
  "h": "expression for the certificate, e.g. (log(x1))**2 + x2**2",
  "invariant_set": "description of the certified set / region of attraction",
  "condition1_check": "derivation for the sign/unsafe-set condition (or positivity for Lyapunov)",
  "lie_derivative": "the decrease quantity ({'V(f(x))-V(x)' if system.get('discrete') else 'gradient dot f'}) and its computation",
  "condition2_check": "derivation that the decrease/invariance condition holds",
  "reasoning": "rationale for choosing this certificate"
}}

[Strict requirements for the "h" field]
1. Only state variables ({', '.join(system['state_vars'])}) and numeric constants; no free parameters
2. Python power notation x**2; allowed functions: exp, log, sin, cos, tan, sqrt, Abs, sinh, cosh, tanh, atan, atanh, asinh, Min, Max
3. Do NOT use intermediate names (A, P, V, H, phi) inside the "h" field — fully expand it"""
    return f"""You are a control theory expert specializing in barrier functions and invariant sets.

Your task is to find a barrier function h(x) for the following continuous dynamical system such that the set C = {{x ∈ X : h(x) >= 0}} is an invariant set.
We consider it acceptable as long as the system does not enter the defined unsafe set; strict confinement within X is not required.

[System Information]
System name: {system['name']}
Dynamics: {system['ode']}
State domain X: {system['X_domain']}
Unsafe set X_u: {system['X_u_desc']}
State variables: {', '.join(system['state_vars'])}

The barrier function need not be polynomial; you may construct it by working backwards from the theorem proof.

[Mathematical Framework (Proposition 4 / Nagumo Theorem)]
Find h: R -> R satisfying:
  Condition 1: h(x) < 0,  ∀x ∈ X_u   (unsafe set lies in the negative region of h)
  Condition 2: ḣ(x) >= 0,  ∀x ∈ ∂C  (i.e., the boundary where h(x)=0, Nagumo condition)
The expression for h should preferably be analytic for ease of verification; avoid using trajectories, vector fields, or other objects that are hard to verify directly. Examples: combinations of trigonometric functions, polynomials, exponentials, etc.

Here ḣ(x) = ∇h(x) · f(x) is the Lie derivative of h along the system trajectories.

Then C = {{x ∈ X : h(x) >= 0}} is an invariant set (superlevel set; note h >= 0, not h <= 0).

[Objective]
- The invariant set C should be as large as possible (covering more safe regions)
- Note: h(x) should be an analytic expression for ease of verification; avoid trajectories, vector fields (these can be used for analysis only)
- Cross-term verification must be rigorous and complete; strict mathematical computation is required, possibly including inequality proofs

[Output Format] Please output strictly in the following JSON format (do not add markdown code blocks):
{{
  "h": "expression for h(x), e.g. 1 - x1**2 - x2**2",
  "invariant_set": "description of C, e.g. x1**2 + x2**2 <= 1",
  "condition1_check": "derivation verifying h(x) < 0 holds on X_u",
  "lie_derivative": "computation process and result of ḣ(x) = ∇h·f",
  "condition2_check": "derivation verifying ḣ(x) >= 0 holds on ∂C (boundary h=0)",
  "reasoning": "rationale for choosing this h"
}}

[Strict requirements for the "h" field]
Since the system will automatically invoke local Python/sympy for symbolic verification and visualization of h, the "h" field must satisfy:
1. Only contain state variables ({', '.join(system['state_vars'])}) and pure numeric constants; no symbolic parameters such as delta, epsilon, etc.
2. All small positive constants must be written as explicit numeric values, e.g. use 0.01 instead of delta
3. Use Python power notation x**2 (not x^2)
4. Allowed functions: exp(·), sin(·), cos(·), tan(·), log(·), sqrt(·), Abs(·)
5. CRITICAL: Do NOT use intermediate variable names (e.g. A, P, F, V, phi) in the "h" field. You may define them in condition1_check/lie_derivative for human readability, but the "h" field itself must be fully expanded in terms of {', '.join(system['state_vars'])} only.
   WRONG: "h": "A - P + Abs(A + P)"   (A and P are not state variables)
   RIGHT: "h": "<fully expanded expression using only {', '.join(system['state_vars'])}>"
6. Example valid expression: -(1 + 2*x1)*x2**2 - x1**2 + (4/3)*x1**3 - 0.01"""


def refuter_system(system: dict) -> str:
    fw = _task_framework(system)
    return f"""You are a rigorous mathematical verification expert specializing in finding flaws and counterexamples in {fw['quantity_name'].split('(')[0].strip()} certificates.

We consider it acceptable as long as the system does not enter the defined unsafe set; strict confinement within X is not required.

System under analysis:
Dynamics: {system['ode']}
State domain X: {system['X_domain']}
{('Unsafe set X_u: ' + system['X_u_desc']) if system.get('X_u_desc') else ''}
State variables: {', '.join(system['state_vars'])}
Task: verify a proposed {fw['quantity_name']} ({'discrete-time map' if system.get('discrete') else 'continuous-time system'})

[Required Conditions]
{fw['conditions']}

[Verification Steps]
1. Verify the first (sign/positivity) condition at specific points; after quick numerical checks, use formal inequality proofs
2. Compute the decrease quantity exactly ({'Delta = V(f(x)) - V(x) or h(f(x))' if system.get('discrete') else 'the Lie derivative ∇·f'})
3. Check the second (decrease/invariance) condition on its required region ({'all of C / all of X' if system.get('discrete') else 'the boundary ∂C for barriers, the whole domain for Lyapunov'}); first quick point verification, then formal inequality proofs if it passes
4. Cross-term verification must be rigorous and complete; strict mathematical computation is required, possibly including inequality proofs
5. (Only when verdict is "valid") Analyze whether the certified set could be enlarged: consider whether the level set threshold, coefficients, or functional form could be adjusted to cover more of X while still satisfying all conditions. If an enlargement direction exists, provide a concrete suggestion.

[Output Format] Please output strictly in the following JSON format (do not add markdown code blocks):
{{
  "verdict": "valid" or "invalid",
  "condition1_result": "Condition 1 verification result with specific numerical values",
  "lie_derivative_computed": "your recomputed ∇h·f expression",
  "condition2_result": "Condition 2 verification result with specific numerical values",
  "counterexample": "if invalid, provide specific counterexample point and numerical verification; if valid, null",
  "flaw": "if invalid, describe which condition fails; if valid, null",
  "suggestion": "if invalid, provide guidance for correction; if valid, null",
  "enlargement_suggestion": "if valid and the invariant set could plausibly be enlarged, describe a concrete direction (e.g. adjust a coefficient, shift the level set, change functional form); if no enlargement is apparent or verdict is invalid, null"
}}"""


def lean4_system(system: dict) -> str:
    fw = _task_framework(system)
    return f"""You are a Lean 4 formal proof expert familiar with Mathlib4.

Your task is to write a formal proof framework in Lean 4 for an already-verified certificate
({fw['quantity_name']}, {'discrete-time map' if system.get('discrete') else 'continuous-time system'}).

System: {system['ode']}
State domain: {system['X_domain']}
{('Unsafe set: ' + system['X_u_desc']) if system.get('X_u_desc') else ''}

Conditions to formalize:
{fw['conditions']}

Requirements:
1. Use Lean 4 + Mathlib4 syntax
2. Define the system dynamics, the certificate, and the certified set
3. State the conditions AS THE ACTUAL INEQUALITIES over the state variables, and FULLY prove
   them and the main theorem with real tactics (nlinarith/polyrith/positivity/...).
4. SOUNDNESS (hard rules — a proof that breaks these is rejected even if it compiles):
   - NO `axiom` declarations of any kind. Never re-declare ℝ or its operations
     (`axiom Real`, `axiom realAdd`, …) — import Mathlib's reals and use them.
   - NO `sorry`, no `admit`. A genuine proof rests only on Mathlib's standard axioms.
   - Give the main result a NAMED top-level `theorem` (e.g. `theorem barrier_main : …`),
     not an anonymous `example`, so its axiom dependencies can be audited.
   - If the calculus/Nagumo bridge genuinely cannot be discharged, say so — do NOT
     axiomatize it to fake a pass.
5. First give a natural language outline of the proof, then write the Lean 4 code implementation
6. The code must compile under `lake env lean` against Mathlib4

Output the Lean 4 code directly, no additional explanation needed."""


# ─────────────────────────────────────────────
# 3. Symbolic / trajectory verification + counterexample cache
# ─────────────────────────────────────────────
class _TrajTimeout(Exception):
    """Raised from inside an ODE right-hand side when the wall-clock deadline
    passes — solve_ivp can otherwise spin forever shrinking steps near a
    singularity (e.g. atanh blow-up at the domain edge), and an outer
    per-trajectory budget never gets a chance to fire."""


def _budgeted_rhs(f_funcs, deadline):
    def rhs(t, state):
        if time.time() > deadline:
            raise _TrajTimeout()
        return [float(fi(*state)) for fi in f_funcs]
    return rhs


def _safe_simplify(expr, sym_list):
    """simplify() only for polynomial/rational expressions — on transcendental
    ones (atanh/log/exp mixes) it can hang for minutes even at small size, and
    the numerical verification downstream does not need simplification."""
    try:
        if expr.is_polynomial(*sym_list) or expr.is_rational_function(*sym_list):
            if sp.count_ops(expr) <= 300:
                return sp.simplify(expr).doit()
            return sp.cancel(expr).doit()
    except Exception:
        pass
    return expr.doit()


def _parse_B_expr(expr_str: str, state_vars: list):
    """Convert LLM output expression to a sympy expression, applying common symbol substitutions"""
    s = expr_str.replace("^", "**").replace("·", "*")
    # real=True so derivatives of Abs/sqrt etc. resolve to sign(...) instead of
    # leaving an unevaluated Derivative that NumPyPrinter can't lambdify.
    syms = {v: sp.Symbol(v, real=True) for v in state_vars}
    extra = {
        "exp": sp.exp, "sin": sp.sin, "cos": sp.cos,
        "tan": sp.tan, "log": sp.log, "sqrt": sp.sqrt,
        "Abs": sp.Abs, "abs": sp.Abs,
        "sinh": sp.sinh, "cosh": sp.cosh, "tanh": sp.tanh,
        "asinh": sp.asinh, "acosh": sp.acosh, "atanh": sp.atanh,
        "atan": sp.atan, "atan2": sp.atan2, "asin": sp.asin, "acos": sp.acos,
        "Min": sp.Min, "Max": sp.Max, "min": sp.Min, "max": sp.Max,
        "sign": sp.sign,
    }
    try:
        expr = sp.sympify(s, locals={**syms, **extra})
        return expr, syms
    except Exception:
        return None, syms


def _eval_Xu(system: dict, pts: np.ndarray) -> np.ndarray:
    """Evaluate X_u membership at sampled points, returning a bool array.
    Supports: single inequalities (Le/Lt/Ge/Gt) and Or compound expressions."""
    state_vars = system["state_vars"]
    X_u_expr   = system.get("X_u_expr", "False")
    syms       = {v: sp.Symbol(v, real=True) for v in state_vars}
    sym_list   = [syms[v] for v in state_vars]

    def _eval_single(expr, pts):
        """Evaluate boolean value for a single inequality"""
        if not (hasattr(expr, "lhs") and hasattr(expr, "rhs")):
            return None
        diff_func = sp.lambdify(sym_list, expr.lhs - expr.rhs, "numpy")
        d = np.array(diff_func(*pts.T), dtype=float)
        rel = type(expr).__name__
        if rel in ("Le", "Lt", "LessThan", "StrictLessThan"):
            return d <= 0
        else:  # Ge, Gt, GreaterThan, StrictGreaterThan
            return d >= 0

    try:
        expr = sp.sympify(X_u_expr.replace("^", "**"), locals=syms)

        # Or expression (e.g. (x>2)|(x<-2)|... )
        if expr.func == sp.Or:
            result = np.zeros(len(pts), dtype=bool)
            for arg in expr.args:
                sub = _eval_single(arg, pts)
                if sub is not None:
                    result |= sub
            return result

        # Single inequality
        sub = _eval_single(expr, pts)
        if sub is not None:
            return sub

    except Exception:
        pass
    return np.zeros(len(pts), dtype=bool)


def verify_symbolic(system: dict, h_str: str, n_samples: int = 300,
                    cond2_frac_tol: float = 0.01, cond2_depth_rel: float = 0.05,
                    cond2_depth_abs: float = 1e-3, cond2_noise: float = 1e-4) -> dict:
    """
    Verify two conditions of barrier function h(x) (paper Proposition 4 / Nagumo Theorem):
      Condition 1: h(x) < 0,  ∀x ∈ X_u
      Condition 2: ḣ(x) >= 0,  ∀x ∈ ∂C  (on the boundary h(x)=0)

    Condition 2 fails only when boundary violations are BOTH widespread and deep:
      - widespread: fraction of violating boundary points > cond2_frac_tol (default 1%)
      - deep:       worst violation below -max(cond2_depth_abs, cond2_depth_rel * typ),
                    where typ = median |ḣ| on the boundary band (scale-free reference)
    This tolerates isolated sampling spikes near kinks/singularities (exp/log/Abs)
    while still rejecting systematic Nagumo leakage. cond2_noise is the numerical
    floor below which a single point counts as a candidate violation.
    """
    if not HAS_SYMPY:
        return {"error": "sympy not installed", "symbolic_valid": None}

    state_vars = system["state_vars"]
    f_exprs = system.get("f_expr")
    if not f_exprs:
        return {"error": "system missing f_expr field", "symbolic_valid": None}

    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return {"error": f"cannot parse h expression: {h_str}", "symbolic_valid": None}

    sym_list = [syms[v] for v in state_vars]

    try:
        f_sym = [sp.sympify(fe.replace("^", "**"),
                            locals={**syms, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
                 for fe in f_exprs]
    except Exception as e:
        return {"error": f"cannot parse f_expr: {e}", "symbolic_valid": None}

    # Compute Lie derivative ḣ = ∇h · f
    grad_h = [sp.diff(expr_h, s) for s in sym_list]
    lie_deriv = sum(g * f for g, f in zip(grad_h, f_sym))
    lie_deriv_simplified = _safe_simplify(lie_deriv, sym_list)
    lie_func = sp.lambdify(sym_list, lie_deriv_simplified, "numpy")

    # Uniformly sample within X_bounds (condition 2 uses only boundary points);
    # if X_u_sample_bounds exists, additionally sample those (used for condition 1)
    rng = np.random.default_rng(42)
    bounds = system.get("X_bounds", [(-3, 3)] * len(state_vars))
    pts_inside = np.column_stack([rng.uniform(lo, hi, n_samples * 20) for lo, hi in bounds])

    xu_bounds = system.get("X_u_sample_bounds")
    if xu_bounds:
        pts_outside = np.column_stack([rng.uniform(lo, hi, n_samples * 20) for lo, hi in xu_bounds])
        pts = np.vstack([pts_inside, pts_outside])
    else:
        pts = pts_inside

    h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")

    try:
        h_vals = np.broadcast_to(np.array(h_func(*pts.T), dtype=float), len(pts)).copy()
        lie_vals = np.broadcast_to(np.array(lie_func(*pts.T), dtype=float), len(pts)).copy()
    except Exception as e:
        return {"error": f"numerical evaluation failed: {e}", "symbolic_valid": None}

    # Determine X_u membership
    in_Xu = _eval_Xu(system, pts)
    not_in_Xu = ~in_Xu

    # Condition 1: h < 0 on X_u
    cond1_ok = True
    cond1_violations = []
    if in_Xu.any():
        h_in_Xu = h_vals[in_Xu]
        max_h_Xu = float(np.max(h_in_Xu))
        cond1_ok = max_h_Xu < 0
        if not cond1_ok:
            viol_pts = pts[in_Xu][h_in_Xu >= 0]
            cond1_violations = [
                {v: round(float(p[i]), 4) for i, v in enumerate(state_vars)}
                for p in viol_pts[:3]
            ]
    else:
        max_h_Xu = None

    # Condition 2 (Nagumo): ḣ >= 0 on ∂C. Sampling can't hit the measure-zero
    # boundary, so use the band 0 <= h < epsilon JUST INSIDE C (one-sided: the
    # h<0 side is outside C where ḣ<0 is legitimate — including it falsely
    # rejects exact Darboux certificates with ḣ = λh).
    # On the band we accept the exponential-CBF relaxation  ḣ >= -C*h  for some
    # C in _CBF_CANDIDATES (comparison lemma: this implies h(t) >= h(0)e^{-Ct},
    # so C is invariant; C=0 is the plain Nagumo check). Needed for first-integral
    # ratio certificates where ḣ ∝ -h*g(x) with g of variable sign.
    h_range = float(np.nanmax(h_vals) - np.nanmin(h_vals))
    epsilon = max(h_range * 0.02, 1e-3)
    on_boundary = not_in_Xu & (h_vals >= -1e-9) & (h_vals < epsilon)

    cond2_ok = True
    cond2_violations = []
    cond2_viol_frac = None
    cbf_constant_used = None
    _CBF_CANDIDATES = (0.0, 1.0, 2.0, 5.0, 10.0, 25.0, 50.0)
    if on_boundary.any():
        c2 = lie_vals[on_boundary]
        hb = h_vals[on_boundary]
        n_b = int(c2.size)
        finite = np.isfinite(c2)
        min_cond2 = float(np.min(c2[finite])) if finite.any() else None
        best = None  # (viol_frac, deep, viol_mask, C)
        for C in _CBF_CANDIDATES:
            relaxed = c2[finite] + C * hb[finite]
            viol_below = relaxed < -cond2_noise
            n_viol = int(viol_below.sum() + (~finite).sum())
            frac = n_viol / n_b
            typ = float(np.median(np.abs(relaxed))) if relaxed.size else 0.0
            worst = float(np.min(relaxed)) if relaxed.size else float("-inf")
            deep = (not finite.all()) or (worst < -max(cond2_depth_abs, cond2_depth_rel * typ))
            # same widespread-AND-deep criterion as before, per candidate C
            ok_C = not (frac > cond2_frac_tol and deep)
            if best is None or frac < best[0]:
                best = (frac, deep, viol_below, C)
            if ok_C:
                cond2_ok = True
                cond2_viol_frac = frac
                cbf_constant_used = C
                break
        else:
            cond2_ok = False
            cond2_viol_frac, _, viol_mask, _ = best
            bad = pts[on_boundary][finite][viol_mask]
            cond2_violations = [
                {v: round(float(p[i]), 4) for i, v in enumerate(state_vars)}
                for p in bad[:3]
            ]
    else:
        min_cond2 = None  # no boundary points sampled, cannot verify

    symbolic_valid = cond1_ok and (cond2_ok if on_boundary.any() else None is None)

    result = {
        "lie_derivative": str(lie_deriv_simplified),
        "boundary_epsilon": round(epsilon, 6),
        "boundary_pts_found": int(on_boundary.sum()),
        "cond1_max_h_in_Xu": round(max_h_Xu, 6) if max_h_Xu is not None else None,
        "cond1_ok": cond1_ok,
        "cond2_min_lie_on_boundary": round(min_cond2, 6) if min_cond2 is not None else None,
        "cond2_cbf_constant": cbf_constant_used,
        "cond2_viol_frac": round(cond2_viol_frac, 4) if cond2_viol_frac is not None else None,
        "cond2_ok": cond2_ok,
        "symbolic_valid": symbolic_valid,
    }
    if cond1_violations:
        result["cond1_violations"] = cond1_violations
    if cond2_violations:
        result["cond2_violations"] = cond2_violations
    return result


def verify_trajectory(system: dict, h_str: str, n_trajs: int = 30, t_span: float = 15.0,
                      time_budget_s: float = 25.0) -> dict:
    """
    Sample initial points from inside C = {h(x) >= 0}, integrate the ODE,
    and check whether trajectories always satisfy h(x(t)) >= 0 (invariant set condition).
    time_budget_s caps total wall time — stiff/high-dim systems otherwise stall
    the whole benchmark; a partial trajectory sample is still a useful filter.
    """
    if not HAS_SCIPY:
        return {"error": "scipy not installed", "trajectory_valid": None}
    if not HAS_SYMPY:
        return {"error": "sympy not installed", "trajectory_valid": None}

    state_vars = system["state_vars"]
    f_exprs = system.get("f_expr")
    if not f_exprs:
        return {"error": "system missing f_expr field", "trajectory_valid": None}

    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return {"error": f"cannot parse h expression: {h_str}", "trajectory_valid": None}

    sym_list = [syms[v] for v in state_vars]

    try:
        f_sym = [sp.sympify(fe.replace("^", "**"),
                            locals={**syms, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
                 for fe in f_exprs]
    except Exception as e:
        return {"error": f"cannot parse f_expr: {e}", "trajectory_valid": None}

    h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")
    f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]

    # Sample within X_bounds, filter points with h(x0) >= 0 (inside C)
    rng = np.random.default_rng(0)
    bounds = system.get("X_bounds", [(-3, 3)] * len(state_vars))
    candidates = np.column_stack([rng.uniform(lo, hi, n_trajs * 50) for lo, hi in bounds])

    try:
        h_cands = np.array(h_func(*candidates.T), dtype=float)
    except Exception as e:
        return {"error": f"h numerical evaluation failed: {e}", "trajectory_valid": None}

    inside_C = candidates[h_cands >= 0]
    if len(inside_C) == 0:
        return {
            "n_trajs": 0,
            "trajectory_valid": None,
            "note": "No initial points satisfying h>=0 found within X_bounds; invariant set C may be empty",
        }

    init_pts = inside_C[:n_trajs]
    min_h_overall = float("inf")
    violations = []
    n_success = 0
    _t0 = time.time()

    for x0 in init_pts:
        if time.time() - _t0 > time_budget_s:
            break
        try:
            deadline = min(time.time() + 5.0, _t0 + time_budget_s)
            sol = solve_ivp(_budgeted_rhs(f_funcs, deadline), [0, t_span], x0.tolist(),
                            max_step=0.05, dense_output=False, rtol=1e-6, atol=1e-8)
            if not sol.success:
                continue
            n_success += 1
            h_traj = np.array(h_func(*sol.y), dtype=float)
            min_h = float(np.min(h_traj))
            if min_h < min_h_overall:
                min_h_overall = min_h
            if min_h < -1e-3:  # trajectory escapes C (h becomes negative)
                t_viol = float(sol.t[np.argmin(h_traj)])
                violations.append({
                    "x0": {v: round(float(x0[i]), 4) for i, v in enumerate(state_vars)},
                    "min_h": round(min_h, 4),
                    "t_violation": round(t_viol, 3),
                })
        except Exception:
            continue

    if n_success == 0:
        return {"n_trajs": 0, "trajectory_valid": None, "note": "All trajectory integrations failed"}

    trajectory_valid = len(violations) == 0 and min_h_overall >= -1e-3

    result = {
        "n_trajs": len(init_pts),
        "t_span": t_span,
        "min_h_on_trajs": round(float(min_h_overall), 6) if min_h_overall < np.inf else None,
        "trajectory_valid": trajectory_valid,
    }
    if violations:
        result["violations"] = violations[:3]
    return result


# ─────────────────────────────────────────────
# 3b. Discrete-time + Lyapunov verification (v5)
#
# System dict flags consumed here (set by dataset_loader):
#   discrete   : bool — dynamics are a map x+ = f(x) instead of an ODE
#   task_type  : "barrier" (default) | "lyapunov"
#   equilibrium: list[float] | None — x* for Lyapunov tasks (default: origin)
#   psd_ok     : bool — accept positive SEMIdefinite V (equilibrium sets,
#                first integrals, consensus subspaces)
# ─────────────────────────────────────────────
def _parse_system_f(system: dict, syms: dict):
    """Parse system f_expr into sympy expressions (shared by all verifiers)."""
    extra = {"exp": sp.exp, "sin": sp.sin, "cos": sp.cos, "tan": sp.tan,
             "log": sp.log, "sqrt": sp.sqrt, "Abs": sp.Abs,
             "sinh": sp.sinh, "cosh": sp.cosh, "tanh": sp.tanh,
             "asinh": sp.asinh, "atanh": sp.atanh, "atan": sp.atan,
             "Min": sp.Min, "Max": sp.Max}
    return [sp.sympify(fe.replace("^", "**"), locals={**syms, **extra})
            for fe in system["f_expr"]]


def _sample_domain(system: dict, n: int, seed: int = 42) -> np.ndarray:
    rng = np.random.default_rng(seed)
    bounds = system.get("X_bounds", [(-3, 3)] * len(system["state_vars"]))
    pts = np.column_stack([rng.uniform(lo, hi, n) for lo, hi in bounds])
    if system.get("simplex"):
        pts = np.abs(pts)
        pts = pts / np.maximum(pts.sum(axis=1, keepdims=True), 1e-12)
    return pts


def verify_symbolic_discrete(system: dict, h_str: str, n_samples: int = 6000,
                             frac_tol: float = 0.01, depth_abs: float = 1e-3) -> dict:
    """Discrete barrier check: Cond1: h<0 on X_u. Cond2: h(f(x)) >= 0 for ALL x
    with h(x) >= 0 (one-step invariance of C — the whole set, not just the
    boundary, since discrete trajectories jump)."""
    if not HAS_SYMPY:
        return {"error": "sympy not installed", "symbolic_valid": None}
    state_vars = system["state_vars"]
    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return {"error": f"cannot parse h expression: {h_str}", "symbolic_valid": None}
    sym_list = [syms[v] for v in state_vars]
    try:
        f_sym = _parse_system_f(system, syms)
    except Exception as e:
        return {"error": f"cannot parse f_expr: {e}", "symbolic_valid": None}

    h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")
    f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]

    pts = _sample_domain(system, n_samples)
    xu_bounds = system.get("X_u_sample_bounds")
    if xu_bounds:
        rng = np.random.default_rng(43)
        pts = np.vstack([pts, np.column_stack(
            [rng.uniform(lo, hi, n_samples // 2) for lo, hi in xu_bounds])])
    try:
        h_vals = np.broadcast_to(np.array(h_func(*pts.T), dtype=float), len(pts)).copy()
        nxt = np.column_stack([np.broadcast_to(np.array(ff(*pts.T), dtype=float), len(pts))
                               for ff in f_funcs])
        h_next = np.broadcast_to(np.array(h_func(*nxt.T), dtype=float), len(pts)).copy()
    except Exception as e:
        return {"error": f"numerical evaluation failed: {e}", "symbolic_valid": None}

    in_Xu = _eval_Xu(system, pts)
    # Cond1: h < 0 on X_u
    cond1_ok, max_h_Xu, cond1_violations = True, None, []
    if in_Xu.any():
        h_in = h_vals[in_Xu]
        max_h_Xu = float(np.max(h_in))
        cond1_ok = max_h_Xu < 0
        if not cond1_ok:
            bad = pts[in_Xu][h_in >= 0]
            cond1_violations = [{v: round(float(p[i]), 4) for i, v in enumerate(state_vars)}
                                for p in bad[:3]]
    # Cond2: x in C (h>=0, not in Xu) => h(f(x)) >= 0
    in_C = (h_vals >= 0) & ~in_Xu
    cond2_ok, min_h_next, cond2_violations, viol_frac = True, None, [], None
    if in_C.any():
        hn = h_next[in_C]
        finite = np.isfinite(hn)
        viol = (hn[finite] < -depth_abs)
        n_viol = int(viol.sum() + (~finite).sum())
        viol_frac = n_viol / int(in_C.sum())
        min_h_next = float(np.min(hn[finite])) if finite.any() else None
        cond2_ok = n_viol == 0 or (viol_frac <= frac_tol and
                                   (min_h_next is None or min_h_next > -10 * depth_abs))
        if not cond2_ok:
            bad = pts[in_C][finite][viol]
            cond2_violations = [{v: round(float(p[i]), 4) for i, v in enumerate(state_vars)}
                                for p in bad[:3]]
    return {
        "mode": "discrete-barrier",
        "step_map_next_h_min": round(min_h_next, 6) if min_h_next is not None else None,
        "cond1_max_h_in_Xu": round(max_h_Xu, 6) if max_h_Xu is not None else None,
        "cond1_ok": cond1_ok,
        "cond2_viol_frac": round(viol_frac, 4) if viol_frac is not None else None,
        "cond2_ok": cond2_ok,
        "symbolic_valid": cond1_ok and cond2_ok,
        **({"cond1_violations": cond1_violations} if cond1_violations else {}),
        **({"cond2_violations": cond2_violations} if cond2_violations else {}),
    }


def verify_lyapunov(system: dict, V_str: str, n_samples: int = 6000,
                    decr_frac_tol: float = 0.01, decr_depth_abs: float = 1e-3,
                    pos_eps: float = 1e-2) -> dict:
    """Lyapunov check (continuous: Vdot = grad V . f <= 0; discrete: V(f(x)) - V(x) <= 0)
    plus positivity: V(x*) = 0 and V > 0 away from x* (V is auto-shifted by V(x*),
    so certificates given up to an additive constant still pass).
    psd_ok=True relaxes positivity to V >= 0 (first integrals / equilibrium sets)."""
    if not HAS_SYMPY:
        return {"error": "sympy not installed", "symbolic_valid": None}
    state_vars = system["state_vars"]
    expr_V, syms = _parse_B_expr(V_str, state_vars)
    if expr_V is None:
        return {"error": f"cannot parse V expression: {V_str}", "symbolic_valid": None}
    sym_list = [syms[v] for v in state_vars]
    try:
        f_sym = _parse_system_f(system, syms)
    except Exception as e:
        return {"error": f"cannot parse f_expr: {e}", "symbolic_valid": None}

    x_star = system.get("equilibrium") or [0.0] * len(state_vars)
    V_func = sp.lambdify(sym_list, expr_V.doit(), "numpy")
    try:
        V0 = float(V_func(*x_star))
    except Exception as e:
        return {"error": f"V(x*) evaluation failed at {x_star}: {e}", "symbolic_valid": None}
    if not np.isfinite(V0):
        return {"error": f"V(x*) is not finite at x*={x_star}", "symbolic_valid": None}

    pts = _sample_domain(system, n_samples)
    try:
        V_vals = np.broadcast_to(np.array(V_func(*pts.T), dtype=float), len(pts)).copy() - V0
    except Exception as e:
        return {"error": f"numerical evaluation failed: {e}", "symbolic_valid": None}

    # decrease condition
    if system.get("discrete"):
        f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]
        nxt = np.column_stack([np.broadcast_to(np.array(ff(*pts.T), dtype=float), len(pts))
                               for ff in f_funcs])
        decr_vals = (np.broadcast_to(np.array(V_func(*nxt.T), dtype=float), len(pts)).copy()
                     - V0) - V_vals
        decr_label = "Delta V = V(f(x)) - V(x)"
        decr_expr_str = "V(f(x)) - V(x)"
    else:
        grad_V = [sp.diff(expr_V, s) for s in sym_list]
        vdot = _safe_simplify(sum(g * f for g, f in zip(grad_V, f_sym)), sym_list)
        vdot_func = sp.lambdify(sym_list, vdot, "numpy")
        decr_vals = np.broadcast_to(np.array(vdot_func(*pts.T), dtype=float), len(pts)).copy()
        decr_label = "Vdot = grad V . f"
        decr_expr_str = str(vdot)

    finite = np.isfinite(decr_vals)
    viol = decr_vals[finite] > decr_depth_abs
    viol_frac = (int(viol.sum()) + int((~finite).sum())) / len(pts)
    max_decr = float(np.max(decr_vals[finite])) if finite.any() else None
    decrease_ok = viol_frac <= decr_frac_tol and (max_decr is None or max_decr <= 10 * decr_depth_abs)
    decr_violations = []
    if not decrease_ok:
        bad = pts[finite][viol]
        decr_violations = [{v: round(float(p[i]), 4) for i, v in enumerate(state_vars)}
                           for p in bad[:3]]

    # positivity: V - V(x*) > 0 away from x* (or >= 0 if psd_ok)
    away = np.linalg.norm(pts - np.array(x_star, dtype=float), axis=1) > pos_eps
    Va = V_vals[away & np.isfinite(V_vals)]
    min_V_away = float(np.min(Va)) if Va.size else None
    if system.get("psd_ok"):
        positivity_ok = min_V_away is None or min_V_away >= -1e-6
    else:
        positivity_ok = min_V_away is not None and min_V_away > 0
    pos_violations = []
    if not positivity_ok and Va.size:
        bad = pts[away & np.isfinite(V_vals)][Va <= 0]
        pos_violations = [{v: round(float(p[i]), 4) for i, v in enumerate(state_vars)}
                          for p in bad[:3]]

    return {
        "mode": "discrete-lyapunov" if system.get("discrete") else "continuous-lyapunov",
        "decrease_quantity": decr_label,
        "lie_derivative": decr_expr_str[:500],
        "V_at_equilibrium_shift": round(V0, 6),
        "decrease_max": round(max_decr, 6) if max_decr is not None else None,
        "decrease_viol_frac": round(viol_frac, 4),
        "decrease_ok": decrease_ok,
        "min_V_away_from_eq": round(min_V_away, 6) if min_V_away is not None else None,
        "positivity_ok": positivity_ok,
        "symbolic_valid": decrease_ok and positivity_ok,
        **({"decrease_violations": decr_violations} if decr_violations else {}),
        **({"positivity_violations": pos_violations} if pos_violations else {}),
    }


def verify_trajectory_discrete(system: dict, expr_str: str, n_trajs: int = 30,
                               n_steps: int = 60) -> dict:
    """Iterate the map. Barrier task: h(x_k) must stay >= 0 from starts in C.
    Lyapunov task: V(x_k) must be non-increasing from domain starts."""
    if not HAS_SYMPY:
        return {"error": "sympy not installed", "trajectory_valid": None}
    state_vars = system["state_vars"]
    task = system.get("task_type", "barrier")
    expr, syms = _parse_B_expr(expr_str, state_vars)
    if expr is None:
        return {"error": f"cannot parse expression: {expr_str}", "trajectory_valid": None}
    sym_list = [syms[v] for v in state_vars]
    try:
        f_sym = _parse_system_f(system, syms)
    except Exception as e:
        return {"error": f"cannot parse f_expr: {e}", "trajectory_valid": None}
    g_func = sp.lambdify(sym_list, expr.doit(), "numpy")
    f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]

    x_star = system.get("equilibrium") or [0.0] * len(state_vars)
    try:
        V0 = float(g_func(*x_star)) if task == "lyapunov" else 0.0
    except Exception:
        V0 = 0.0

    cands = _sample_domain(system, n_trajs * 50, seed=0)
    try:
        g_c = np.array([float(g_func(*p)) for p in cands])
    except Exception as e:
        return {"error": f"evaluation failed: {e}", "trajectory_valid": None}
    if task == "barrier":
        starts = cands[g_c >= 0][:n_trajs]
        if len(starts) == 0:
            return {"n_trajs": 0, "trajectory_valid": None,
                    "note": "no starts with h>=0 found; C may be empty"}
    else:
        starts = cands[np.isfinite(g_c)][:n_trajs]

    violations = []
    for x0 in starts:
        x = np.array(x0, dtype=float)
        prev = float(g_func(*x)) - V0
        for k in range(n_steps):
            try:
                x = np.array([float(ff(*x)) for ff in f_funcs])
                cur = float(g_func(*x)) - V0
            except Exception:
                break
            if not np.isfinite(cur):
                break
            if task == "barrier" and cur < -1e-6:
                violations.append({"x0": {v: round(float(x0[i]), 4) for i, v in enumerate(state_vars)},
                                   "step": k + 1, "value": round(cur, 6)})
                break
            if task == "lyapunov" and cur > prev + 1e-6:
                violations.append({"x0": {v: round(float(x0[i]), 4) for i, v in enumerate(state_vars)},
                                   "step": k + 1, "increase": round(cur - prev, 6)})
                break
            prev = cur
    return {"n_trajs": len(starts), "n_steps": n_steps,
            "trajectory_valid": len(violations) == 0,
            **({"violations": violations[:3]} if violations else {})}


def verify_trajectory_lyapunov(system: dict, V_str: str, n_trajs: int = 25,
                               t_span: float = 12.0) -> dict:
    """Continuous Lyapunov trajectory check: V(x(t)) non-increasing along solutions."""
    if not (HAS_SCIPY and HAS_SYMPY):
        return {"error": "scipy/sympy not installed", "trajectory_valid": None}
    state_vars = system["state_vars"]
    expr_V, syms = _parse_B_expr(V_str, state_vars)
    if expr_V is None:
        return {"error": f"cannot parse V: {V_str}", "trajectory_valid": None}
    sym_list = [syms[v] for v in state_vars]
    try:
        f_sym = _parse_system_f(system, syms)
    except Exception as e:
        return {"error": f"cannot parse f_expr: {e}", "trajectory_valid": None}
    V_func = sp.lambdify(sym_list, expr_V.doit(), "numpy")
    f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]

    starts = _sample_domain(system, n_trajs * 10, seed=5)[:n_trajs]
    violations, n_ok = [], 0
    _t0 = time.time()
    for x0 in starts:
        if time.time() - _t0 > 25.0:   # wall-time budget, same rationale as verify_trajectory
            break
        try:
            deadline = min(time.time() + 5.0, _t0 + 25.0)
            sol = solve_ivp(_budgeted_rhs(f_funcs, deadline), [0, t_span], x0.tolist(),
                            max_step=0.05, rtol=1e-6, atol=1e-8)
            if not sol.success:
                continue
            n_ok += 1
            v_traj = np.array([float(V_func(*sol.y[:, i])) for i in range(sol.y.shape[1])])
            incr = np.diff(v_traj)
            worst = float(np.max(incr)) if incr.size else 0.0
            if worst > 1e-3 * max(1.0, float(np.max(np.abs(v_traj)))):
                violations.append({"x0": {v: round(float(x0[i]), 4) for i, v in enumerate(state_vars)},
                                   "max_increase": round(worst, 6)})
        except Exception:
            continue
    if n_ok == 0:
        return {"n_trajs": 0, "trajectory_valid": None, "note": "all integrations failed"}
    return {"n_trajs": n_ok, "trajectory_valid": len(violations) == 0,
            **({"violations": violations[:3]} if violations else {})}


def parse_json_response(text: str) -> dict:
    """Try to extract JSON from LLM output with error tolerance"""
    # Strip possible markdown code blocks
    text = text.strip()
    if text.startswith("```"):
        lines = text.split("\n")
        text = "\n".join(lines[1:-1]) if lines[-1].strip() == "```" else "\n".join(lines[1:])
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        # Try to find the first { ... } block
        start = text.find("{")
        end = text.rfind("}") + 1
        if start != -1 and end > start:
            try:
                return json.loads(text[start:end])
            except json.JSONDecodeError:
                pass
    return {"raw": text}


# ─────────────────────────────────────────────
# 4. Visualization
# ─────────────────────────────────────────────
def plot_barrier(system: dict, system_key: str, h_str: str, output_prefix: str):
    """
    Plot barrier function visualization:
      - State domain X (dashed rectangle boundary)
      - Unsafe set X_u (red shading)
      - Invariant set C = {h(x) >= 0} (green shading)
      - Sample trajectories (blue, starting from inside C)
    2D systems saved as PNG; 3D systems (Lorenz) plot three projection subplots.
    """
    if not HAS_SYMPY:
        print("Warning: visualization requires sympy, skipping.")
        return
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.patches import Patch, Rectangle
        from matplotlib.lines import Line2D
    except ImportError:
        print("Warning: matplotlib not installed, skipping visualization.")
        return

    state_vars = system["state_vars"]
    bounds     = system["X_bounds"]
    n_dim      = len(state_vars)

    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        print("Warning: cannot parse h expression, skipping visualization.")
        return
    sym_list = [syms[v] for v in state_vars]
    h_func   = sp.lambdify(sym_list, expr_h, "numpy")

    # ── Trajectory generation (shared) ──
    trajs = []
    if HAS_SCIPY and system.get("f_expr"):
        try:
            f_sym   = [sp.sympify(fe.replace("^", "**"),
                                  locals={**{v: syms[v] for v in state_vars},
                                          "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
                       for fe in system["f_expr"]]
            f_funcs = [sp.lambdify(sym_list, fi, "numpy") for fi in f_sym]
            rng  = np.random.default_rng(123)
            cands = np.column_stack([rng.uniform(lo, hi, 2000) for lo, hi in bounds])
            try:
                h_c = np.array(h_func(*cands.T), dtype=float)
                inside = cands[h_c >= 0][:20]
            except Exception:
                inside = []
            for x0 in inside:
                try:
                    sol = solve_ivp(_budgeted_rhs(f_funcs, time.time() + 5.0), [0, 12],
                                    x0.tolist(), max_step=0.05, rtol=1e-5, atol=1e-7)
                    if sol.success:
                        trajs.append(sol.y)
                except Exception:
                    pass
        except Exception:
            pass

    # ── 2D plot ──
    if n_dim == 2:
        (x1_lo, x1_hi), (x2_lo, x2_hi) = bounds
        N  = 400
        x1a = np.linspace(x1_lo, x1_hi, N)
        x2a = np.linspace(x2_lo, x2_hi, N)
        X1, X2 = np.meshgrid(x1a, x2a)
        try:
            H = np.array(h_func(X1, X2), dtype=float)
        except Exception as e:
            print(f"Warning: h grid evaluation failed: {e}, skipping visualization.")
            return

        fig, ax = plt.subplots(figsize=(8, 7))

        # Invariant set C = {h >= 0}
        ax.contourf(X1, X2, H, levels=[0, np.nanmax(H) + 1], colors=["#90EE90"], alpha=0.55)
        ax.contour( X1, X2, H, levels=[0], colors=["green"], linewidths=2)

        # Unsafe set X_u
        xu_expr = system.get("X_u_expr", "")
        if xu_expr and xu_expr not in ("X^C", ""):
            try:
                xu_sym = sp.sympify(xu_expr.replace("^", "**"),
                                    locals={v: syms[v] for v in state_vars})
                if hasattr(xu_sym, "lhs") and hasattr(xu_sym, "rhs"):
                    d_expr = xu_sym.lhs - xu_sym.rhs
                    d_func = sp.lambdify(sym_list, d_expr, "numpy")
                    D = np.array(d_func(X1, X2), dtype=float)
                    rel = type(xu_sym).__name__
                    mask = D <= 0 if rel in ("Le", "Lt", "LessThan", "StrictLessThan") else D >= 0
                    Xu_z = np.where(mask, 1.0, 0.0)
                    ax.contourf(X1, X2, Xu_z, levels=[0.5, 1.5], colors=["#FFB6C1"], alpha=0.6)
                    ax.contour( X1, X2, D, levels=[0], colors=["red"], linewidths=1.5)
            except Exception:
                pass

        # State domain border
        rect = Rectangle((x1_lo, x2_lo), x1_hi - x1_lo, x2_hi - x2_lo,
                          linewidth=2, edgecolor="navy", facecolor="none", linestyle="--")
        ax.add_patch(rect)

        # Trajectories
        for traj in trajs:
            ax.plot(traj[0], traj[1], "b-", alpha=0.35, linewidth=0.9)
            ax.plot(traj[0, 0], traj[1, 0], "b.", markersize=4)

        ax.set_xlim(x1_lo, x1_hi)
        ax.set_ylim(x2_lo, x2_hi)
        ax.set_xlabel(state_vars[0], fontsize=12)
        ax.set_ylabel(state_vars[1], fontsize=12)
        h_display = h_str if len(h_str) < 60 else h_str[:57] + "..."
        ax.set_title(f"{system_key}\nh(x) = {h_display}", fontsize=10)
        ax.set_aspect("equal")
        ax.grid(True, alpha=0.3)
        legend_elems = [
            Patch(facecolor="#90EE90", alpha=0.55, edgecolor="green", label="Invariant set C = {h>=0}"),
            Patch(facecolor="#FFB6C1", alpha=0.6,  edgecolor="red",   label="Unsafe set Xu"),
            Line2D([0], [0], color="navy",  linestyle="--", label="Domain X"),
            Line2D([0], [0], color="blue",  alpha=0.5,      label="Sample trajectories"),
        ]
        ax.legend(handles=legend_elems, loc="upper right", fontsize=9)

    # ── 3D plot (Lorenz etc.) ──
    elif n_dim == 3:
        from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
        (x_lo, x_hi), (y_lo, y_hi), (z_lo, z_hi) = bounds

        fig = plt.figure(figsize=(14, 5))
        proj_pairs = [(0, 1, state_vars[0], state_vars[1]),
                      (0, 2, state_vars[0], state_vars[2]),
                      (1, 2, state_vars[1], state_vars[2])]
        bnd2 = [bounds[0], bounds[1], bounds[2]]

        for idx, (ia, ib, la, lb) in enumerate(proj_pairs, 1):
            ax = fig.add_subplot(1, 3, idx)
            lo_a, hi_a = bnd2[ia]
            lo_b, hi_b = bnd2[ib]
            N = 300
            aa = np.linspace(lo_a, hi_a, N)
            bb = np.linspace(lo_b, hi_b, N)
            A, B = np.meshgrid(aa, bb)
            # Project at zero slice of the third dimension
            ic = 3 - ia - ib  # remaining dimension index
            mid_c = (bnd2[ic][0] + bnd2[ic][1]) / 2
            coords = [None, None, None]
            coords[ia] = A
            coords[ib] = B
            coords[ic] = np.full_like(A, mid_c)
            try:
                H2 = np.array(h_func(*coords), dtype=float)
                ax.contourf(A, B, H2, levels=[0, np.nanmax(H2) + 1],
                             colors=["#90EE90"], alpha=0.55)
                ax.contour( A, B, H2, levels=[0], colors=["green"], linewidths=1.5)
            except Exception:
                pass

            rect = Rectangle((lo_a, lo_b), hi_a - lo_a, hi_b - lo_b,
                              linewidth=1.5, edgecolor="navy", facecolor="none", linestyle="--")
            ax.add_patch(rect)

            for traj in trajs:
                ax.plot(traj[ia], traj[ib], "b-", alpha=0.3, linewidth=0.8)
                ax.plot(traj[ia, 0], traj[ib, 0], "b.", markersize=3)

            ax.set_xlim(lo_a, hi_a)
            ax.set_ylim(lo_b, hi_b)
            ax.set_xlabel(la, fontsize=11)
            ax.set_ylabel(lb, fontsize=11)
            ax.set_aspect("equal")
            ax.grid(True, alpha=0.3)

        h_display = h_str if len(h_str) < 80 else h_str[:77] + "..."
        fig.suptitle(f"{system_key}\nh(x) = {h_display}", fontsize=10)

    else:
        print(f"Warning: visualization not supported for {n_dim}D systems, skipping.")
        return

    save_path = f"{output_prefix}.png"
    plt.tight_layout()
    plt.savefig(save_path, dpi=150, bbox_inches="tight")
    plt.close()
    print(f"Visualization saved: {save_path}")


# ─────────────────────────────────────────────
# Counterexample cache
# ─────────────────────────────────────────────
def _pt_to_array(pt: dict, state_vars: list) -> np.ndarray:
    return np.array([float(pt[v]) for v in state_vars])


def precheck_cache(system: dict, h_str: str, cache: dict) -> list:
    """Re-check a new h against previously found violation points. Zero tokens.
    Returns a list of human-readable failure strings (empty = pass)."""
    if not HAS_SYMPY:
        return []
    state_vars = system["state_vars"]
    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return [f"h expression unparseable: {h_str}"]
    sym_list = [syms[v] for v in state_vars]
    try:
        h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")
    except Exception as e:
        return [f"h cannot be lambdified: {e}"]

    fails = []
    for pt in cache.get("xu_points", []):
        x = _pt_to_array(pt, state_vars)
        try:
            hv = float(h_func(*x))
        except Exception:
            continue
        if hv >= 0:
            fails.append(f"Condition 1 fails at known unsafe point {pt}: h = {hv:.5g} (must be < 0)")

    # escape points: only relevant if the new C still contains them
    if HAS_SCIPY and system.get("f_expr") and cache.get("escape_points"):
        try:
            f_sym = [sp.sympify(fe.replace("^", "**"),
                                locals={**syms, "exp": sp.exp, "sin": sp.sin, "cos": sp.cos})
                     for fe in system["f_expr"]]
            f_funcs = [sp.lambdify(sym_list, fi.doit(), "numpy") for fi in f_sym]
        except Exception:
            return fails

        for pt in cache.get("escape_points", [])[:5]:
            x0 = _pt_to_array(pt, state_vars)
            try:
                if float(h_func(*x0)) < 0:
                    continue  # point no longer inside C, not a counterexample for new h
                sol = solve_ivp(_budgeted_rhs(f_funcs, time.time() + 5.0), [0, 15.0],
                                x0.tolist(), max_step=0.05, rtol=1e-6, atol=1e-8)
                if not sol.success:
                    continue
                h_traj = np.array(h_func(*sol.y), dtype=float)
                if float(np.min(h_traj)) < -1e-3:
                    fails.append(
                        f"Known escaping trajectory still escapes: x0={pt}, min h(x(t)) = {float(np.min(h_traj)):.5g}")
            except Exception:
                continue
    return fails


def harvest_cache(cache: dict, sym_result: dict, traj_result: dict):
    for pt in sym_result.get("cond1_violations", []) or []:
        if pt not in cache["xu_points"]:
            cache["xu_points"].append(pt)
    for v in (traj_result.get("violations", []) or []):
        pt = v.get("x0")
        if pt and pt not in cache["escape_points"]:
            cache["escape_points"].append(pt)


# ─────────────────────────────────────────────
# Non-triviality guard: reject empty / degenerate invariant sets
# ─────────────────────────────────────────────
def nontrivial_C_check(system: dict, h_str: str, n: int = 5000, min_pts: int = 5) -> str:
    """Reject barriers whose invariant set C = {x in X : h(x) >= 0} is empty or
    near-empty inside the domain (e.g. h = -1). Conditions hold vacuously on an
    empty set, so such 'solutions' are degenerate cheats. Returns a failure string
    (empty = OK)."""
    if not HAS_SYMPY:
        return ""
    state_vars = system["state_vars"]
    expr_h, syms = _parse_B_expr(h_str, state_vars)
    if expr_h is None:
        return ""  # parse failure is handled elsewhere
    sym_list = [syms[v] for v in state_vars]
    try:
        h_func = sp.lambdify(sym_list, expr_h.doit(), "numpy")
    except Exception:
        return ""
    bounds = system.get("X_bounds", [(-3, 3)] * len(state_vars))
    rng = np.random.default_rng(7)
    pts = np.column_stack([rng.uniform(lo, hi, n) for lo, hi in bounds])
    try:
        h_vals = np.broadcast_to(np.array(h_func(*pts.T), dtype=float), n)
    except Exception:
        return ""
    inside = int(np.count_nonzero(np.isfinite(h_vals) & (h_vals >= 0)))
    if inside < min_pts:
        return (f"Invariant set C = {{x in X : h(x) >= 0}} is empty/degenerate: only "
                f"{inside}/{n} sampled domain points satisfy h(x) >= 0. The conditions "
                f"hold only vacuously — propose a NON-trivial h whose C has real volume "
                f"inside the domain (h must be positive on a meaningful region).")
    return ""


# ─────────────────────────────────────────────
# Local verification bundle (runs BEFORE the Refuter)
# ─────────────────────────────────────────────
def local_verify(system: dict, h_str: str, cache: dict) -> dict:
    """Task-aware local verification bundle. Dispatch:
      task_type=barrier  + continuous -> verify_symbolic + verify_trajectory
      task_type=barrier  + discrete   -> verify_symbolic_discrete + verify_trajectory_discrete
      task_type=lyapunov + continuous -> verify_lyapunov + verify_trajectory_lyapunov
      task_type=lyapunov + discrete   -> verify_lyapunov + verify_trajectory_discrete"""
    out = {"cache_fails": [], "symbolic": {}, "trajectory": {}, "passed": False, "feedback": ""}
    task = system.get("task_type", "barrier")
    discrete = bool(system.get("discrete"))

    out["cache_fails"] = precheck_cache(system, h_str, cache) if (task == "barrier" and not discrete) else []
    if task == "barrier":
        trivial_fail = nontrivial_C_check(system, h_str)
        if trivial_fail:
            out["cache_fails"].append(trivial_fail)

    sym_result, traj_result = {}, {}
    sym_ok = traj_ok = None
    if HAS_SYMPY and system.get("f_expr"):
        _t = time.time()
        if task == "lyapunov":
            sym_result = verify_lyapunov(system, h_str)
        elif discrete:
            sym_result = verify_symbolic_discrete(system, h_str)
        else:
            sym_result = verify_symbolic(system, h_str)
        sym_result["elapsed_s"] = round(time.time() - _t, 3)
        sym_ok = sym_result.get("symbolic_valid")
    if HAS_SYMPY and system.get("f_expr"):
        _t = time.time()
        if discrete:
            traj_result = verify_trajectory_discrete(system, h_str)
        elif task == "lyapunov":
            traj_result = verify_trajectory_lyapunov(system, h_str) if HAS_SCIPY else {}
        else:
            traj_result = verify_trajectory(system, h_str) if HAS_SCIPY else {}
        if traj_result:
            traj_result["elapsed_s"] = round(time.time() - _t, 3)
            traj_ok = traj_result.get("trajectory_valid")

    out["symbolic"] = sym_result
    out["trajectory"] = traj_result
    if task == "barrier" and not discrete:
        harvest_cache(cache, sym_result, traj_result)

    out["passed"] = (not out["cache_fails"]) and (sym_ok is not False) and (traj_ok is not False)
    if out["passed"]:
        return out

    parts = list(out["cache_fails"])
    if sym_ok is False:
        if task == "lyapunov":
            if not sym_result.get("positivity_ok", True):
                parts.append(
                    f"Positivity failed: min (V - V(x*)) away from equilibrium = "
                    f"{sym_result.get('min_V_away_from_eq')} (must be > 0).")
                if sym_result.get("positivity_violations"):
                    parts.append(f"Violation points: {sym_result['positivity_violations']}")
            if not sym_result.get("decrease_ok", True):
                parts.append(
                    f"Decrease condition failed: max {sym_result.get('decrease_quantity')} = "
                    f"{sym_result.get('decrease_max')} (must be <= 0). "
                    f"Expression: {sym_result.get('lie_derivative')}")
                if sym_result.get("decrease_violations"):
                    parts.append(f"Violation points: {sym_result['decrease_violations']}")
        else:
            if not sym_result.get("cond1_ok", True):
                parts.append(f"Condition 1 failed: max h on X_u = {sym_result.get('cond1_max_h_in_Xu')} (must be < 0).")
                if sym_result.get("cond1_violations"):
                    parts.append(f"Violation points: {sym_result['cond1_violations']}")
            if not sym_result.get("cond2_ok", True):
                if discrete:
                    parts.append(
                        f"Condition 2 (one-step invariance) failed: min h(f(x)) over C = "
                        f"{sym_result.get('step_map_next_h_min')} (must be >= 0).")
                else:
                    parts.append(
                        f"Condition 2 (Nagumo) failed: min hdot on boundary = {sym_result.get('cond2_min_lie_on_boundary')} "
                        f"(must be >= 0). Lie derivative = {sym_result.get('lie_derivative')}")
                if sym_result.get("cond2_violations"):
                    parts.append(f"Violation points: {sym_result['cond2_violations']}")
    if traj_ok is False:
        if discrete:
            parts.append("Iterated-map check failed:")
            for v in (traj_result.get("violations") or [])[:2]:
                parts.append(f"  {v}")
        elif task == "lyapunov":
            parts.append("Trajectory check failed: V increased along a solution:")
            for v in (traj_result.get("violations") or [])[:2]:
                parts.append(f"  {v}")
        else:
            parts.append(
                f"Trajectory check failed: min h along trajectories from inside C = {traj_result.get('min_h_on_trajs')} "
                f"(must stay >= 0).")
            for v in (traj_result.get("violations") or [])[:2]:
                parts.append(f"  escaping trajectory: x0={v['x0']}, min h={v['min_h']} at t={v['t_violation']}")
    if sym_result.get("error"):
        parts.append(f"Symbolic verification error: {sym_result['error']}")
    out["feedback"] = "\n".join(parts)
    return out
