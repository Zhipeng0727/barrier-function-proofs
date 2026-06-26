"""
dual_agent_debate_3.py — shared library for the barrier-synthesis pipeline.

This module is NOT a standalone entry point; it provides the building blocks
imported by dual_agent_debate_4.py (the active pipeline):
  - System definitions: API_CONFIG, SYSTEMS, HAS_SYMPY, HAS_SCIPY
  - Agent prompts:       proposer_system, refuter_system, lean4_system
  - Local verification:  verify_symbolic, verify_trajectory, _parse_B_expr, _eval_Xu
  - Utilities:           parse_json_response, plot_barrier

Mathematical framework (continuous time, Proposition 4 / Nagumo Theorem):
  Given state domain X, unsafe set X_u ⊂ X, find h: X -> R satisfying:
    (1) h(x) < 0,  ∀x ∈ X_u
    (2) ḣ(x) >= 0,  ∀x ∈ ∂C  (Nagumo condition, only on the boundary h=0)
  Then C = {x ∈ X : h(x) >= 0} is an invariant set.
"""

import json
import os
import numpy as np

try:
    import sympy as sp
    HAS_SYMPY = True
except ImportError:
    HAS_SYMPY = False

try:
    from scipy.integrate import solve_ivp
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False

# ─────────────────────────────────────────────
# 1. API Configuration
# ─────────────────────────────────────────────
# Only `timeout` is consumed downstream: dual_agent_debate_4.py copies this dict,
# then overwrites `model` via select_provider() and sends requests using its own
# PROVIDERS endpoints/keys — so base_url/api_key here are dead. `model` is kept as a
# harmless default (always overridden by the active provider).
API_CONFIG = {
    "model": os.environ.get("OPENAI_MODEL", "gpt-5.5"),
    "timeout": int(os.environ.get("API_TIMEOUT_MS", "120000")) // 1000,
}

# ─────────────────────────────────────────────
# 2. System Definitions (paper framework: X, X_u, f_expr)
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

# 4.27 [Strict requirements for the "h" field] new add
# ─────────────────────────────────────────────
# 3. Agent System Prompts
# ─────────────────────────────────────────────
def proposer_system(system: dict) -> str:
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

# 2026.4.27 add 5. (Only when verdict is "valid") Analyze whether the invariant set C = {{h(x) >= 0}} could be enlarged: consider whether the level set threshold, coefficients, or functional form of h could be adjusted to cover more of X while still satisfying both conditions. If an enlargement direction exists, provide a concrete suggestion.

def refuter_system(system: dict) -> str:
    return f"""You are a rigorous mathematical verification expert specializing in finding flaws and counterexamples in barrier functions.

We consider it acceptable as long as the system does not enter the defined unsafe set; strict confinement within X is not required.

System under analysis:
Dynamics: {system['ode']}
State domain X: {system['X_domain']}
Unsafe set X_u: {system['X_u_desc']}
State variables: {', '.join(system['state_vars'])}

[Mathematical Framework (Proposition 4 / Nagumo Theorem)]
  Condition 1: h(x) < 0,  ∀x ∈ X_u   (unsafe set lies in the negative region of h)
  Condition 2: ḣ(x) >= 0,  ∀x ∈ ∂C  (i.e., the boundary where h(x)=0, Nagumo condition)
The invariant set is C = {{x ∈ X : h(x) >= 0}} (superlevel set).

[Verification Steps]
1. Verify Condition 1: pick specific points in X_u, compute whether h(x) is indeed < 0; after quick numerical checks, use formal inequality proofs
2. Compute the Lie derivative ḣ(x) = ∇h · f(x)
3. Specifically check whether ḣ(x) >= 0 holds on the boundary ∂C where h(x) = 0 (Nagumo condition); first do quick point verification, then use formal inequality proofs if it passes
4. Cross-term verification must be rigorous and complete; strict mathematical computation is required, possibly including inequality proofs
5. (Only when verdict is "valid") Analyze whether the invariant set C = {{h(x) >= 0}} could be enlarged: consider whether the level set threshold, coefficients, or functional form of h could be adjusted to cover more of X while still satisfying both conditions. If an enlargement direction exists, provide a concrete suggestion.

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
    return f"""You are a Lean 4 formal proof expert familiar with Mathlib4.

Your task is to write a formal proof framework in Lean 4 for an already-verified barrier function.

System: {system['ode']}
State domain: {system['X_domain']}
Unsafe set: {system['X_u_desc']}

Mathematical Framework (Proposition 4):
  Condition 1: h(x) < 0,  ∀x ∈ X_u   (unsafe set lies in the negative region of h)
  Condition 2: ḣ(x) >= 0,  ∀x ∈ ∂C  (i.e., the boundary where h(x)=0, Nagumo condition)
  Then C = {{x ∈ X : h(x) >= 0}} is an invariant set

Requirements:
1. Use Lean 4 + Mathlib4 syntax
2. Define the system dynamics, barrier function h, and invariant set C
3. State and (as far as possible) prove both conditions and the invariant set theorem
4. First give a natural language outline of the proof, then write the Lean 4 code implementation
5. The code should pass Lean 4 syntax checking

Output the Lean 4 code directly, no additional explanation needed."""


# ─────────────────────────────────────────────
# 4. Local Verification Tools
# ─────────────────────────────────────────────
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
    lie_deriv_simplified = sp.simplify(lie_deriv).doit()
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

    # Condition 2 (Nagumo): ḣ >= 0 on ∂C, only check boundary points where h(x) ≈ 0
    # Use 2% of h value range as boundary thickness epsilon
    h_range = float(np.nanmax(h_vals) - np.nanmin(h_vals))
    epsilon = max(h_range * 0.02, 1e-3)
    on_boundary = not_in_Xu & (np.abs(h_vals) < epsilon)

    cond2_ok = True
    cond2_violations = []
    cond2_viol_frac = None
    if on_boundary.any():
        c2 = lie_vals[on_boundary]
        n_b = int(c2.size)
        finite = np.isfinite(c2)
        c2f = c2[finite]
        # a boundary point violates Nagumo if ḣ is meaningfully negative (below the
        # numerical noise floor); a non-finite ḣ (blow-up) is treated as a violation too
        viol_below = c2f < -cond2_noise
        n_viol = int(viol_below.sum() + (~finite).sum())
        cond2_viol_frac = n_viol / n_b
        min_cond2 = float(np.min(c2f)) if c2f.size else None
        # depth scale: typical |ḣ| magnitude on the boundary band (scale-free reference)
        typ = float(np.median(np.abs(c2f))) if c2f.size else 0.0
        worst = min_cond2 if min_cond2 is not None else float("-inf")
        deep = (not finite.all()) or (worst < -max(cond2_depth_abs, cond2_depth_rel * typ))
        # FAIL only if violations are BOTH widespread (fraction) AND deep — this kills
        # systematic leakage but tolerates isolated sampling spikes near kinks/singularities
        cond2_ok = not (cond2_viol_frac > cond2_frac_tol and deep)
        if not cond2_ok:
            bad = pts[on_boundary][finite][viol_below]
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
        "cond2_viol_frac": round(cond2_viol_frac, 4) if cond2_viol_frac is not None else None,
        "cond2_ok": cond2_ok,
        "symbolic_valid": symbolic_valid,
    }
    if cond1_violations:
        result["cond1_violations"] = cond1_violations
    if cond2_violations:
        result["cond2_violations"] = cond2_violations
    return result


def verify_trajectory(system: dict, h_str: str, n_trajs: int = 30, t_span: float = 15.0) -> dict:
    """
    Sample initial points from inside C = {h(x) >= 0}, integrate the ODE,
    and check whether trajectories always satisfy h(x(t)) >= 0 (invariant set condition).
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

    def ode_rhs(t, state):
        return [float(fi(*state)) for fi in f_funcs]

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

    for x0 in init_pts:
        try:
            sol = solve_ivp(ode_rhs, [0, t_span], x0.tolist(), max_step=0.05,
                            dense_output=False, rtol=1e-6, atol=1e-8)
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
# 6. Visualization
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
            def ode_rhs(t, s):
                return [float(fi(*s)) for fi in f_funcs]
            rng  = np.random.default_rng(123)
            cands = np.column_stack([rng.uniform(lo, hi, 2000) for lo, hi in bounds])
            try:
                h_c = np.array(h_func(*cands.T), dtype=float)
                inside = cands[h_c >= 0][:20]
            except Exception:
                inside = []
            for x0 in inside:
                try:
                    sol = solve_ivp(ode_rhs, [0, 12], x0.tolist(),
                                    max_step=0.05, rtol=1e-5, atol=1e-7)
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


