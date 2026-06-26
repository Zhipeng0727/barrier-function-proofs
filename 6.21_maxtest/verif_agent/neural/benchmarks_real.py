"""
benchmarks_real.py — REAL, literature-sourced Lyapunov systems, transcribed
verbatim from other people's benchmark code on disk (not our constructed core200).

Source: FOSSIL (Abate, Ahmed, Edwards, Giacobbe, Peruffo),
  experiments/benchmarks/models.py + benchmarks_lyap.py.
  - NonPoly0..3: POLYNOMIAL dynamics whose Lyapunov function is NON-polynomial
    (2014 "Non-Polynomial Lyapunov via Darboux" + Parrillo CDC 2011). This is the
    genuine poly-failure set — the clean neutral H1 test.
  - Poly2..4, Benchmark0: polynomial Lyapunov exists (Sriram nolcos13 / FOSSIL).
Domains are FOSSIL's (Torus(c,outer,inner) → box [c-outer,c+outer]; positive-
orthant sphere radius R → box [0.01,R]); equilibrium is the origin for all.

vars x,y,z -> x1,x2,x3.
"""

REAL_SYSTEMS = {
    # ---- non-poly Lyapunov needed (poly dynamics) ----
    "fossil_nonpoly0": {
        "name": "FOSSIL NonPoly0", "state_vars": ["x1", "x2"],
        "f_expr": ["-x1 + x1*x2", "-x2"],
        "X_bounds": [(-1.0, 1.0), (-1.0, 1.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5,
        "source": "FOSSIL NonPoly0 (Darboux non-poly Lyapunov series)"},
    "fossil_nonpoly1": {
        "name": "FOSSIL NonPoly1", "state_vars": ["x1", "x2"],
        "f_expr": ["-x1 + 2*x1**2*x2", "-x2"],
        "X_bounds": [(0.01, 10.0), (0.01, 10.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5,
        "source": "FOSSIL NonPoly1 (positive orthant)"},
    "fossil_nonpoly2": {
        "name": "FOSSIL NonPoly2", "state_vars": ["x1", "x2", "x3"],
        "f_expr": ["-x1", "-2*x2 + 0.1*x1*x2**2 + x3", "-x3 - 1.5*x2"],
        "X_bounds": [(0.01, 10.0)] * 3, "equilibrium": [0.0, 0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5,
        "source": "FOSSIL NonPoly2 (positive orthant, 3D)"},
    "fossil_nonpoly3": {
        "name": "FOSSIL NonPoly3", "state_vars": ["x1", "x2", "x3"],
        "f_expr": ["-3*x1 - 0.1*x1*x2**3", "-x2 + x3", "-x3"],
        "X_bounds": [(0.01, 10.0)] * 3, "equilibrium": [0.0, 0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5,
        "source": "FOSSIL NonPoly3 (positive orthant, 3D)"},
    # ---- polynomial Lyapunov exists (control set) ----
    "fossil_benchmark0": {
        "name": "FOSSIL Benchmark0", "state_vars": ["x1", "x2"],
        "f_expr": ["-x1", "-x2"],
        "X_bounds": [(-10.0, 10.0), (-10.0, 10.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5, "source": "FOSSIL Benchmark0"},
    "fossil_poly1": {
        "name": "FOSSIL Poly1", "state_vars": ["x1", "x2", "x3"],
        "f_expr": ["-x1**3 - x1*x3**2", "-x2 - x1**2*x2", "-x3 + 3*x1**2*x3 - 3*x3"],
        "X_bounds": [(-10.0, 10.0)] * 3, "equilibrium": [0.0, 0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5, "source": "FOSSIL Poly1 (Sriram nolcos13)"},
    "fossil_poly2": {
        "name": "FOSSIL Poly2", "state_vars": ["x1", "x2"],
        "f_expr": ["-x1**3 + x2", "-x1 - x2"],
        "X_bounds": [(-10.0, 10.0), (-10.0, 10.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5, "source": "FOSSIL Poly2 (Sriram nolcos13)"},
    "fossil_poly3": {
        "name": "FOSSIL Poly3", "state_vars": ["x1", "x2"],
        "f_expr": ["-x1**3 - x2**2", "x1*x2 - x2**3"],
        "X_bounds": [(-10.0, 10.0), (-10.0, 10.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5, "source": "FOSSIL Poly3 (Sriram nolcos13)"},
    "fossil_poly4": {
        "name": "FOSSIL Poly4", "state_vars": ["x1", "x2"],
        "f_expr": ["-x1 - 1.5*x1**2*x2**3", "-x2**3 + 0.5*x1**3*x2**2"],
        "X_bounds": [(-10.0, 10.0), (-10.0, 10.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5, "source": "FOSSIL Poly4 (Sriram nolcos13)"},
    # ---- Chang et al. NeurIPS 2019: inverted pendulum, LQR-stabilised closed loop ----
    # f=[x2,(mGl sin x1 - b x2 + u)/(ml^2)], G=9.81,m=0.15,l=0.5,b=0.1; u=-Kx, LQR
    # gain K=[1.97725,0.97624] (Q=I,R=1). Transcendental (sin); eq origin. Quadratic
    # LQR Lyapunov holds locally — bigger box exposes the sin nonlinearity.
    "chang_pendulum_lqr": {
        "name": "Chang inverted pendulum (LQR)", "state_vars": ["x1", "x2"],
        "f_expr": ["x2", "19.62*sin(x1) - 52.7267*x1 - 28.6997*x2"],
        "X_bounds": [(-3.0, 3.0), (-3.0, 3.0)], "equilibrium": [0.0, 0.0],
        "task_type": "lyapunov", "discrete": False, "inner_radius": 0.5,
        "source": "Chang et al. NeurIPS 2019 inverted pendulum, LQR closed loop"},
}
