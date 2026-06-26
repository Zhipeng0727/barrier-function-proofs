"""
cert.py — neural certificates that bridge to the SOUND symbolic verifiers.

Key idea: a small tanh MLP is itself a closed-form transcendental expression, so a
trained net can be turned into a sympy string (`to_sympy`) and handed to the
existing interval / dReal backends — no auto_LiRPA dependency, the whole sound
stack is reused. The NN supplies expressiveness + gradient training; soundness
comes from the same verifiers as the symbolic arm.

Two Lyapunov parameterisations (a controlled variable in the sweep):
  - LyapunovNetStructural:  V(x) = ‖φ(x)−φ(x*)‖² + α‖x−x*‖²
        positive-definiteness is STRUCTURAL (V(x*)=0, V≥α‖x−x*‖²>0), so the
        verifier only needs the decrease condition ∇V·f ≤ 0. φ = tanh(W₁x+b₁).
  - LyapunovNetPlain:       V(x) = (W₂·tanh(W₁x+b₁)+b₂) − V(x*)
        positivity is NOT structural — must be verified too (the ablation).
"""
from __future__ import annotations

import sympy as sp
import torch
import torch.nn as nn


class LyapunovNetStructural(nn.Module):
    def __init__(self, dim, width, x_star, alpha=0.1, seed=0):
        super().__init__()
        torch.manual_seed(seed)
        self.dim, self.width, self.alpha = dim, width, alpha
        self.register_buffer("x_star", torch.tensor(x_star, dtype=torch.float64))
        self.lin = nn.Linear(dim, width).double()

    def phi(self, x):
        return torch.tanh(self.lin(x))

    def forward(self, x):
        phi_x = self.phi(x)
        phi_star = self.phi(self.x_star.unsqueeze(0))
        diff = phi_x - phi_star
        quad = ((x - self.x_star) ** 2).sum(dim=-1)
        return (diff ** 2).sum(dim=-1) + self.alpha * quad

    def to_sympy(self, state_vars):
        xs = [sp.Symbol(v, real=True) for v in state_vars]
        W = self.lin.weight.detach().cpu().numpy()
        b = self.lin.bias.detach().cpu().numpy()
        xstar = self.x_star.detach().cpu().numpy()
        terms = []
        for j in range(self.width):
            lin = sp.Float(float(b[j])) + sum(sp.Float(float(W[j, i])) * xs[i]
                                              for i in range(self.dim))
            zstar = float(torch.tanh(torch.tensor(
                float(b[j]) + sum(float(W[j, i]) * float(xstar[i]) for i in range(self.dim)),
                dtype=torch.float64)))
            terms.append((sp.tanh(lin) - sp.Float(zstar)) ** 2)
        quad = sum((xs[i] - sp.Float(float(xstar[i]))) ** 2 for i in range(self.dim))
        expr = sum(terms) + sp.Float(self.alpha) * quad
        return str(expr)


class LyapunovNetPlain(nn.Module):
    """V = scalar MLP, shifted to V(x*)=0. Positivity is a LEARNED constraint."""
    def __init__(self, dim, width, x_star, alpha=0.0, seed=0):
        super().__init__()
        torch.manual_seed(seed)
        self.dim, self.width = dim, width
        self.register_buffer("x_star", torch.tensor(x_star, dtype=torch.float64))
        self.l1 = nn.Linear(dim, width).double()
        self.l2 = nn.Linear(width, 1).double()

    def _raw(self, x):
        return self.l2(torch.tanh(self.l1(x))).squeeze(-1)

    def forward(self, x):
        return self._raw(x) - self._raw(self.x_star.unsqueeze(0))

    def to_sympy(self, state_vars):
        xs = [sp.Symbol(v, real=True) for v in state_vars]
        W1 = self.l1.weight.detach().cpu().numpy()
        b1 = self.l1.bias.detach().cpu().numpy()
        W2 = self.l2.weight.detach().cpu().numpy()[0]
        b2 = float(self.l2.bias.detach().cpu().numpy()[0])
        xstar = self.x_star.detach().cpu().numpy()
        hid = []
        for j in range(self.width):
            lin = sp.Float(float(b1[j])) + sum(sp.Float(float(W1[j, i])) * xs[i]
                                               for i in range(self.dim))
            hid.append(sp.tanh(lin))
        raw = sum(sp.Float(float(W2[j])) * hid[j] for j in range(self.width)) + sp.Float(b2)
        # numeric V(x*)
        v0 = float(self.forward(self.x_star.unsqueeze(0)).item()) + 0.0
        raw_star = sum(float(W2[j]) * float(torch.tanh(torch.tensor(
            float(b1[j]) + sum(float(W1[j, i]) * float(xstar[i]) for i in range(self.dim)),
            dtype=torch.float64))) for j in range(self.width)) + b2
        return str(raw - sp.Float(raw_star))


class PolyLyapQuad(nn.Module):
    """Fair POLYNOMIAL baseline (A0): V(x) = ‖L·z‖² + α‖z‖², z=x−x*. P=LᵀL is PSD,
    V(x*)=0 structurally, and V is a degree-2 polynomial → z3 verifies it EXACTLY.
    'Does a quadratic Lyapunov function exist' is the classical question the
    NonPoly systems are built to fail."""
    def __init__(self, dim, width, x_star, alpha=1e-3, seed=0):
        super().__init__()
        torch.manual_seed(seed)
        self.dim, self.alpha = dim, alpha
        self.register_buffer("x_star", torch.tensor(x_star, dtype=torch.float64))
        # seed 0 = exact identity (the natural V=||z||^2 is always a candidate, so
        # the quadratic baseline is fair); seeds>0 perturb to explore other P.
        noise = 0.0 if seed == 0 else 0.2 * torch.randn(dim, dim, dtype=torch.float64)
        self.L = nn.Parameter(torch.eye(dim, dtype=torch.float64) + noise)

    def forward(self, x):
        z = x - self.x_star
        Lz = z @ self.L.T
        return (Lz ** 2).sum(dim=-1) + self.alpha * (z ** 2).sum(dim=-1)

    def to_sympy(self, state_vars):
        xs = [sp.Symbol(v, real=True) for v in state_vars]
        L = self.L.detach().cpu().numpy()
        xstar = self.x_star.detach().cpu().numpy()
        z = [xs[i] - sp.Float(float(xstar[i])) for i in range(self.dim)]
        terms = []
        for i in range(self.dim):
            row = sum(sp.Float(float(L[i, j])) * z[j] for j in range(self.dim))
            terms.append(row ** 2)
        quad = sum(z[i] ** 2 for i in range(self.dim))
        return str(sum(terms) + sp.Float(self.alpha) * quad)


def make_cert(kind, dim, width, x_star, alpha, seed=0):
    if kind == "structural":
        return LyapunovNetStructural(dim, width, x_star, alpha=alpha, seed=seed)
    if kind == "plain":
        return LyapunovNetPlain(dim, width, x_star, alpha=alpha, seed=seed)
    if kind == "quad":
        return PolyLyapQuad(dim, width, x_star, alpha=max(alpha, 1e-3), seed=seed)
    raise ValueError(f"unknown cert kind {kind}")
