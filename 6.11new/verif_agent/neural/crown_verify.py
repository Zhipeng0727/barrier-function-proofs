#!/usr/bin/env python3
"""
crown_verify.py — SOUND verification of a neural Lyapunov decrease via CROWN
(auto_LiRPA), run in a py3.11 env that has auto_LiRPA (e.g. conda env prover-mps).

Reads a JSON spec on argv[1] describing a trained structural tanh Lyapunov net
  V(x) = Σ_j (tanh(W1_j·x+b1_j) − c_j)² + α‖x−x*‖²
and polynomial dynamics f (as monomials), then bounds the Lie derivative
  L(x) = ∇V(x)·f(x)
over the domain box with CROWN, using simple box branch-and-bound + inner-ball
exclusion (asymptotic stability on the annulus). If the CROWN UPPER bound of L is
< 0 on every kept sub-box, decrease is proved (sound). Prints JSON {status,...}.

Decrease, not positivity: positivity is structural (V≥α‖x−x*‖²). CROWN bounds are
far tighter than naive interval on wide boxes, so this is the route to FOSSIL's
full-radius domains where interval BnB is too loose.
"""
import json
import sys

import torch
import torch.nn as nn


class LieNet(nn.Module):
    """L(x) = ∇V(x)·f(x), all closed-form torch ops (CROWN-traceable)."""
    def __init__(self, W1, b1, xstar, alpha, fmono):
        super().__init__()
        self.register_buffer("W1", torch.tensor(W1, dtype=torch.float32))   # (H,n)
        self.register_buffer("b1", torch.tensor(b1, dtype=torch.float32))   # (H,)
        self.register_buffer("xstar", torch.tensor(xstar, dtype=torch.float32))  # (n,)
        self.alpha = float(alpha)
        self.n = len(xstar)
        self.fmono = fmono  # list (per state k) of [coeff, [e1..en]] monomials
        c = torch.tanh(self.xstar @ self.W1.T + self.b1)
        self.register_buffer("c", c)                                         # (H,)

    def forward(self, x):                      # x: (N,n) -> (N,1)
        z = x @ self.W1.T + self.b1            # (N,H)
        t = torch.tanh(z)
        g = 2.0 * (t - self.c) * (1.0 - t * t)  # (N,H)
        gradV = g @ self.W1 + 2.0 * self.alpha * (x - self.xstar)  # (N,n)
        fk = []
        for k in range(self.n):
            acc = torch.zeros(x.shape[0], dtype=x.dtype)
            for coeff, exps in self.fmono[k]:
                term = torch.full((x.shape[0],), float(coeff), dtype=x.dtype)
                for i, e in enumerate(exps):
                    for _ in range(int(e)):
                        term = term * x[:, i]
                acc = acc + term
            fk.append(acc)
        f = torch.stack(fk, dim=-1)            # (N,n)
        return (gradV * f).sum(dim=-1, keepdim=True)   # (N,1)


def _box_in_ball(lo, hi, c, r):
    far2 = sum(max((lo[i] - c[i]) ** 2, (hi[i] - c[i]) ** 2) for i in range(len(c)))
    return far2 <= r * r


def crown_decrease(spec):
    from auto_LiRPA import BoundedModule, BoundedTensor
    from auto_LiRPA.perturbations import PerturbationLpNorm

    net = LieNet(spec["W1"], spec["b1"], spec["xstar"], spec["alpha"], spec["fmono"])
    net.eval()
    n = net.n
    x0 = torch.zeros(1, n, dtype=torch.float32)
    bm = BoundedModule(net, x0, device="cpu")
    xstar, r = spec["xstar"], float(spec.get("inner_radius", 0.0))
    bounds0 = [tuple(b) for b in spec["bounds"]]
    max_boxes = int(spec.get("max_boxes", 4000))
    min_w = float(spec.get("min_width", 0.05))

    stack = [bounds0]
    processed, worst_ub = 0, -1e18
    while stack:
        if processed >= max_boxes:
            return {"status": "unknown", "reason": "box budget", "processed": processed}
        box = stack.pop()
        processed += 1
        lo = [b[0] for b in box]
        hi = [b[1] for b in box]
        if r > 0 and _box_in_ball(lo, hi, xstar, r):
            continue
        xL = torch.tensor([lo], dtype=torch.float32)
        xU = torch.tensor([hi], dtype=torch.float32)
        xm = (xL + xU) / 2
        bx = BoundedTensor(xm, PerturbationLpNorm(norm=float("inf"), x_L=xL, x_U=xU))
        lb, ub = bm.compute_bounds(x=(bx,), method="CROWN")
        ub = float(ub)
        if ub <= 0:
            continue                          # L < 0 on this whole sub-box
        worst_ub = max(worst_ub, ub)
        widths = [hi[i] - lo[i] for i in range(n)]
        i = max(range(n), key=lambda j: widths[j])
        if widths[i] < min_w:
            return {"status": "unknown", "reason": "irreducible box, ub>0",
                    "ub": ub, "box": box, "processed": processed}
        mid = (lo[i] + hi[i]) / 2
        b1, b2 = list(box), list(box)
        b1[i] = (lo[i], mid)
        b2[i] = (mid, hi[i])
        stack += [b1, b2]
    return {"status": "proved", "processed": processed, "worst_ub": worst_ub}


if __name__ == "__main__":
    spec = json.load(open(sys.argv[1]))
    try:
        print(json.dumps(crown_decrease(spec)))
    except Exception as e:
        import traceback
        print(json.dumps({"status": "error", "err": f"{type(e).__name__}: {e}",
                          "tb": traceback.format_exc()[-800:]}))
