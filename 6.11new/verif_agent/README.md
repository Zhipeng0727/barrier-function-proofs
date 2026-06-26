# verif_agent — verification-method-selection agent for barrier / Lyapunov certificates

A SATzilla-style **algorithm-selection agent** for formal verification of
barrier functions and Lyapunov functions. Given a `(dynamical system,
certificate)`, it routes to the cheapest **sound** backend that can settle the
problem and stops at the first conclusive verdict. *Selection is the acceleration
mechanism.*

This is the engine; the companion **skill** (`~/.claude/skills/verif-agent-route/`)
is the natural-language front door that extracts a problem from a paper and drives
this package.

## Why an agent here (and not just α,β-CROWN)

Mainstream NN-robustness verification is dominated by one tool (α,β-CROWN), so
selection is pointless there. Barrier/Lyapunov verification is the opposite:
**no method dominates** — the right backend depends on (dynamics class × certificate
form × dimension × discrete/continuous). On core200 the split is 49 poly / 16
rational / 8 piecewise / 127 transcendental, each favouring a different sound
technique. That heterogeneity is exactly what makes routing worthwhile.

## Conditions checked (matches the pipeline's `barrier_core` semantics)

- **Barrier (continuous, Nagumo):** `h<0` on `X_u`; `ḣ=∇h·f ≥ 0` on `∂C`, accepted
  via the exponential-CBF family `ḣ ≥ -C·h` (comparison lemma ⇒ invariance).
- **Barrier (discrete):** `h<0` on `X_u`; `h(f(x)) ≥ 0` on all of `C`.
- **Lyapunov:** `V(x*)=0`, `V>0` away from `x*` (PSD if `psd_ok`); `V̇=∇V·f ≤ 0`
  (continuous) or `V(f(x))-V(x) ≤ 0` (discrete).

## Backends (the routing pool)

| backend | sound | fragment it owns | mechanism |
|---|---|---|---|
| `sampling` | ✗ | all (gate) | reuses `barrier_core` samplers — fast falsifier, rejects wrong certs |
| `z3` | ✓ | polynomial **+ rational** | nlsat counterexample search; rational via `sign(N/D)=sign(N·D)` with a pole pre-check |
| `interval` | ✓ | transcendental / Abs-Min-Max, dim ≤ 4 | mpmath interval-arithmetic branch-and-bound |
| `dreal` | ✓ | transcendental, higher dim | δ-complete SMT via the `dreal/dreal4` **Docker** image + SMT2 (pip build is broken on macOS). Lyapunov positivity delegated to interval-PSD (dReal can't prove PD near x*); dReal proves the decrease. |
| `lean` | ✓ | parametric ∀n / structural | LLM-written Mathlib proof, strict (sorry-free); slowest, opt-in `--with-lean` |
| `crown`, `milp` | ✓ | **neural** certificates | registered, dormant on symbolic core200 (fire when `cert_nn` is set) |

Soundness contract: a `proved` is reported `sound=True` only from a sound backend.
The agent never funnels to one backend; a sampling-only pass is flagged unsound.
Refutations are only trusted when the counterexample lies in the true domain
(simplex systems and rational poles are handled so they never false-refute).

## Usage

```python
import sys; sys.path.insert(0, "/Users/zhipeng/Desktop/paper4/6.11new")
from verif_agent import verify, route_system
res = verify(system_dict)            # AgentResult: status, sound, chosen_backend, trace
route_system(system_dict)            # {ladder, rationale, feature_vector}
```

Benchmark / iterate:
```
python3 -m verif_agent.eval_on_core200 --limit 200          # core200 sweep
python3 -m verif_agent.eval_on_core200 --limit 200 --use-glm  # fuller coverage (GLM converts hard entries)
python3 -m verif_agent.paper_examples                        # paper's SYSTEMS (darboux, bb_linear, …)
```

## Results (core200, locally-parsed cert-bearing subset, n=53)

Sound coverage over four iterations: **25 → 31 → 33 → 41 / 53**, with **0 false
refutations** throughout and the router **matching the oracle on every instance**
(whenever some sound backend can prove a case, the router picks it). By class:
polynomial 7/7, rational 4/7, transcendental 29/35, piecewise 1/4. Backend split:
z3 owns poly+rational, interval+dReal split transcendental (interval ≤4D fast,
dReal for what interval's dependency-problem wall blocks). Selection acceleration
≈1.4× (stop at first conclusive vs running the whole pool).

The 12 remaining unsound-passes are honest limits: dReal returns δ-sat on
semidefinite-tight decreases (`V̇=0` on a set), rational certs with poles inside
the domain, and a few piecewise discrete cases. See `benchmark_result.json` for
per-instance traces.

## Extending

- **Add a backend:** subclass `Backend` (`backend_base.py`), implement
  `applicable()` + `_verify()`, `register()` it, add it to the selector ladder.
- **Learned routing:** `selector.route()` is the single swap point — replace the
  rule table with a model trained on `benchmark_result.json` outcomes; the agent
  and backends don't change.
- **NN certificates:** set `system["cert_nn"]` / `system["dynamics_nn"]`; the
  crown/milp adapters then become applicable.
