# verif_agent.neural — neural certificate synthesis arm

Brings the neural-network apparatus into the agent: the certificate is a **trained
tanh network** (expressiveness + gradient training), not a fixed symbolic ansatz.
Soundness is reused, not reinvented — a tanh MLP is a closed-form transcendental
expression, so the trained net is turned into a sympy string and certified by the
SAME sound backends (interval / dReal) as the symbolic arm. No auto_LiRPA needed.

## Pipeline

```
train (torch)            →  to_sympy()              →  sound verify (interval/dReal)
small tanh net V_θ          closed-form expr            ∇V·f ≤ 0 over the box
   ↑ counterexample ──────────────  CEGIS  ──────────────────┘
```

- `cert.py` — `LyapunovNetStructural`: `V(x)=‖φ(x)−φ(x*)‖²+α‖x−x*‖²`, φ=tanh(W₁x+b₁).
  Positive-definiteness is **structural** (V(x*)=0, V≥α‖x−x*‖²>0) so the verifier
  only checks the decrease. `LyapunovNetPlain` is the ablation (PD learned, not free).
- `train.py` — Adam on `relu(∇V·f + margin·‖x−x*‖²)`; f lambdified to torch so the
  Lie derivative flows through autograd.
- `cegis.py` — learner-verifier-falsifier loop: train → sound-verify → on refuted
  use the verifier's counterexample, on unknown run a **PGD falsifier** (ascend V̇)
  to find one; add it and retrain. `unknown` + clean falsifier ⇒ verifier-limited.
- `sweep.py` — controlled-variable comparison: one structural knob changed per
  variant (kind / width / margin / iters / lr / verifier / max_rounds).
- `glm_tuner.py` — GLM reads the results and proposes the next config (one-knob
  change, no repeats) to optimise solved-count → rounds → time.
- `run_experiment.py` — the H1 test: exclusive wins of neural-CEGIS over the
  symbolic-polynomial baseline `V=‖x−x*‖²` on the transcendental Lyapunov slice.

## Why this is the right shape

The selection agent's job grows from "pick a verifier" to "pick a certificate
*representation + synthesizer*": symbolic (LLM/SOS, gives a Lean cert) when it
suffices, neural-CEGIS when expressiveness is needed (the transcendental /
poly-failure systems). The neural arm is just another registered synthesizer whose
output is verified by the existing sound stack — so it composes, and a "proved" is
still only sound because interval/dReal said so.

## Honest limits

- A trained net has **no Lean proof** — for those systems you trade the
  Lean-checkable certificate for coverage. Mitigation (future): symbolic-regress
  the trained V back to a closed form and verify that in Lean.
- Keep the net small (width ≲ 8): the to_sympy decrease expression has one tanh
  term per hidden unit, and interval BnB / dReal cost grows with that count.
- `unknown-verifier-limited` is a real outcome — the learner found a cert that
  passes sampling + PGD but interval's enclosure is too loose to certify. That's a
  verifier-tightness problem (try dReal, or α,β-CROWN later), not a learner bug.

## Run

```
python3 -m verif_agent.neural.run_experiment --n 8 --tune 3
```
Needs torch (installed) and Docker for the dReal verifier variant; interval-only
runs need neither beyond mpmath.
