In this work, we focus mainly on continuous dynamical systems and consider the following questions:
1. Can we find invariant sets for the system, provide candidate barrier functions, and give rigorous proofs that the theorem conditions are satisfied?
2. Can larger invariant sets be obtained?
3. Can the method be extended to high-dimensional systems?

**Among these questions, the existing paper provides a solution to the first. However, due to the limitations of the SMT-based verification tool, it does not address the second and third questions. ** For LLM-based methods for discovering barrier functions, the following questions need to be considered:
1. What information should be provided to the LLM to better guide and accelerate its reasoning?
2. How should the agent and tool workflow be designed? 
3. How can local tools be effectively integrated, such as fast trajectory-based validation and Python-based symbolic verification (Sympy, SINDy)?

---

## Repository structure

| Path | Contents |
| --- | --- |
| `Main.lean`, `Prover1/` | Original Lean 4 barrier-function proof examples (`ex1`–`ex4`). |
| `6.11new/` | Multi-agent **generate–verify–refute** pipeline for barrier / Lyapunov certificate synthesis. |
| `6.21_maxtest/` | Latest agent iteration (`dual_agent_debate_4`, agent arena v4). |

### `6.11new/` — generate–verify–refute pipeline

A closed loop where an LLM proposes barrier / Lyapunov certificates, **Lean 4 machine-checks** them, and a refuter searches for counterexamples; failures are fed back as structured guidance.

- **Lean-feedback loop with an error knowledge base.** Lean 4 compile errors are classified (knowledge / tactic / syntax) and distilled into a reusable error→fix knowledge base and an **inequality-lemma database**, which are injected into the prompt. This raises the first-pass compile rate and measurably reduces LLM hallucination on the nonlinear / high-dimensional cases where SMT / Lipschitz-constant methods give only conditional or numerical guarantees.
- **core200 dataset tooling.** 200+ certificates drawn from real verification systems in the literature, spanning continuous / discrete / parametric (`∀n`) systems × safety / reach-avoidance / stability, annotated by verification-condition type.
- **Cost-aware orchestration.** Refuter gating, templated proofs, and multi-task scheduling minimize the number of dual-iteration rounds and the token budget.

> Secrets (`*.secrets.env`), Lean build artifacts (`.lake/`), caches, and run logs are excluded via `.gitignore`. API keys are loaded at runtime from a local, untracked `.secrets.env` and are never committed.
