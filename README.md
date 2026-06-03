In this work, we focus mainly on continuous dynamical systems and consider the following questions:
1. Can we find invariant sets for the system, provide candidate barrier functions, and give rigorous proofs that the theorem conditions are satisfied?
2. Can larger invariant sets be obtained?
3. Can the method be extended to high-dimensional systems?
\textbf{Among these questions, the existing paper provides a solution to the first. However, due to the limitations of the SMT-based verification tool, it does not address the second and third questions.} For LLM-based methods for discovering barrier functions, the following questions need to be considered:
1. What information should be provided to the LLM to better guide and accelerate its reasoning?
2. How should the agent and tool workflow be designed? 
3. How can local tools be effectively integrated, such as fast trajectory-based validation and Python-based symbolic verification (Sympy, SINDy)?
