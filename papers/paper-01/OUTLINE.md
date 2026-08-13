# Paper I outline

> **Fallback paper outline.** The active publication target is the metric-only
> coupling detector in
> [`../../docs/RESEARCH_RESET.md`](../../docs/RESEARCH_RESET.md). This outline
> remains the release path if the detector fails its statement or validation
> gates.

Working title:

**Pointwise Scalar Reconstruction and Its Discrete Ambiguity in the Generic
Kaluza Einstein–Maxwell–Dilaton Sector**

## 1. Recognizable prior question

Introduce the classical Rainich inverse problem, scalar geometrization, and
the distinguished `a = √3` EMD theory from Kaluza reduction. State that the
coupled inverse problem—not unification in general—is the target.

## 2. Conventions and field equations

Give the selected action and derive all equations and trace identities. Include
a convention comparison table against the exact solutions used later.

## 3. Generic algebraic theorem

- Decompose the Ricci endomorphism into Maxwell and scalar parts.
- Use the non-null Maxwell square identity and rank-one update.
- Derive the characteristic factorization and protected pair.
- Express `q²` and the obstruction through curvature invariants.

## 4. Scalar-gradient reconstruction

- Solve the tensor equation for the rank-one contribution.
- State exact existence, causal-sign, and factorization-uniqueness conditions.
- Show explicitly why the polynomial obstruction alone is insufficient.
- Present the generic eigenbasis formulas
  `u=(a²-q²)/(a-b)` and `v=(b²-q²)/(b-a)`.
- Prove automatic trace compatibility and distinguish real symmetric
  rank-one completion from Lorentzian scalar-covector factorization.
- Prove that the two relative-sign tensors are distinct, classify all
  scalar-generated solutions into the two reflection-related possibilities,
  and interpret the reflection as an element of the Ricci centralizer.

## 5. Differential closure

- Factor the rank-one tensor into a covector.
- Impose local closure/exactness.
- Reconstruct the residual Maxwell stress and impose the Maxwell–Rainich
  differential condition.
- Close with the scalar field equation and global duality datum.

## 6. Algebraic main theorem

State the generic pointwise existence-and-orbit classification and the
curvature-only uniqueness obstruction. This is the first public-release result.

## 7. Target local theorem

State a local necessary-and-sufficient theorem for the generic, non-null,
nondegenerate branch. Every hypothesis should have a geometric interpretation
and a matching Lean declaration or an explicitly documented formalization gap.

## 8. Degenerate cases and limitations

Give a branch table even if complete proofs are deferred. Do not describe the
generic theorem as universal.

## 9. Exact and adversarial tests

Use exact Kaluza metrics as positive tests and unrelated matter models as
negative tests. Separate theorem proof from computational evidence.

## 10. Relation to prior work

Include a table with columns: prior result, reused theorem, new coupled step,
and machine-checked declaration. This section is essential for Vibemathed.
It must include the earlier symmetry-reduced “generalized Rainich algebra” in
scalar–tensor gravity and explain why the present target is more general.

## 11. Discussion

Discuss curvature-based identification of hidden Kaluza structure and possible
applications only after the theorem and limitations are complete.
