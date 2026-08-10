# Research roadmap

## Phase 0 — Provenance and novelty audit

- Fix the exact `a = √3` EMD action, frame, signature, and normalizations.
- Re-derive the Einstein, Maxwell, and scalar equations.
- Build a specialist bibliography for coupled Rainich/EMD inverse problems.
- Recover or independently reproduce all inherited numerical calculations.

Exit criterion: every starting equation has a source or derivation and every
novelty statement is phrased comparatively.

## Phase 1 — Generic algebraic reconstruction

- Derive the Ricci characteristic factorization from `R = S + V`.
- Formalize the rank-one determinant identity in Lean.
- Prove the protected eigenpair and invariant formulas.
- Solve the linear tensor equation for `V` on the generic branch.
- Prove admissibility and factorization uniqueness for a fixed tensor up to the
  scalar global sign.
- Classify the additional relative-sign tensor ambiguity and its Ricci
  centralizer action.
- Construct counterexamples to algebraic sufficiency.

Exit criterion: a zero-placeholder theorem package for the generic algebraic
step, including an honest existence/orbit classification and every
nondegeneracy hypothesis.

## Phase 2 — Differential closure and local sufficiency

- Factor the reconstructed rank-one tensor into a covector up to sign.
- Determine which differential conditions select or identify the two
  pointwise relative-sign partners.
- State and prove the closure condition implying local exactness.
- Apply Maxwell–Rainich algebraic and differential conditions to `S = R - V`.
- Add the Kaluza scalar equation and duality-complexion datum.
- Prove a local necessary-and-sufficient theorem.

Exit criterion: Paper I candidate with manuscript-to-Lean claim translation.

## Phase 3 — Degenerate branches

Treat `R = 0`, null Maxwell fields, null scalar gradients, `q = 0`, repeated
eigenvalues, and eigenvalue collisions separately. Determine whether each has
a reconstruction theorem, a no-go theorem, or unavoidable nonuniqueness.

## Phase 4 — Exact and adversarial metrics

- Validate on several exact Kaluza/EMD solutions.
- Test non-Kaluza scalar, electrovacuum, perfect-fluid, and mixed-matter metrics.
- Distinguish algebraic false positives from differential false positives.
- Use exact arithmetic or certified residual bounds where possible.

## Phase 5 — Applications

Only after the reconstruction theorem is stable should the project reconnect
to spin-induced scalar multipoles, binary signatures, or the scalar parametric
amplifier. Each application must state whether it follows from Kaluza reduction
or from an independent EFT assumption.
