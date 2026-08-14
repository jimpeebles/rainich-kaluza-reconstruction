# Vibemathed positioning and Lean contract (archived)

> Historical positioning only.  Current claims and tasks are governed by
> [`CLAIM_LEDGER.md`](../CLAIM_LEDGER.md) and [`RESEARCH_PLAN.md`](../RESEARCH_PLAN.md).

## Recommended submission narrative

The submission should begin with a standard inverse problem in general
relativity, not with spacetime engineering:

1. Rainich reconstructed electromagnetism from geometry.
2. Later work reconstructed scalar fields from geometry.
3. Kaluza reduction produces a distinguished theory containing both fields.
4. The coupled reconstruction problem is not obtained by naively applying the
   two separate theorems, because curvature contains their sum.
5. We derive and machine-check the generic algebraic decomposition and show
   that curvature determines a two-element centralizer orbit rather than a
   unique scalar tensor.
6. The larger project asks which differential conditions select or identify
   those partners and complete a local if-and-only-if result.

That progression makes the paper a response to known mathematical questions.
The broader Kaluza motivation belongs in the introduction and discussion, not
in the theorem statement.

## What Lean should certify

Lean should cover the exact logical spine:

- characteristic-polynomial and invariant identities;
- the matrix determinant/rank-one argument;
- existence and classification of reconstructed rank-one tensor orbits;
- branch hypotheses and all divisions/nondegeneracy conditions;
- algebraic Maxwell residual conditions;
- eventually, the local differential integrability implications to the extent
  supported by the formal differential-geometry library.

Lean should not be presented as verifying:

- novelty;
- physical realization of Kaluza theory;
- a numerical scan without certified error bounds;
- an approximation imported from physics prose;
- correspondence between informal tensors and Lean objects unless an explicit
  claim-translation table is included.

## Submission artifact

A credible Vibemathed package should contain:

- a short conventional mathematical-physics manuscript;
- a theorem dependency graph;
- pinned Lean/Mathlib versions;
- zero `sorry`, `admit`, or project axioms on the advertised theorem surface;
- an assumptions report (`#print axioms` for principal theorems), explaining
  Lean's standard logical dependencies separately from project assumptions;
- exact-solution and adversarial examples;
- a claim-translation table connecting every displayed manuscript theorem to
  a Lean declaration;
- a prior-work table saying what is reused, strengthened, or genuinely new.

## Minimum publishable delta

The polynomial obstruction alone is not sufficient for submission. A meaningful
advance is one of:

1. a proved generic rank-one reconstruction/orbit classification, including a
   no-go theorem for pointwise uniqueness; or
2. a genuine local necessary-and-sufficient EMD geometrization theorem.

The second is stronger. The first could still be a focused paper if it resolves
a clearly documented missing algebraic step in the literature and is paired
with exact counterexamples showing why weaker conditions fail.

The repository now meets the algebraic core of the first option: it has a
machine-checked generic block classification, a signature-aware
scalar-factorization criterion, a complete two-branch classification, and a
basis-independent theorem showing invariance under Ricci-centralizing
involutions. A public partial-result submission should emphasize the discrete
uniqueness obstruction and should be released only with the convention note,
claim map, pinned source, and explicit comparison to the symmetry-reduced work
of Costa, Naves de Oliveira, and Guimarães.
