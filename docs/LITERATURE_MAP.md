# Literature map and problem lineage

This document records the intellectual lineage that makes the project a
recognizable reconstruction problem rather than a free-standing speculative
theory. A targeted literature audit was completed on 2026-08-10; any priority
claim remains provisional pending specialist review.

## 1. Classical Rainich question

Rainich asked for local geometric conditions, expressed through curvature,
that are necessary and sufficient for a spacetime to be an Einstein–Maxwell
solution, together with reconstruction of the electromagnetic field up to the
expected duality freedom.

- G. Y. Rainich, *Electrodynamics in the General Relativity Theory* (1925).
- C. W. Misner and J. A. Wheeler, *Classical Physics as Geometry* (1957).

Our project inherits the same question but changes the matter sector from
Maxwell alone to the coupled scalar–Maxwell system fixed by Kaluza reduction.

## 2. Scalar geometrization

Metric-only necessary-and-sufficient conditions and scalar reconstruction are
known for broad Einstein–scalar systems. Krongos and Torre unify and extend
this line, including null/non-null branches and potentials:

- D. S. Krongos and C. G. Torre,
  [*Geometrization Conditions for Perfect Fluids, Scalar Fields, and
  Electromagnetic Fields*](https://arxiv.org/abs/1503.06311).

This establishes that reconstructing a scalar from curvature is a known and
serious problem. It does not by itself solve the **coupled** EMD reconstruction,
because the Ricci tensor contains scalar and Maxwell contributions at once.

## 3. Algebraic Rainich theory beyond four dimensions

Bergqvist and Höglund develop algebraic Rainich identities for forms and obtain
a complete five-dimensional generalization in their setting:

- G. Bergqvist and A. Höglund,
  [*Algebraic Rainich Theory and Antisymmetrisation in Higher
  Dimensions*](https://arxiv.org/abs/gr-qc/0202092).

Our target is not “Rainich theory in five dimensions.” It is a four-dimensional
metric-only characterization of the particular **reduced** scalar–Maxwell
sector arising from five-dimensional vacuum gravity.

## 4. Kaluza reduction and the selected EMD theory

Five-dimensional vacuum gravity with a spacelike circle symmetry reduces,
after frame and field redefinitions, to a four-dimensional
Einstein–Maxwell–dilaton theory with the distinguished coupling `a = √3`.
Paper I must select one convention and derive every coefficient used in the
reconstruction equations.

Exact rotating and dyonic Kaluza solutions provide nonlinear positive tests,
but an exact solution satisfying a condition does not establish that the
condition is new or sufficient.

A useful convention and provenance reference is:

- H. Lü, P. Mao, and J.-B. Wu,
  [*Asymptotic Structure of Einstein–Maxwell–Dilaton Theory and Its Five
  Dimensional Origin*](https://arxiv.org/abs/1909.00970).

It explicitly gives the four-dimensional EMD equations, the trace relation
`R = ½(∂φ)²` in its normalization, and the lift of the Kaluza-coupled solution
space to five dimensions.

## 5. Prior generalized Rainich work in scalar–tensor settings

The phrase “generalized Rainich algebra” has already been used for
scalar–tensor/Einstein–Maxwell–dilaton systems. Costa, Naves de Oliveira, and
Guimarães apply modified Ricci algebra to static charged cosmic-string
solutions:

- M. L. Costa, A. L. Naves de Oliveira, and M. E. X. Guimarães,
  *On the Generalized Rainich Algebra in Scalar-Tensor Gravities*,
  PoS(IC2006)061 (2006).

This is essential prior art. Our defensible delta must therefore be a generic,
coordinate-free reconstruction/orbit-classification theorem with differential closure,
not the observation that a dilaton modifies Rainich algebra and not a
symmetry-reduced exact-solution construction.

## 6. The precise synthesis question

The repository asks:

> Given only a generic four-dimensional Lorentzian metric, can curvature
> locally identify the `a = √3` EMD sector, reconstruct the scalar-gradient
> tensor and Maxwell stress, and state the remaining differential conditions
> as a necessary-and-sufficient theorem?

The expected contribution is therefore a synthesis theorem joining two known
geometrization problems under a physically distinguished coupling. The first
paper succeeds only if it proves more than the separate application of known
scalar and Maxwell results.

## 7. Mandatory novelty checks

Before a novelty claim is made, the bibliography must be audited for:

- Rainich-like conditions in scalar–tensor and EMD theories;
- inverse problems for coupled Einstein–matter systems;
- invariant classification of `a = √3` EMD spacetimes;
- Kaluza uplift criteria stated directly in four-dimensional curvature;
- degenerate/null reconstructions and global duality obstructions.

## 8. Provisional novelty and significance assessment (2026-08-10)

The audit found substantial prior work on each neighboring ingredient:
classical and higher-dimensional algebraic Rainich theory, separate
geometrization theorems for scalar and Maxwell matter, Kaluza reduction to the
distinguished `a=√3` EMD theory, and symmetry-reduced generalized Rainich
calculations in scalar--tensor gravity. It did not locate a generic
four-dimensional, metric-only, necessary-and-sufficient reconstruction theorem
for the coupled Kaluza EMD sector, nor a comparable machine-checked
formalization.

Accordingly, the defensible novelty is not any isolated Rainich identity. It
is the coupled synthesis: curvature-derived scalar-branch classification,
Maxwell residual and principal-plane reconstruction, simultaneous
complexion/coupling recovery, a constructive real two-form square root, and
eventually a local Kaluza uplift theorem, with an explicit Lean claim ledger.
This is a targeted-search conclusion, not a claim of exhaustive priority; the
paper should use “we are unaware of” until expert review confirms the gap.

The current result is a substantial formal algebraic reconstruction result but
not yet the high-impact theorem. Its significance rises sharply if Phase III
closes the smooth local Maxwell orbit and differential integrability, and
again if Phase IV proves the full local necessary-and-sufficient uplift.
