# Literature map and problem lineage

This document records the intellectual lineage that makes the project a
recognizable reconstruction problem rather than a free-standing speculative
theory. Targeted literature audits were completed on 2026-08-10,
2026-08-12, and 2026-08-13; any priority claim remains provisional pending
specialist review.

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
finite local reconstruction theorem with differential closure,
not the observation that a dilaton modifies Rainich algebra and not a
symmetry-reduced exact-solution construction.

Electromagnetic duality in broader Einstein--Maxwell--scalar models can also
relate different coupling functions while preserving the scalar and spacetime
geometry:

- C. A. R. Herdeiro and J. M. S. Oliveira,
  [*Electromagnetic dual Einstein--Maxwell--scalar
  models*](https://arxiv.org/abs/2005.05354), JHEP 07 (2020) 130.

That result is neighboring prior art rather than the theorem sought here. It
reinforces that metric-level coupling identification must confront duality
orbits explicitly; it does not state the first-channel shear obstruction or
the next-order detector for the fixed exponential EMD family.

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

## 8. Formal PDE and analytic realization

The promotion from compatible finite jets to analytic EMD solution germs uses
B. Kruglikov,
[*Involutivity of field equations*](https://arxiv.org/abs/0902.1685).
The relevant cited result is his Theorem 3 for the gauge-degenerate
source-free Einstein--Maxwell potential system, together with Lemma 4 for a
determined scalar-wave block and the analytic realization consequence.  EMD is
not named in that paper.  Our application works in pure second-order
potentials $(g,A,\phi)$, observes that the exponential couplings are lower
order, and uses the EMD Noether identity for contracted-Bianchi compatibility.
This extension is a human proof requiring specialist audit, not a Lean theorem
and not a direct invocation of Kruglikov's Theorem 4.

## 9. Provisional novelty and significance assessment (updated 2026-08-13)

The audit found substantial prior work on each neighboring ingredient:
classical and higher-dimensional algebraic Rainich theory, separate
geometrization theorems for scalar and Maxwell matter, Kaluza reduction to the
distinguished `a=√3` EMD theory, and symmetry-reduced generalized Rainich
calculations in scalar--tensor gravity. It did not locate a generic
four-dimensional, metric-only, necessary-and-sufficient reconstruction theorem
for the coupled Kaluza EMD sector, nor a comparable machine-checked
formalization.

The 2026-08-12 proof audit identified the channel obstruction, and the
2026-08-13 argument upgrades it to analytic solution germs conditional on the
explicit EMD involutivity lemma pending specialist audit.
For a curvature-normalized non-null Maxwell seed, the complete first
seed-derivative channels determine only

```text
A = a cos(2 theta),
eta = dtheta + (a sin(2 theta)/2)Jv.
```

They possess an exact one-parameter shear kernel and therefore cannot recover
`a²` at metric order three. Constancy of the physical coupling yields one
derivative later

```text
dA + 2B eta - B²Jv = 0,
B = a sin(2 theta),
```

whose wedge with `Jv` reconstructs `B` on the active locus, hence
`a²=A²+B²`.

A focused search did not locate this specific lower-order
non-identifiability/higher-order recovery result in classical Rainich,
scalar-geometrization, generalized scalar-tensor Rainich, higher-dimensional
Rainich, or electromagnetic-duality-orbit work. The defensible novelty is now
the active, simple-spectrum common metric-three-jet continuum at solution
level conditional on that lemma,
the complete-channel shear mechanism, and the matching fourth-order physical
recovery.  The finite algebra is checked by Lean; the analytic solution-germ
upgrade has the separate human-proof boundary in Section 8.

This is a targeted-search conclusion, not a claim of exhaustive priority. The
paper should say “we are unaware of” until specialist review confirms the
gap. The full metric-only necessary-and-sufficient Kaluza theorem remains a
separate, stronger goal and should not be used to inflate the present result.
