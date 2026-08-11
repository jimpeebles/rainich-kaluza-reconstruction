# Realigned execution plan

Date adopted: 2026-08-11

This document is the operational companion to
[`HIGH_IMPACT_PROGRAM.md`](HIGH_IMPACT_PROGRAM.md). Roman numerals always refer
to the six scientific phases in that program. Repository work packages use
labels such as `IV-G1` and `V-T1`; they are not additional phases.

## Why the plan was realigned

The project has advanced far enough that two different milestones must no
longer be conflated:

1. **Phase-IV uplift-module completion:** accepted generic EMD data are
   integrated and classified into local five-dimensional Ricci-flat uplifts.
2. **Official Phase-IV program exit:** the four-dimensional metric itself
   supplies those accepted data through intrinsic curvature conditions, so the
   full curvature-only local if-and-only-if theorem follows.

The first milestone is complete. The smooth curvature-projector realization
part of the Phase-II seam is now complete on the explicit generic local patch.
The second milestone still crosses the substantive scalar-branch closedness
or obstruction problem. The former Maxwell principal-plane input has also
been discharged algebraically from dimension four, trace zero, and the
non-null square law.
Exact metrics may enter a labeled Phase-V validation track after the uplift
module is complete, but Phase IV is not marked complete until the upstream
curvature gate and the uplift theorem are both closed.

## Current verified position

- Phase III has a complete generic local decision interface conditional on an
  admissible scalar branch and its first jet.
- Phase IV.1 integrates the physical two-form and classifies its local gauge
  orbit.
- Phase IV.2 derives and verifies the Kaluza constants and independently
  recovers `a²=3`.
- Phase IV.3 proves the complete normal-frame Ricci/EMD equivalence, realizes
  it using actual `C²` fields, and identifies it with generic coordinate
  Levi--Civita Ricci.
- Affine coordinate covariance and universal nonlinear connection-level Ricci
  covariance are complete.
- Nonlinear metric realization is complete. Lean verifies the transformed
  inverse-metric jet, both differentiated raising contractions, the induced
  product-rule Christoffel jet, unconditional coordinate-Ricci covariance and
  two-sided Ricci-flatness equivalence, and the nonlinear-coordinate Kaluza
  specialization.
- Intrinsic local packaging is complete. The actual componentwise `C²`
  Lorentzian Kaluza metric on the circle-invariant product patch supplies a
  symmetric nondegenerate coordinate two-jet, and Ricci-flatness is proved
  independent of every invertible nonlinear chart-overlap three-jet.
- The local uplift orbit is classified exhaustively inside the
  product-preserving circle-coordinate class. Gauge shifts, radius rescaling,
  and fiber reversal are named instances of a single necessary-and-sufficient
  presentation theorem; the active and exceptional duality branches remain
  explicit.
- The conditional uplift module is assembled. An explicit accepted-branch
  certificate bridges the post-unweighting `C¹` field package to actual
  normal-gauge `C²` EMD fields; one theorem then performs scalar integration,
  radial potential recovery, intrinsic uplift, converse reduction, and orbit
  closure.
- The II-G1 algebraic entrance is complete. Both Maxwell projector ranges have
  rank two, rank-one scalar perturbations retain actual `±q` characteristic
  roots, and the canonical endomorphism coefficients obey the advertised
  quadratic factorization and obstruction.
- The II-G2 geometric instantiation is complete on explicit labeled
  simple-spectrum and strict fixed-probe patches. The Lagrange projectors are
  smooth matrix fields, their coordinate derivatives satisfy the full
  Levi--Civita four-block formula, and the reconstructed spectral one-forms
  have explicit obstruction matrices `dα,dβ`.
- The Phase-II existence/closure problem remains the principal mathematical
  risk of the north-star theorem.

## Critical path through Phase IV

### IV-G1 — close nonlinear metric realization

Prove that the transformed inverse metric and transformed first- and
second-metric jets induce the already-certified product-rule transformed
second-kind connection jet. Derive as immediate corollaries:

- unconditional nonlinear covariance of `coordinateRicci`;
- preservation and reflection of coordinate Ricci-flatness;
- nonlinear-coordinate specialization of the actual Kaluza local-product
  theorem.

**Gate:** no conditional Christoffel-jet equality remains in the advertised
coordinate-Ricci surface.

**Status: complete.** The affine first-kind product rule and the inhomogeneous
metric-Hessian/third-derivative product rule are proved separately and
assembled into `transformedFirstKindJet_raise_eq_connectionBracketJet`.
`coordinateChristoffelJet_transformConnectionJet` closes the second-kind
metric realization, with first-metric-jet symmetry
`dg R A B = dg R B A` explicit. Its Ricci covariance, two-sided flatness
corollary, and nonlinear-coordinate Kaluza specialization are machine checked.

### IV-G2 — intrinsic local packaging

Package the finite-jet covariance result as a chart-independent local theorem
for the pseudo-Riemannian Kaluza metric. Reuse the proved overlap law instead
of rebuilding the component curvature calculation inside a large manifold
API. State all differentiability, signature, product-patch, and
circle-invariance hypotheses explicitly.

**Gate:** Ricci-flatness of the constructed local product is independent of
the normal/radial-gauge chart used to prove it.

**Status: complete.** `IntrinsicKaluzaLocal.lean` packages a symmetric,
nondegenerate pseudo-Riemannian coordinate two-jet and defines
Ricci-flatness after an arbitrary invertible nonlinear overlap three-jet.
The already-proved nonlinear tensor law gives a two-sided chart-independence
theorem. Its Kaluza specialization starts from the actual componentwise `C²`
metric on `BaseCoordinateSpace × ℝ`, records circle invariance and the
displayed `(-,+,+,+,+)` signature explicitly, and proves both pairwise chart
independence and `intrinsicRicciFlatAt_iff_emd`. The theorem is local and does
not assert a global circle quotient or global manifold topology.

### IV-O1 — complete uplift-orbit classification

Assemble the existing invariance and uniqueness results and prove that the
list is exhaustive:

- scalar orientation paired with `a↦-a`;
- additive scalar constant paired with circle-radius normalization;
- Maxwell gauge `A↦A+dχ` paired with the fiber-coordinate shift;
- surviving overall Maxwell sign and fiber reversal;
- admissible changes of local circle coordinate.

Exceptional zero-coupling or inactive-source duality orbits must remain
separate from the generic active branch.

**Gate:** two local uplifts of the same accepted branch are equivalent exactly
by the stated continuous, gauge, and discrete freedoms.

**Status: complete.** `KaluzaUpliftOrbit.lean` defines the first-order datum of
an admissible product-preserving circle-coordinate change and proves
`equivalentUnder_iff_compatible`: equality of two Kaluza block presentations
holds exactly when their warped base blocks, fiber radii, and connection
one-forms obey the three forced compatibility laws. Gauge plus fiber shift,
constant dilaton plus circle-radius/base rescaling, and Maxwell sign plus
fiber reversal are proved instances. The field-level gauge theorem turns
equal curvature into an exact local coordinate shift on an open convex patch.
The Kaluza coupling locus is exactly `a=±√3`; on the active nonzero-coupling
branch the duality orbit is iff the overall sign, while the already-certified
zero-coupling and inactive-source loci retain the full circle. Circle
translations are invisible to the tangent pairing and are covered by the
circle-invariant local metric.

### IV-C1 — assemble the conditional uplift theorem

Compose scalar integration, Maxwell unweighting, radial potential recovery,
the `a²=3` detector, intrinsic Ricci-flatness, converse reduction, and IV-O1.

**Gate:** a single theorem takes an accepted generic Phase-III orbit to the
complete local Ricci-flat uplift orbit and proves the converse, without an
unlisted chart or gauge choice.

**Status: complete, conditional on the explicit accepted-data bridge.**
`ConditionalKaluzaUplift.lean` defines `AcceptedKaluzaBranchAt`, whose fields
state the exact seam between the existing abstractions: a closed scalar
one-form with a chosen point normalization, the post-unweighting `C¹` closed
Maxwell field, `a²=3`, and a normal-gauge realizer that identifies chosen
potentials with actual `C²` EMD fields.
`exists_completeConditionalKaluzaUplift` integrates and normalizes the scalar,
chooses the radial Maxwell potential, constructs the Lorentzian product germ,
proves intrinsic Ricci-flatness in every nonlinear chart, retains the converse
Ricci-flatness/EMD iff, and returns the complete additive scalar, exact gauge,
coupling-orientation, and product-presentation orbits. The certificate does
not assert that curvature supplies the bridge; constructing an accepted
closed branch remains the upstream curvature-entry obligation. RK-R2o now
settles the scalar-potential part once the smooth curvature jet is realized as
the actual Frechet derivative of its spectral one-form field.

## Upstream curvature gate for the official Phase-IV exit

### II-G1 — finish the algebraic entrance

- formalize the four-dimensional non-null Maxwell principal-plane
  multiplicities or isolate the exact literature theorem as a named input;
- complete the protected-eigenvector-to-characteristic-root assembly;
- keep algebraic false positives visibly rejected.

**Status: complete.** `AlgebraicEntrance.lean` reuses the already proved
rank-two theorem `maxwellProjectors_finrank_range_eq_two`, extracts independent
pairs in both polynomial projector ranges, and composes them with rank-one
protection. `protected_opposite_isRoot_charpoly_of_maxwellResidual` converts
the surviving vectors to roots of the actual Mathlib characteristic
polynomial. `CharacteristicData.ofEndomorphism` fixes the coefficient signs,
and `charpoly_factorization_of_maxwellResidual_add_rankOne_canonical` plus
`kaluzaObstruction_of_maxwellResidual_add_rankOne` close the factorization and
necessary-obstruction chain. The obstruction-zero false positive remains a
separate explicit rejection theorem. The square law itself remains the named
four-dimensional Maxwell input RK-A1; no additional principal-plane
multiplicity input is needed.

### II-G2 — instantiate smooth curvature projectors

Promote the evaluated Lagrange-projector and scalar-amplitude derivative
formulas to smooth Ricci tensor fields with their Levi--Civita derivatives.
Assemble curvature-derived one-forms `α,β` and explicit formulas for
`dα,dβ`.

**Status: complete on the explicit generic local patch.**
`SmoothCurvatureProjector.lean` realizes every four-root Lagrange polynomial
as an entrywise `C^n` matrix field wherever its three labeled target gaps are
nonzero, transports the basis-free idempotence and four-projector resolution
to those matrices, and turns fixed projected probes into smooth normalized
metric-dual eigen-one-forms on strict Gram-sign patches. The mixed-tensor
coordinate connection is proved to be a derivation; consequently ordinary
differentiated projector and eigen-equations yield the complete
Levi--Civita formula in
`leviCivitaSpectralProjectorDerivative_fourBlock_of_coordinateJets`.
The reconstructed amplitude derivatives are assembled directionwise, and
`CurvatureScalarBranchJet4` supplies the explicit product-rule obstruction
forms `dα,dβ` with relative-sign tests `dα±dβ`. No assertion that either test
vanishes is made here; that is exactly II-G3.

### II-G3 — settle branch existence

Classify the two relative-sign candidates by the exact differential
obstructions. Prove one of the outcomes demanded by the Phase-II gate:

- a unique generic closed branch;
- a genuine two-uplift exceptional locus; or
- a sharp curvature obstruction proving that neither branch closes.

**Status: exact obstruction and local integration classifier complete at the
realized-field interface.** `CurvatureBranchObstruction.lean` proves the
exhaustive four-way decision from the explicit II-G2 matrices. Unique plus,
unique minus, two-branch, and no-branch outcomes have
necessary-and-sufficient equations; the no-branch case is `dα≠dβ` and
`dα≠-dβ`. At patch level, one nonzero `dα+dβ` witness and one nonzero
`dα-dβ` witness—possibly at different points—reject both local branches.
`CurvatureBranchIntegration.lean` then identifies those coordinate matrices
with Mathlib closedness for genuine differentiable one-form fields whose
displayed jets are their actual Frechet derivatives. On every open convex
patch, obstruction vanishing is iff local scalar-potential existence, all
zero/one/two-potential outcomes are exhaustive, and the two witnesses rule
out both potentials. No existence assumption is made. The remaining
curvature-entry seam is to instantiate the explicit realization certificate
directly from the II-G2 smooth projector and amplitude fields; downstream HC1
then tests each surviving branch rather than deciding scalar integrability.

### IV-N1 — north-star composition

Instantiate the RK-R2o realization from the II-G2 smooth curvature fields,
then compose II-G1--II-G3, the completed Phase-III decision interface, and
IV-C1 into the finite-order curvature-only local recognition theorem. Every
null, repeated-root, zero-trace, and topological exclusion remains explicit.

**Official Phase-IV gate:** IV-G1, IV-G2, IV-O1, IV-C1, and IV-N1 are all
complete. A conditional uplift theorem alone does not close this gate.

## Phase-V validation track

The validation harness may begin after IV-C1 because it can exercise the
accepted-data interface and help diagnose II-G3. Its results do not replace
the Phase-IV proof obligations.

### V-T1 — reproducible exact-metric infrastructure

- recover every inherited convention and source from first principles;
- use exact symbolic arithmetic or certified residual bounds;
- record software versions, inputs, generated identities, and normalization
  maps in the repository;
- separate machine-generated evidence from Lean-proved claims.

**Status: operational, source recovery still in progress.** `validation/`
pins Python 3.12.13 and SymPy 1.14.0 with hashed package artifacts, implements
the coordinate Christoffel/Ricci, convention-fixed EMD-residual, exterior
derivative, and Kaluza-uplift formulas using exact symbolic arithmetic, and
records canonical inputs, provenance, runtime versions, expected branch,
residual hashes, and byte-for-byte artifact drift. The seed
`vt1-flat-cylindrical-pure-gauge` passes eight exact checks in nonlinear base
and fiber coordinates. It is an infrastructure oracle, not the inherited
rotating solution; independent recovery of that source and normalization map
is the remaining V-T1/V-T2 entrance task.

### V-T2 — positive Kaluza benchmark

Rebuild the rotating dyonic `a=√3` example and verify the full pipeline:
algebraic fingerprint, scalar branch, differential obstruction pair,
`a_geom²=3`, potential orbit, and Ricci-flat uplift.

### V-T3 — non-Kaluza EMD control

Use a comparable `a²≠3` exact EMD solution. It should pass the generic EMD
reconstruction conditions while returning its non-Kaluza coupling magnitude
and refusing the five-dimensional vacuum-Kaluza exit.

### V-T4 — adversarial and degenerate suite

- reject scalar-plus-fluid and other mixed-matter false positives;
- distinguish algebraic from differential rejection;
- route null fields, zero Ricci trace, `q=0`, repeated roots, and eigenvalue
  collisions to named degenerate outcomes rather than generic constructors.

### V-G1 — generative moonshot

Only after V-T1--V-T4 are reproducible, impose the curvature-only conditions
on a tractable metric ansatz. A new exact Kaluza solution is the preferred
high-impact outcome; an overdetermination or no-go theorem is also a valid
research result.

## Publication decision points

1. **Uplift module paper:** IV-C1 plus the nonlinear covariance theorem and
   orbit classification may support a focused formal Kaluza-reduction paper.
2. **Generic reconstruction Paper I:** if II-G3 produces a sharp obstruction
   before universal existence, publish the conditional reconstruction theorem,
   discrete no-go result, and obstruction interface without claiming the
   north-star theorem.
3. **North-star paper:** reserve the full metric-only recognition claim for
   IV-N1.
4. **Phase-V companion:** exact benchmarks become a paper contribution only
   when they establish discrimination, expose a new branch, or generate a new
   solution; numerical agreement alone is a unit test.

## Immediate execution order

1. Instantiate `RealizedCurvatureScalarBranchPatch4` from the existing smooth
   projector/amplitude fields and their computed first jets; then pass every
   scalar-potential branch returned by the exact classifier to Phase III.
2. In parallel, use the operational V-T1 harness to recover the V-T2 rotating
   source and convention map; feed its exact jets through the same obstruction
   interface.
3. Compose IV-N1 once the realized branch list and downstream accepted/rejected
   orbits are connected; report a sharp obstruction or no-go theorem as a
   result, not as a failed proof.

No phase label advances merely because later infrastructure has started.
Claims advance only when their stated gate is proved and recorded in the
claim ledger.
