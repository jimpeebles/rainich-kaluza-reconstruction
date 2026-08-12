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
The second milestone has crossed the scalar-branch and pointwise Maxwell
decision seams. The Maxwell field-realization layer is now complete for an
actual smooth frame/magnitude certificate: `C²` fields `L,q` with their actual
coordinate jets canonically produce the rescaled first jet and hence the
matching closed `C¹` physical two-form. The concrete curvature-residual frame
and magnitude bridge is now also available: `S=R-V`, the scalar
reconstruction equation, and positive `qSq` produce smooth complementary
Maxwell projectors, the positive magnitude, and a verified
pseudo-orthonormal/Lorentz fixed-probe frame. A positive-cosine chart
constructs the local complexion angle from a unit coefficient pair. The
canonical Ricci frame now proves the full scalar reconstruction equation and
certified frame transport preserves it. The remaining substantive boundary is
identifying the actual curvature/scalar fields with that transported canonical
pair and identifying the curvature-selected unit complexion/Hodge relation
with the residual certificate, then constructing the compatible normal-gauge
`C²` EMD realizer. The selected branch covector now constructs its actual
mixed scalar tensor and self-adjoint residual directly, and both exterior EMD
channels survive the genuine `C¹` field handoff rather than being re-assumed
downstream. The former Maxwell principal-plane input has also been discharged
algebraically from dimension four, trace zero, and the non-null square law.
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
- The concrete scalar list is now composed with the Phase-III obstruction
  test. Every branch carries either a scalar matrix witness, a Maxwell
  three-form-channel witness, or a Phase-III acceptance certificate; accepted
  branches also carry the exponential-unweighting closure identities and map
  to an explicit conditional-uplift completion type.
- The accepted-jet analytic bridge is complete.
  `PhysicalMaxwellFieldRealization.lean` converts coordinate matrices and
  first jets to continuous bilinear forms, upgrades coordinate exterior
  closure to arbitrary directions, proves the exponential product-rule
  derivative and its continuity, and constructs the exact matching closed
  `C¹` physical Maxwell package. The downstream uplift interface is reduced
  to the Kaluza coupling check and normal-gauge `C²` EMD realizer.
- The transported-seed calculus and rescaled realization are complete for
  actual smooth frame data. `PhaseIIITransportedSeedCalculus.lean` proves the
  positive square-root derivative, the finite product rule for both
  `LᵀFcan(q)L` seed channels, and equality with the displayed `dL,dq` jets.
  `C²` regularity supplies jet continuity automatically; the duality rotation
  and exponential unweighting then produce the closed physical Maxwell field.
  No matrix norm or new Maxwell equation is assumed.
- Actual-derivative and complexion bookkeeping are also complete. The patch
  can define `dL,dq,dc,ds` as actual coordinate derivatives; a `C¹` angle
  supplies `c=cos θ`, `s=sin θ`, `ω=dθ`, the unit-circle law, and both tangent
  equations. Componentwise `C²` matrix projectors with strict fixed probes
  supply the smooth tetrad/coframe candidate.
- The curvature-residual projector bridge is complete. The actual field
  `S=R-V` inherits the Maxwell square law from the scalar square law and
  reconstruction equation; `q=√qSq` is smooth and positive; its two
  polynomial projectors are smooth complementary idempotents. Residual
  self-adjointness and strict fixed probes verify the pseudo-orthonormal
  tetrad, and a Minkowski orthonormal trivialization gives `L G Lᵀ=G`.
  The positive-cosine chart `θ=atan(s/c)` smoothly recovers every unit pair.
- The accepted scalar-contribution bridge is explicit. A certified inverse
  metric raises the chosen branch covector and constructs
  `V^i_j=(1/2)g^{ik}v_kv_j`; Lean proves its rank-one trace square law,
  smoothness, metric self-adjointness, residual self-adjointness, and the
  residual square theorem without a separately supplied scalar square law.
- The generic canonical Ricci frame proves the full reconstruction equation
  from the two forced scalar amplitudes and `qSq=q²`; a separate theorem
  preserves it under every certified two-sided frame transport.
- The actual field handoff retains both Phase-III exterior channels. The
  unweighted physical Maxwell form and positively weighted rotated Hodge flux
  are genuine closed `C¹` two-form fields with exact seed identities. The
  remaining Maxwell seam is the metric-Hodge identification, not closure.
- The next curvature-entry step is to identify the actual mixed Ricci and
  selected scalar fields with the transported canonical pair, identify the
  selected complexion and Hodge channel with the residual certificate, and
  reduce the compatible normal-gauge realizer equation by equation. That
  realizer remains the principal downstream risk.

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
the actual Frechet derivative of its spectral one-form field, and RK-R2p
reduces that realization to constituent coordinate-jet identities. RK-R2q
supplies the two normalized fixed-probe eigen-one-form identities, and RK-R2r
supplies the two reconstructed scalar-amplitude identities. The complete
concrete constituent patch now has no derivative-identity inputs.

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
`CurvatureEigenOneFormDerivative.lean` now differentiates the fixed matrix
probe, metric contraction, reciprocal square-root normalization, normalized
vector, and metric dual for both signatures. Its coordinate specializations
identify the actual timelike and spacelike eigen-one-form jets.
`CurvatureScalarAmplitudeFieldDerivative.lean` differentiates both rational
spectral diagonals and the signature-adjusted square-root amplitude fields;
their coordinate specializations are exactly the displayed reconstructed
amplitude one-forms.

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
out both potentials. No existence assumption is made. RK-R2p now removes the
derived product-rule assumption: coordinate components reconstruct arbitrary
scalar and one-form Frechet derivatives, and
`CurvatureScalarBranchComponentPatch4.ofCoordinateFDerivs` automatically
builds the realized branch certificate and exact potential list from the
constituent amplitude/eigen-one-form jets. RK-R2q further provides
`ofFixedProbeCurvatureEigenCovectors`, which inserts the two actual normalized
fixed-probe coordinate jets directly. RK-R2r differentiates the rational
reconstructed diagonal fields and their signature-adjusted square roots,
identifies both actual amplitude coordinate jets, and provides
`ofConcreteFixedProbeCurvatureFields`. Thus all four RK-R2p constituent
identities are discharged for the concrete smooth fields, and the exact
zero/one/two-potential list is available automatically. Downstream HC1 now
tests each surviving branch rather than deciding scalar integrability.
`CurvatureKaluzaComposition.lean` performs that test for both branches,
retains finite scalar/Maxwell rejection witnesses, proves the exponential-
weight closure identities for accepted survivors, and maps each survivor to
the precise remaining field-level obligations of `AcceptedKaluzaBranchAt`.

### IV-N1 — north-star composition

Compose the concrete II-G2/RK-R2p--RK-R2r zero/one/two-potential branch list,
the completed Phase-III decision interface, and IV-C1 into the finite-order
curvature-only local recognition theorem. Every rejected branch and every
null, repeated-root, zero-trace, and topological exclusion remains explicit.

**Official Phase-IV gate:** IV-G1, IV-G2, IV-O1, IV-C1, and IV-N1 are all
complete. A conditional uplift theorem alone does not close this gate.

**Status: decision composition, smooth-frame paired Maxwell realization,
residual principal data, and the actual branch scalar-contribution layer
complete; reconstruction/Hodge identification and normal-gauge realization
open.** RK-R2s
now supplies the complete accepted/rejected branch tree from the concrete
fixed-probe fields through the Phase-III obstruction pair and into the
conditional-uplift interface. RK-R2t proves that any actual matching rescaled
first-jet realization produces the required closed `C¹` physical Maxwell
field and reduces the remaining uplift interface accordingly. RK-R2u reduces
that realization to scalar seed calculus, and RK-R2v discharges the two
transported-seed coordinate derivative identities and jet continuity from
actual `C²` `L,q` fields and their displayed `dL,dq` coordinate jets. RK-R2w
further makes every derivative array actual by construction, generates
the unit complexion and tangent equations from a `C¹` angle, and obtains the
smooth coframe candidate from componentwise `C²` matrix projectors and strict
fixed probes. RK-R2x constructs the actual residual projectors and positive
magnitude from `S=R-V` and `qSq`, verifies the pseudo-orthonormal and Lorentz
frame identities, and supplies a positive-cosine local angle chart. IV-N1
remains open. RK-R2y retains both closed exterior channels as actual `C¹`
fields. RK-R2z constructs `V=(1/2)v^sharp tensor v` from the selected branch
and a certified inverse metric, proving its square law, smoothness, and
self-adjointness and hence residual self-adjointness automatically. The
generic canonical Ricci frame now also supplies the full reconstruction
equation from its two scalar amplitude identities, and arbitrary certified
frame transport preserves that equation. The remaining steps are to identify
the actual mixed Ricci and scalar fields with that transported canonical pair,
identify the curvature-selected complexion/metric-Hodge channel, and construct
the normal-gauge `C²` EMD realizer.

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

1. **Complete:** compose the concrete zero/one/two-potential list with the
   Phase-III Maxwell obstruction interface, preserve every scalar/Maxwell
   rejection witness, and map every survivor to the conditional-uplift
   obligations (RK-R2s).
2. **Complete at the analytic promotion layer:** promote an accepted
   survivor's realized rescaled first jet to the matching post-unweighting
   `C¹` physical Maxwell field package, retaining the coordinate seed
   equality (RK-R2t).
3. **Complete (RK-R2u--RK-R2v):** actual `C²` `L,q` fields and their `dL,dq`
   coordinate jets construct `PositiveQPhaseIIIRescaledMaxwellC1Realization`
   and the accepted branch's closed physical Maxwell field.
4. **Complete (RK-R2w):** actual derivative arrays, angle-generated unit
   complexion data, and smooth fixed-probe coframe construction require no
   further calculus hypotheses.
5. **Complete at the residual principal-data layer (RK-R2x):** `S=R-V`,
   `q=√qSq`, the smooth complementary projectors, verified fixed-probe
   tetrad/Lorentz coframe, and positive-cosine local angle chart compose.
6. **Complete (RK-R2y--RK-R2z):** retain both closed exterior channels as
   genuine `C¹` fields; construct the selected branch's actual mixed scalar
   tensor from `v` and the inverse metric; discharge its square law,
   smoothness, and self-adjointness and the residual self-adjointness.
7. **Complete at the canonical algebra/transport layer:** derive the full
   reconstruction equation from the generic canonical Ricci roots and scalar
   amplitudes and prove its invariance under a certified spectral frame.
8. Identify the actual mixed Ricci and branch scalar fields with that
   transported canonical pair, identify the curvature-selected unit
   complexion/Hodge pair with the residual certificate, then reduce and
   construct the compatible normal-gauge `C²` EMD realizer and finish IV-N1;
   report a sharp obstruction or no-go theorem as a result, not a failed proof.
9. Use the operational V-T1 harness to recover the V-T2 rotating source and
   convention map, then feed its exact jets through the new paired classifier.

No phase label advances merely because later infrastructure has started.
Claims advance only when their stated gate is proved and recorded in the
claim ledger.
