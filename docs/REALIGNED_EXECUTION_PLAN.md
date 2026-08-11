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

The first milestone is close. The second still crosses the genuine Phase-II
geometric seam: smooth curvature-projector realization, scalar-branch
closedness or obstruction, and the remaining Maxwell principal-plane input.
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
- The remaining metric realization has been decomposed and three ingredients
  are Lean-verified: the nonlinear inverse-metric jet product rule, the full
  differentiated first-kind pullback, and its undifferentiated raised
  contraction. The remaining endpoint is the differentiated-bracket
  contraction assembling them into the certified connection jet.
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

**Current substatus:** the transformed inverse-metric derivative, explicit
first-kind derivative, and undifferentiated raising/bracket contraction are
complete. Next prove the differentiated-bracket contraction and assemble the
unconditional theorem.

### IV-G2 — intrinsic local packaging

Package the finite-jet covariance result as a chart-independent local theorem
for the pseudo-Riemannian Kaluza metric. Reuse the proved overlap law instead
of rebuilding the component curvature calculation inside a large manifold
API. State all differentiability, signature, product-patch, and
circle-invariance hypotheses explicitly.

**Gate:** Ricci-flatness of the constructed local product is independent of
the normal/radial-gauge chart used to prove it.

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

### IV-C1 — assemble the conditional uplift theorem

Compose scalar integration, Maxwell unweighting, radial potential recovery,
the `a²=3` detector, intrinsic Ricci-flatness, converse reduction, and IV-O1.

**Gate:** a single theorem takes an accepted generic Phase-III orbit to the
complete local Ricci-flat uplift orbit and proves the converse, without an
unlisted chart or gauge choice.

## Upstream curvature gate for the official Phase-IV exit

### II-G1 — finish the algebraic entrance

- formalize the four-dimensional non-null Maxwell principal-plane
  multiplicities or isolate the exact literature theorem as a named input;
- complete the protected-eigenvector-to-characteristic-root assembly;
- keep algebraic false positives visibly rejected.

### II-G2 — instantiate smooth curvature projectors

Promote the evaluated Lagrange-projector and scalar-amplitude derivative
formulas to smooth Ricci tensor fields with their Levi--Civita derivatives.
Assemble curvature-derived one-forms `α,β` and explicit formulas for
`dα,dβ`.

### II-G3 — settle branch existence

Classify the two relative-sign candidates by the exact differential
obstructions. Prove one of the outcomes demanded by the Phase-II gate:

- a unique generic closed branch;
- a genuine two-uplift exceptional locus; or
- a sharp curvature obstruction proving that neither branch closes.

### IV-N1 — north-star composition

Compose II-G1--II-G3, the completed Phase-III decision interface, and IV-C1
into the finite-order curvature-only local recognition theorem. Every null,
repeated-root, zero-trace, and topological exclusion remains explicit.

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

1. IV-G1: the remaining nonlinear metric-second-jet identity.
2. IV-G1 corollaries and axiom audit.
3. IV-G2: chart-independent local-product packaging.
4. IV-O1: exhaustive uplift-orbit theorem.
5. IV-C1: assembled conditional forward/converse theorem.
6. Begin V-T1 while returning the main proof effort to II-G1--II-G3.
7. Attempt IV-N1; report an obstruction or no-go result as a result, not as a
   failed proof.

No phase label advances merely because later infrastructure has started.
Claims advance only when their stated gate is proved and recorded in the
claim ledger.
