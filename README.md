# Rainich–Kaluza reconstruction

This repository investigates a precise descendant of the classical Rainich
question:

> When does a four-dimensional Lorentzian metric encode, and allow one to
> reconstruct, the coupled scalar and Maxwell fields of the
> `a = √3` Einstein–Maxwell–dilaton sector obtained from five-dimensional
> vacuum Kaluza gravity?

The project is intentionally narrower than a new unified-field proposal. Its
first goal is a necessary-and-sufficient local reconstruction theorem on a
clearly stated generic branch, together with a classification of the branches
where that theorem fails or changes form.

## Current verified surface

The Lean development currently proves the coefficient algebra underlying the
candidate Ricci fingerprint and the generic pointwise reconstruction layer:

- expansion of the proposed characteristic factorization;
- existence of the protected `±q` polynomial roots;
- a complete four-dimensional algebraic entrance theorem: trace zero and the
  non-null Maxwell square law force two rank-two principal projector ranges,
  any scalar rank-one perturbation retains `±q` eigenvectors, those vectors
  are roots of the actual Mathlib characteristic polynomial, and its
  canonically extracted coefficients have the proposed quadratic
  factorization;
- vanishing of `C_KK = e₁²e₄ - e₁e₂e₃ + e₃²` for factored data;
- recovery of `q² = -e₃/e₁` on the nonzero-trace branch;
- an exact perfect-fluid-spectrum adversarial check;
- an explicit obstruction-zero false positive with no real protected pair,
  proving that the polynomial condition alone is insufficient;
- forced generic-eigenbasis scalar-block diagonals and automatic trace
  compatibility;
- exact real rank-one and Lorentzian signature-aware scalar-factorization
  criteria for the complementary two-dimensional block;
- uniqueness of scalar components for a fixed nondegenerate block up to the
  unavoidable global sign;
- a two-branch classification showing that pointwise curvature data admit a
  second, distinct scalar tensor under a relative component sign flip;
- realization of that ambiguity by an involutive spectral reflection which
  commutes with the Ricci block;
- an exact first differential-selection result: both relative-sign covector
  branches can satisfy a linear closure condition only when their spectral
  pieces satisfy it separately;
- a Phase-I differential-coupling layer proving that either nonzero rescaled
  Maxwell channel uniquely fixes the signed EMD coupling after scalar
  orientation is chosen, while `a²` is orientation invariant;
- a coordinate-free bilinear formula for `a²` on non-null differential
  channels, with primal/dual agreement;
- an explicit polynomial spectral projector and reflection for two-root
  invariant blocks, requiring no chosen eigenvectors;
- full four-root Lagrange projectors which commute with the Ricci operator,
  extract each eigenspace component, are idempotent, and resolve the identity
  under an explicit simple-spectrum decomposition hypothesis;
- the basis-free spectral-derivative identities reconstructing every
  off-diagonal projector derivative from the Ricci derivative divided by an
  eigenvalue gap, including the complete four-block sum and no dependence on
  eigenvalue derivatives;
- explicit evaluated derivatives for the curvature-derived `q²`, scalar
  diagonals, and nonzero scalar amplitudes;
- smooth coordinate Lagrange-projector fields on every explicit
  simple-spectrum patch, with pointwise idempotence and four-projector
  resolution inherited from the basis-free construction;
- a coordinate Levi--Civita specialization of the complete spectral-projector
  derivative, including the proof that ordinary differentiated
  idempotence/eigen-equations automatically become the required covariant
  identities;
- smooth fixed-probe curvature eigen-one-forms, smooth reconstructed scalar
  amplitudes, and a concrete scalar branch jet whose exterior obstructions are
  the explicit product-rule forms `dα,dβ`, with branch tests `dα±dβ`;
- an exhaustive four-way branch classifier: plus only iff
  `dα=-dβ≠0`, minus only iff `dα=dβ≠0`, both iff `dα=dβ=0`, and neither iff
  `dα` is neither equal nor opposite to `dβ`, including patch-level finite
  witnesses that reject both local branches;
- a field-level realization of that classifier: when the displayed
  curvature jets are the actual Frechet derivatives of the reconstructed
  spectral one-forms, obstruction vanishing is equivalent to genuine
  closedness, and on an open convex patch it is equivalent to existence of a
  local scalar potential; the resulting zero/one/two-potential list is
  exhaustive, while two finite witnesses rule out both potentials;
- an automatic constituent-field constructor for that realization:
  coordinate components reconstruct arbitrary scalar and one-form Frechet
  derivatives, while the product rule derives the full `d(xθ)` branch jet
  from the actual amplitude and eigen-one-form jets; the fixed-probe matrix
  derivative, timelike/spacelike normalization derivatives, and metric-dual
  derivatives generate both concrete eigen-one-form coordinate jets, while
  exact quotient and square-root differentiation generates both reconstructed
  scalar-amplitude jets; the resulting concrete fixed-probe constructor has
  no constituent derivative identities left as inputs;
- an exact Phase-III equivalence between the scalar reconstruction equation
  and the residual Maxwell square law, followed by eigenvector-free Maxwell
  principal-plane projectors on the non-null branch;
- a constructive canonical Maxwell duality-orbit classification, unique
  infinitesimal complexion rate, and simultaneous two-channel recovery of
  complexion and signed EMD coupling;
- an explicit antisymmetric Lorentzian two-form calculation producing the
  canonical Maxwell stress, energy sign, Hodge action, duality invariance, and
  a real seed for every positive residual magnitude;
- Lorentz-frame covariance of the seed and Maxwell stress, including
  preservation of the residual square law and principal-projector splitting;
- a constructive indefinite Gram--Schmidt theorem extracting a full
  pseudo-orthonormal principal tetrad from projected local probes on explicit
  open Gram-sign branches;
- a four-dimensional rank/signature theorem that supplies those probes
  pointwise, promotes the tetrad to a basis, and constructs a real skew
  two-form whose Maxwell stress is exactly the supplied residual;
- a `C^n` fixed-probe theorem producing a smooth tetrad, frame matrix, and
  transported Maxwell seed on every strict Gram-sign patch;
- an exact first-jet formula for the transported seed and Hodge seed,
  separating the `dq/(2q)` amplitude channel from a Lorentz-connection
  channel `Ω=(dL)L⁻¹`, with `ΩG+GΩᵀ=0`;
- an actual transported-seed calculus theorem: componentwise `C²` frame and
  positive magnitude fields with their coordinate `dL,dq` jets have exactly
  those electric/Hodge first derivatives, whose continuity is automatic;
  after the complexion product rule and exponential unweighting, every
  accepted branch yields the matching closed physical Maxwell field;
- an actual-field Phase-III constructor: all displayed jets can be the actual
  coordinate derivatives by definition, a `C¹` angle generates the unit
  cosine/sine complexion pair and its tangent equations, and smooth matrix
  projectors with strict fixed probes generate the smooth coframe candidate;
- a concrete curvature-principal constructor: `S=R-V` inherits the Maxwell
  square law from the scalar reconstruction equation, `q=sqrt(qSq)` is smooth
  and positive, its two polynomial projector fields are smooth complementary
  idempotents, and the fixed-probe tetrad is pointwise pseudo-orthonormal; in
  a Minkowski orthonormal trivialization its coframe is exactly Lorentz;
- a local exteriorization theorem producing alternating seed-channel
  three-forms and two explicit obstructions whose simultaneous vanishing is
  equivalent to the full EMD Bianchi/Maxwell closure equations;
- a genuine local scalar integration theorem on open convex patches, including
  analytic relative-sign branch selection and uniqueness of the scalar
  potential up to an additive constant;
- a paired curvature-to-Phase-III classifier: each concrete relative-sign
  candidate is either rejected by a nonzero scalar curvature matrix, rejected
  by a nonzero Maxwell `F`/`G` obstruction tensor, or accepted with both a
  scalar potential and vanishing Maxwell obstructions; all rejections retain
  explicit point witnesses and accepted branches expose the exact conditional
  uplift obligations;
- an audited Phase-IV handoff: the actual exponential weights have their
  required derivatives, accepted Phase-III data give a closed physical
  Maxwell field and weighted dual flux, and `a²=3` admits the positive
  `a=√3` scalar orientation;
- a constructive Phase-IV radial homotopy operator for the closed physical
  two-form, including radial gauge, an honest dominated
  differentiation-under-the-integral interface, the fundamental-calculus
  curvature identity for its derivative candidate, exact pointwise gauge
  freedom, and the field-level theorem that equal-curvature potentials differ
  by `dχ` with `χ` unique up to a constant;
- the closed Phase-IV.1 analytic splice: under a `C¹` closed regularity
  package on a star-shaped patch, the radial gauge potential is a genuine
  differentiable local potential with `dA=F`, every dominated
  differentiation-under-the-integral obligation discharged uniformly for all
  evaluation directions, and the complete local potential orbit is `A+dχ`;
- convention-independent Kaluza block-metric assembly, including symmetry,
  nondegeneracy from the base metric and nonzero warp factors, gauge invariance
  of both `dz+cA` and `u g+v(dz+cA)²`, and additive composition of gauge shifts;
- the uplift convention constants `c₁=-1/√3`, `c₂=2/√3`, `c₃=1` derived from
  the five-dimensional Einstein-Hilbert action, with Lean-verified
  Einstein-frame, scalar-normalization, and Maxwell-exponent conditions, a
  re-derivation of `a²=3` from the five-dimensional origin, and the
  convention-fixed block pairing inheriting symmetry, nondegeneracy, gauge
  invariance, and the additive-constant modulus law;
- the five-dimensional block-metric coordinate layer: the unipotent
  congruence factorization `ĝ = Pᵀ(u g ⊕ v)P`, explicit two-sided
  inverse-metric formulas, the determinant `det ĝ = u⁴·v·det g` with
  Lorentz-sign preservation at the derived convention, and the orthogonal
  family lift settling index-one signature at the trivialization level;
- the six closed-form Christoffel blocks of the warped Kaluza metric at a
  normal-gauge point, including the Maxwell shear whose prefactor is exactly
  the EMD weight `e^{√3φ}`, with torsion symmetry and consistency against
  the assembled block inverse;
- the second-jet curvature layer: assembled second metric derivatives, the
  certified inverse-metric derivative, the product-rule Christoffel
  derivative, the raw Ricci contraction, and all three Ricci
  blocks: `R̂₅₅` is the scalar equation, `R̂_{n5}` is the weighted Maxwell
  equation, and `R̂_{np}` is the Einstein residual plus the exact scalar
  trace correction. Mixed-order symmetry is proved for genuine second jets,
  and vanishing of the full `5×5` Ricci tensor is Lean-proved equivalent in
  both directions to the convention-fixed normal-frame EMD system;
- a smooth coordinate-germ realization: actual componentwise `C²` fields in
  normal coordinates and radial gauge assemble into a circle-invariant local
  product metric whose point value, first derivative, and complete Hessian are
  exactly the jets used by the Ricci-flatness/EMD equivalence;
- an exterior-form complexion theorem reducing both EMD equations to explicit
  seed channels, together with the generic collapse of constant duality to
  overall sign and its zero-coupling/inactive-source exceptions;
- an explicit duality transition group and overlap cocycle, including the
  exact variable-transition law `ω↦ω+τ`, an invariant corrected rate `ω-A`,
  and gauge-invariant recovery of the EMD coupling;
- the basis-independent square law for rank-one endomorphisms;
- a basis-independent theorem that a rank-one perturbation preserves an
  eigenvalue carried by a two-dimensional eigenspace, and hence conditionally
  protects the Maxwell `+q/-q` pair;
- the converse polynomial theorem that a nonzero protected opposite root pair
  forces the full `(x²-q²)` characteristic factor;
- a coordinate-free, noncommutative derivation of the Sylvester reconstruction
  equation, together with its invariance under Ricci-centralizing involutions.

These statements now complete the conditional generic local Phase-III Maxwell
decision interface: once an admissible scalar branch and its first jet are
supplied, the exact obstruction pair either rejects it or returns the local
Maxwell/coupling orbit. Phase IV.1 is closed: on a star-shaped
patch the `C¹` closed regularity package makes the radial gauge potential a
genuine differentiable local potential with `dA=F`, and the local potential
orbit is exactly `A+dχ`. The IV.2 uplift constants are derived from the
five-dimensional Einstein-Hilbert action and fixed as verified Lean
definitions. The development also does **not** yet prove that the original
fingerprint always supplies a closed scalar-gradient branch, cover the null or
repeated-root cases, or settle global bundle topology. The full IV.3
coordinate-jet reduction is now complete: the full five-dimensional Ricci
tensor vanishes if and only if the convention-fixed normal-frame EMD
Einstein, weighted Maxwell, and scalar residuals vanish. What remains before
claiming a local Ricci-flat uplift theorem is now narrower. The smooth
coordinate-germ wrapper extracts the jets from actual `C²` fields, derives all
mixed-partial symmetries by Schwarz's theorem, extends the assembled metric
circle-invariantly to a local product, and identifies its point value, first
derivative, and complete second derivative with the audited Kaluza jets. The
resulting curvature is now proved to be the ansatz-independent standard
coordinate Levi--Civita/Ricci contraction of those actual derivatives. The
affine coordinate seam is also closed for every invertible constant Jacobian,
including changes mixing base and circle directions, with Ricci-flatness
preserved and reflected. The universal inhomogeneous nonlinear connection and
Ricci cancellation is now proved for arbitrary coordinate three-jets as well.
The nonlinear metric endpoint is now complete: the affine first-kind and
inhomogeneous metric-Hessian/third-derivative product rules are proved
separately, assembled into the transformed Christoffel jet, and propagated to
unconditional coordinate-Ricci covariance and two-sided Ricci-flatness.
Consequently the genuine Kaluza local-product metric remains Ricci-flat iff
EMD after every invertible nonlinear coordinate three-jet, including changes
mixing base and circle directions. First-metric-jet symmetry is explicit where
the inverse-metric contraction requires it. The intrinsic local chart seam is
now closed in `IntrinsicKaluzaLocal.lean`: a symmetric nondegenerate
pseudo-Riemannian coordinate two-jet is extracted from the actual
componentwise `C²` product metric, the product-patch and circle-invariance
statements are explicit, and the normal frame displays signature
`(-,+,+,+,+)`. Ricci-flatness in any two invertible nonlinear overlap jets is
equivalent, and intrinsic local Ricci-flatness is equivalent to EMD. This is a
local product-germ theorem; it does not assert a global circle quotient or
global manifold topology. `KaluzaUpliftOrbit.lean` now also closes the local
uniqueness classification: equality under any product-preserving local fiber
coordinate jet is equivalent to exactly the warped-base, fiber-radius, and
connection compatibility laws. Gauge shifts, dilaton/radius rescaling, and
fiber reversal are named instances; the active duality orbit is exactly the
overall sign, while zero-coupling and inactive-source exceptional circles
remain explicit. `ConditionalKaluzaUplift.lean` now assembles the single
conditional forward/converse theorem. Its accepted-branch certificate states
the real abstraction seam—a scalar point normalization, post-unweighting `C¹`
closure, and a normal-gauge realizer—and the theorem performs normalized
scalar integration, radial potential
recovery, intrinsic uplift, converse reduction, and orbit closure without an
unlisted chart or gauge choice.

The current execution plan deliberately distinguishes completion of that
uplift module from the official curvature-only Phase-IV exit. The conditional
module is now complete, so exact metrics may enter a labeled Phase-V validation
track while the main theorem effort returns to the upstream curvature gate.
That validation track is now operational in `validation/`: a pinned
Python/SymPy exact-tensor engine records canonical inputs, source provenance,
runtime versions, residual hashes, and byte-for-byte checked JSON artifacts.
Its seed oracle places flat four- and five-dimensional geometry in nonlinear
cylindrical and pure-gauge Kaluza coordinates and passes eight exact checks.
This is computational evidence, deliberately separated from the Lean proof
surface; the rotating dyonic benchmark remains to be independently rebuilt.
The smooth curvature-projector and scalar-branch-form gate is now closed on
the stated simple-spectrum, strict-sign local patches. The exact jet and patch
decision is machine checked, and `CurvatureBranchIntegration.lean` proves its
precise analytic meaning for realized curvature fields: each candidate has a
local scalar potential exactly when its obstruction vanishes. This yields the
complete zero/one/two local potential list and a sharp no-potential
certificate without assuming that some branch exists. The normalized
fixed-probe eigen-one-form derivative pair is now complete: the matrix probe,
normalization scale, normalized vector, and metric dual are differentiated
explicitly for both signatures, and their coordinate jets feed the branch
constructor directly. The scalar-amplitude pair is now complete as well:
Lean differentiates the two rational reconstructed diagonals and their
signature-adjusted square roots, then identifies both actual coordinate jets
with the curvature formulas. The concrete smooth fields therefore generate
the realization and complete potential list with no derivative-identity
inputs. `CurvatureKaluzaComposition.lean` now carries that entire list through
the Phase-III Maxwell test: scalar and Maxwell rejections have explicit point
witnesses, while every accepted survivor has the two canonical exponential-
weight closure identities and a typed route into the conditional uplift
theorem. The remaining north-star seam is field-level and is now split
cleanly. `PhysicalMaxwellFieldRealization.lean` closes the
analytic promotion part of that seam: coordinate first jets become genuine
continuous-bilinear Frechet derivatives, coordinate closure upgrades to full
cyclic closure, and any actual rescaled `rotatedF` realization is
exponentially unweighted to the exact matching closed `C¹` physical Maxwell
package. `PhaseIIITransportedSeedCalculus.lean` now closes the remaining
analytic Maxwell step for actual smooth frame data: it proves both transported
electric/Hodge coordinate product rules from `C²` `L,q` and their displayed
`dL,dq` jets, derives jet continuity, constructs the rescaled realization,
assembles the duality rotation, and feeds the closed-field theorem. Its
actual-field constructor removes the remaining derivative bookkeeping: a
local angle supplies the unit complexion and all its derivatives, while
smooth fixed-probe matrix projectors supply the coframe candidate.
`PhaseIIICurvaturePrincipalData.lean` now constructs those projectors directly
from the curvature residual `S=R-V` and positive reconstructed `qSq`, proves
their structural identities, verifies the tetrad and Lorentz coframe, and
supplies a positive-cosine local angle chart. The remaining curvature seam is
to identify the accepted branch's concrete residual/self-adjoint metric data
and unit complexion coefficients with this certificate, then construct the
compatible normal-gauge `C²` EMD realizer.
See the
[`realigned execution plan`](docs/REALIGNED_EXECUTION_PLAN.md) for the ordered
proof obligations and publication decision points.

The current result also corrects an earlier uniqueness expectation: on the
genuinely two-component generic branch, curvature algebra determines the
scalar tensor only up to a discrete spectral-centralizer action. Differential
data are therefore essential, not merely a final consistency check.

## Why this is not a left-field problem

The project sits at the intersection of three established reconstruction
programs:

1. classical four-dimensional Rainich reconstruction of electromagnetism;
2. metric-only geometrization and reconstruction of scalar fields;
3. the `a = √3` Einstein–Maxwell–dilaton system obtained by Kaluza reduction.

The possible new contribution is the coupled reconstruction problem: recover
the scalar-gradient tensor and Maxwell sector simultaneously from curvature,
including the differential and degenerate conditions needed for a genuine
if-and-only-if theorem. See [the literature map](docs/LITERATURE_MAP.md) and
[Vibemathed positioning](docs/VIBEMATHED_POSITIONING.md).

## Build

Install `elan`, then run:

```sh
lake update
lake exe cache get
lake build
```

The Lean and Mathlib releases are pinned. Publication branches must contain no
`sorry`, `admit`, or project axioms in the claimed theorem surface.

Run the stronger local audit with:

```sh
bash scripts/audit.sh
```

The audit builds with warnings treated as errors before printing the axiom
surface.

Run the separate exact-metric validation audit with:

```sh
cd validation
./audit.sh
```

This uses the pinned interpreter and dependency lock, runs the tensor-engine
tests, and rejects any drift from the committed exact artifact.

GitHub CI additionally requests independent checking through `nanoda` while
forbidding `sorryAx`, then reproduces the pinned exact-metric artifact and
checks it for drift.

## Repository map

- `RainichKaluza/`: machine-checked definitions and theorems.
- `validation/`: pinned exact-symbolic Phase-V evidence and reproducibility
  artifacts, explicitly outside the Lean proof surface.
- `docs/RESEARCH_STATE.md`: inherited results, corrections, and open questions.
- `docs/PROGRAM_SYNTHESIS.md`: cross-conversation research map and adopted
  physics-first sequence.
- `docs/HIGH_IMPACT_PROGRAM.md`: north-star local uplift theorem, phased proof
  program, exact-solution tests, and kill criteria.
- `docs/REALIGNED_EXECUTION_PLAN.md`: current critical path through the
  Phase-IV uplift module, upstream curvature gate, and Phase-V validation
  track.
- `docs/PHASE_III_MAXWELL_RECONSTRUCTION.md`: proved residual entry point and
  the completed generic local two-form/complexion obstruction interface.
- `docs/PHASE_IV_UPLIFT.md`: verified Phase-IV entry contract and the
  two-form integration, convention, metric-assembly, and Ricci-flatness work
  packages.
- `docs/UPLIFT_CONVENTION.md`: derivation of the uplift constants
  `c₁, c₂, c₃` from the five-dimensional Einstein-Hilbert action.
- `docs/EMD_CONVENTION.md`: convention-fixed field-equation provenance.
- `docs/GENERIC_RECONSTRUCTION.md`: derivation and boundary of the current
  generic eigenbasis result.
- `docs/CLAIM_LEDGER.md`: exact claim classification and proof obligations.
- `docs/LITERATURE_MAP.md`: relation to known reconstruction results.
- `docs/VIBEMATHED_POSITIONING.md`: publication narrative and Lean contract.
- `docs/RELEASE_CHECKLIST.md`: public GitHub release boundary and audit list.
- `papers/paper-01/OUTLINE.md`: first-paper theorem architecture.
- `papers/paper-01/MANUSCRIPT.md`: self-contained public-release manuscript.
- `papers/paper-01/LEAN_MAP.md`: manuscript-to-Lean claim translation.
- `papers/paper-01/DRAFT_THEOREMS.md`: precise working statements and proof
  status for the first paper.
- `papers/paper-01/VIBEMATHED_SUBMISSION.md`: staged submission fields and
  verification disclosure.
- `RainichKaluza/AxiomAudit.lean`: printed axiom dependencies for advertised
  theorems.
- `ROADMAP.md`: staged research program.
- `RELEASE_NOTES.md`: draft pinned-release claim and verification boundary.
