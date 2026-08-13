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

## Current research focus

The repository was adversarially re-audited on 2026-08-12. The formal
infrastructure is substantial and builds without placeholders, but the full
metric-only recognition converse is not yet proved. The finite detector
itself takes only the metric. On the explicit active regular locus, packaged
physical EMD data now give an accepted survivor with output `a²`, and every
pointwise member of the finite accepted set is proved to return that same
physical value on the sharp unique scalar-closure locus. The final necessity
wrapper now composes conventional selector/regularity data with one
choice-free physical activity premise and returns a metric-only accepted
output `a²` (`3` for Kaluza). Exact complete-detector benchmarking, theorem
presentation, and the separate converse remain.

The active target is now sharp and testable: the complete first
curvature-seed derivative channels have an exact one-parameter shear kernel,
so the former third-order coupling claim is false. One derivative later,
constancy of the physical EMD coupling breaks that kernel on the active locus
and constructs `aGeomSq=A²+B²=a²` using metric derivatives through order four.
The compiled theorem says that every packaged Ricci--exterior EMD witness
satisfying the displayed regular and active hypotheses produces a survivor
of the explicit finite metric-only detector; on the unique scalar-closure
locus, every certified survivor returns the same `a²`. The former assumption that one projected
coordinate vector is timelike has now been removed. Six finite algebraic
pivot recipes extract a timelike direction from any projected pair with
negative Gram determinant, and the detector constructs its smooth principal
coframe from that metric-dependent choice. An arbitrary-basis theorem now
also proves that a rank-two Lorentzian projector range supplies such a pair
and both strict frame signs; the coordinate-matrix specialization and local
persistence of one fixed finite choice are also proved. Positive observer
energy now forces a timelike negative Maxwell range, while the square law and
trace force both ranges to have rank two; the detector consequently selects
the complete Maxwell frame on a neighborhood. The scalar coordinate probes
are now selected as well: idempotence and trace one certify rank-one
complementary projectors, intrinsic causal type forces an admissible projected
coordinate direction on each line, and normalized representatives are unique
up to sign. A stronger two-line theorem proves that every admissible projected
probe pair generates the same enumerated sum/difference metric-dual covector
orbit as the physical normalized eigenline representatives, up to one global
sign. The arbitrary-chart principal tensor transport now uses the true
dual coframe `E⁻¹`; the Maxwell gates and frame signs prove `LᵀηL=G`. A finite
orientation reflection fixes the electric seed, negates the Hodge seed, and
always selects a positive orientation. The explicit coordinate Hodge formula
is now proved exactly natural on that positive-determinant branch, and the
actual-metric wrapper derives exact Hodge compatibility directly from the
coframe metric and Maxwell/frame gates. The abstract EMD scalar-identifiability
theorem is now proved: the reconstruction equation in a generic
pseudo-orthonormal Ricci eigenbasis forces the amplitudes, kills the protected
components off resonance, and makes the finite probe list contain the physical
covector up to global sign. The projector/probe half of its actual-metric
instantiation is now complete: `ActualMetricScalarIdentifiability.lean`
proves that the actual metric gate, causal eigenlines, a generic Ricci
spectral frame, and the physical reconstruction equation make one literal
stored detector candidate equal to the physical covector up to global sign.
The choice-independent EMD Ricci witness, fixed-sign scalar germ, complete
upstream selector, exact positive-orientation Hodge naturality, and finite
orientation choice are now proved. The selector has now been promoted from a
base-point result to an honest fixed-choice open patch: assuming continuity at
the base point of the two strict reconstructed diagonal amplitudes and of the
selected coframe entries, the same raw choice retains its scalar `±` germ and
four frame signs and satisfies every upstream gate throughout a smaller open
neighborhood. Upstream entrance itself now proves `det L>0`, so positive
orientation and exact Hodge convention persist there without a separate
patch-selection premise. An adversarial audit also corrected a
vacuous quantifier:
genericity cannot hold for every enumerated wedge component, since diagonal
components vanish. The intrinsic active wedge now existentially selects one
finite generic channel. In parallel, constructive Maxwell stress-fibre
theorems prove the unit-duality orbit pointwise and its smooth realization on
any positive adapted patch where the coframe and stress identities hold
throughout the patch.
The selected actual-metric coframe algebra is now closed on every upstream
point (`L⁻¹L=LL⁻¹=1`, `L G⁻¹ Lᵀ=η`, and canonicalized residual), and
the corresponding patch theorem gives explicit smooth duality coordinates
for any smooth physical stress witness. A new germ-transfer theorem proves
that neighborhood equality of genuine physical and reconstructed `C¹` fields
also identifies their stored first jets and transfers both EMD exterior
equations to the reconstructed seed jet.
`NorthStarComposition.lean` now removes those neighborhood field equalities
as independent assumptions. On a positive selected patch, reconstructed
stress puts the physical Maxwell field in the smooth canonical duality orbit;
exact positive-orientation Hodge naturality then fixes its physical Hodge
partner with the same complexion. The two physical/reconstructed field germs,
their first jets, and the reconstructed EMD exterior channel therefore follow
from the physical stress and Hodge relations.
The quotient-derivative subproblem is now closed: a local physical channel
identity forces the literal quotient field and hence its actual Frechet
derivative to equal the physical double-angle field and derivative. The sole
selected actual-metric coframe is also proved Maxwell-adapted pointwise: it
conjugates the recovered residual to the canonical diagonal stress and hence
puts every physical stress witness in the canonical duality orbit. The scalar
germ and frame-sign germ are already retained. Consequently the conditional
actual-metric necessity theorem is now machine checked: on that smooth open
upstream patch, a genuine `C¹` Maxwell/Hodge pair with reconstructed stress,
the physical metric-Hodge relation, EMD exterior closure at an oriented
coupling with the same square as `a`, and an active wedge produces a finite
accepted choice with `aGeomSq=a²`. Its Kaluza specialization returns `3`.
`InvariantEMDDetectorComposition.lean` now packages a conventional,
detector-choice-free physical EMD patch and performs the sign-aligned
composition: it intersects the selected scalar `±` germ with the upstream
germ on one honest open patch, derives detector residual stress, replaces
`a` by `-a` on the negative scalar branch, and returns the invariant `a²`.
`InvariantEMDEndToEnd.lean` composes that result with the finite upstream
selector. Thus genuine physical EMD data imply that the metric-only accepted
set is nonempty and contains a survivor returning `a²` (`3` at Kaluza
coupling), conditional only on the stated selected regular-locus hypotheses.
`ActualMetricDetectorRegularity.lean` and
`InvariantEMDRegularityEndToEnd.lean` remove the bespoke selected-coframe and
positive-magnitude `C²` premises: on the selected upstream patch they derive
both from ordinary `C²` regularity of `g`, the reconstructed residual, and
`qSq`. `PhysicalComplexionInvariant.lean` closes the other entrance seam. It
constructs the choice-free physical complexion covector
`(C dS - S dC)/2` directly from the physical Maxwell/Hodge pair, inverse
metric, and positive stress magnitude; proves frame and simultaneous field-
sign invariance; derives the physical effective channel without selecting a
source; and identifies detector activity exactly with a choice-free physical
Maxwell-complexion/stress wedge condition before finite source/wedge
selection. `InvariantActiveWedgeOpenness.lean` further proves that this
choice-free active locus is open for continuous physical data and persists
locally from pointwise continuity. No density claim is made.

`InvariantEMDConfluence.lean` now proves the sharp pointwise all-survivor
statement: on the explicit unique scalar-closure locus
`¬(O_false = 0 ∧ O_true = 0)`, every member of the finite accepted set, under
the displayed ordinary local regularity and admissible-probe hypotheses,
returns the physical `a²`. Hence all survivors agree there. The exclusion is
essential: when both scalar branches close, the present hypotheses do not
identify one physical branch, so unconditional confluence is neither proved
nor claimed. `InvariantEMDPublicationCorollaries.lean` packages the exact
per-survivor certificate and proves that nonemptiness plus one certificate for
every accepted survivor makes the complete finite output image exactly
`{a²}`. `InvariantEMDPhysicalActiveEndToEnd.lean` completes necessity
nonemptiness on the explicit active regular locus: its callback asks only for
selected-residual `C²`, and its sole activity premise is the choice-free
physical Maxwell-complexion condition. The immediate tasks are exact benchmark
routing and manuscript presentation, followed separately by the converse.
The first complete routing audit found that the original helical point fails
the detector's causal scalar-radicand gate, despite passing the physical EMD
channel. A replacement point passes the exact prefix through literal scalar
reconstruction and its selected closure obstruction, but is not yet a
certified accepted detector instance. No new
exact Kaluza spacetime has been discovered.

[`docs/RESEARCH_RESET.md`](docs/RESEARCH_RESET.md) is the single operational
plan. The older high-impact and realigned phase documents are historical
records of the verified surface, not competing priority lists.

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
- a constructive canonical Maxwell duality-orbit classification and unique
  infinitesimal complexion rate, together with a corrected coupling result:
  the complete seed channels uniquely recover the effective pair `(eta,A)`
  but are never injective in the physical `(dtheta,B)` variables because of
  an exact shear; the next-order constancy equation generically reconstructs
  `B`, and the explicit fourth-order constructor returns `A²+B²=a²`; the
  witness-free implementation filters at most 64 raw source/wedge choices,
  retains all unused components as obstruction equations, constructs `dA` by
  actual Frechet differentiation of the channel-derived `A`, and proves
  open-patch confluence across every accepted choice;
- a completely finite actual-metric detector boundary: actual coordinate
  metric jets construct mixed Ricci, characteristic roots and projectors,
  scalar candidates, residuals, principal coframes, raw fourth-order
  channels, and `dA`; the accepted set tests the full algebraic, signature,
  scalar-closure, reconstruction, Maxwell-projector, metric-Hodge, Gram-sign,
  and next-order equations without taking a matter field, coupling,
  complexion, or EMD equations as inputs;
- an explicit coordinate metric Hodge star with a canonical Minkowski
  convention theorem, scalar-orientation invariance of `aGeomSq`, full
  metric-level source/wedge component confluence for a fixed geometric
  branch, accepted-branch physical correctness `aGeomSq=a²`, and the Kaluza
  selector `aGeomSq=3`;
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

These statements complete a conditional generic local Phase-III Maxwell
decision interface, but the former interpretation of its evaluated
two-channel pair as direct physical coupling recovery was valid only in an
aligned complexion gauge. The new full-channel no-go and fourth-order
recovery theorem give the correct invariant interpretation. Phase IV.1 is
closed: on a star-shaped
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

The current execution plan deliberately distinguishes the fourth-order
necessity detector, the later full local converse, and completion of the
conditional uplift module. The conditional
module is now complete, so exact metrics may enter a labeled Phase-V validation
track while the main theorem effort returns to the upstream curvature gate.
That validation track is now operational in `validation/`: a pinned
Python/SymPy exact-tensor engine records canonical inputs, source provenance,
runtime versions, residual hashes, and byte-for-byte checked JSON artifacts.
Its suite now contains: the flat nonlinear/pure-gauge seed; a nonzero-field
boosted black string; an exact `a²=1` dilaton black hole that reconstructs `1`
and is rejected as Kaluza; a generic helical Schwarzschild-string quotient
with four real simple Ricci roots that reconstructs `aGeomSq=3`; and a paired
second-jet near miss rejected by the polynomial obstruction. All use exact
arithmetic and drift-checked artifacts. This is computational evidence,
deliberately separated from the Lean proof surface. The routing artifact also
records that the original helical point has an empty complete-detector set;
its `3` is a physical-channel result. The actual-metric finite
detector is now constructed. At the transported curvature-seed boundary Lean
now proves the missing necessity implication: genuine local EMD exterior
closure rotates back to the detector's canonical physical channel; on the
positive-`q`, nonzero-source, nondegenerate-wedge locus the finite transported
detector is nonempty, and every accepted branch returns `a²`. The same result
is composed with the actual metric fields, so a genuine realization of those
constructed fields implies the former packaged compatibility predicate and
the Kaluza output `3`. The remaining central claim is therefore narrower. The
actual-metric polynomial-projector/probe instantiation, choice-independent EMD
Ricci witness, fixed scalar germ, complete upstream choice, and exact
positive-orientation Hodge gate are proved. `NorthStarComposition.lean` now
proves conditional complete nonemptiness from a genuine `C¹` physical
Maxwell/Hodge pair on a smooth upstream patch with
reconstructed stress, the physical Hodge relation, EMD closure, and an active
wedge. Stress plus positive orientation plus the physical Hodge relation
derive the formerly assumed physical/reconstructed field germs. The
fixed-choice neighborhood-promotion theorem now constructs the required open
upstream patch and positive determinant from the choice-independent EMD Ricci
patch, retained scalar/frame germs, and continuity of the two diagonal
amplitudes and coframe entries. `InvariantEMDDetectorComposition.lean` now
adds the detector-choice-free genuine EMD physical patch, intersects its
scalar and upstream germs, and handles both scalar/coupling signs.
`InvariantEMDEndToEnd.lean` composes the finite selector with that theorem and
proves accepted-set nonemptiness with output `a²` (or `3`).
`ActualMetricDetectorRegularity.lean` and
`InvariantEMDRegularityEndToEnd.lean` derive the formerly selected `C²`
coframe/magnitude data from conventional `C²` metric, residual, and `qSq`
regularity on the selected upstream patch. `PhysicalComplexionInvariant.lean`
constructs the choice-free physical complexion one-form and proves that its
physical stress wedge is exactly the detector active gate, closing the
effective-channel/complexion seam. Finally, `InvariantEMDConfluence.lean`
proves that every pointwise accepted survivor returns physical `a²` on the
sharp unique scalar-closure locus, under the displayed local regularity and
probe hypotheses. `InvariantEMDPhysicalActiveEndToEnd.lean` composes these
entrance ingredients and proves final metric-only accepted-set nonemptiness
with output `a²`; its Kaluza corollary returns `3`. The exact complete-detector
benchmark, theorem presentation, and converse remain.
The finite detector now enriches each projected Lorentzian coordinate pair
with six metric-dependent pivot recipes. Any negative-Gram pair provably
yields a timelike pivot and valid companion, including charts where no
individual projected coordinate vector is timelike, and the smooth recipe is
integrated into the principal-coframe constructor. A rank-two Lorentzian
projector range is now proved to obtain such a pair from every ambient basis.
The pointwise coordinate-matrix bridge is also closed. The analogous
rank-one arbitrary-chart theorem now selects both scalar eigenline probes
from the checked projector identities and invariant causal type, with local
persistence and uniqueness up to sign. The two-line projected-probe theorem
also proves that the finite relative-sign list exhausts the physical
metric-dual covector orbit once its two spectral components and amplitudes are
identified. `PhysicalScalarIdentifiability.lean` now derives those magnitudes,
protected-root vanishing, two-line support, and final finite-probe recovery
from the generic spectral-frame reconstruction equation.
`ActualMetricScalarIdentifiability.lean` instantiates its projector, rank,
causal-line, and coordinate-probe hypotheses at the actual metric formulas and
returns the detector's stored candidate itself. Those spectral-frame,
reconstruction, exact positive-orientation Hodge, and selector-composition
steps are now closed. The selected patchwise physical-field identification is
also derived in `NorthStarComposition.lean` from reconstructed stress,
positive coframe orientation, and the physical Hodge relation. The same fixed
raw choice is now promoted to an open upstream neighborhood, and upstream
itself implies positive determinant there. Finite-coordinate necessity is now
composed through a detector-choice-free EMD physical patch, including the
correlated scalar/coupling sign. Its former regular-locus seams—the selected
`C²` coframe/magnitude hypotheses and the physical effective-channel/
complexion covector—are now closed: conventional regularity derives
the selected analytic data, the choice-free physical complexion module
derives the active channel, and pointwise all-survivor correctness holds on
the unique scalar-closure locus. The physical-active end-to-end theorem now
composes these results into accepted-set nonemptiness.
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
theorem. The analytic parts of the former field-level north-star seam were
split cleanly before their final composition.
`PhysicalMaxwellFieldRealization.lean` closes the analytic promotion step:
coordinate first jets become genuine
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
supplies a positive-cosine local angle chart. The curvature input was then
narrowed further. `CurvatureScalarContribution.lean` constructs the selected
branch's actual `V^i_j=(1/2)g^{ik}v_kv_j` from the inverse metric and proves
its trace square law, smoothness, and metric self-adjointness, so the residual
self-adjointness is automatic. In the generic canonical Ricci frame the same
module now derives the full reconstruction equation from the two scalar
amplitude identities and transports it through an arbitrary certified frame.
The actual smooth seed handoff also retains
the closed positively weighted Hodge channel alongside the physical Maxwell
field. The exterior-channel and fourth-order `(A,B,eta)` implication is now
closed once those actual metric-constructed fields are a genuine EMD
realization. Equality of genuine physical and reconstructed `C¹` field germs
transfers their stored first jets and both exterior equations, and
`NorthStarComposition.lean` now derives those germs from the physical stress
and Hodge relations on a positive adapted patch. Its conditional theorem
already yields a finite accepted choice with output `a²` (and `3` under
Kaluza normalization). The fixed-choice selector now supplies an honest open
upstream patch and positive determinant under explicit diagonal-amplitude and
coframe continuity. The invariant composition modules place the conventional
physical `C¹` pair, stress, Hodge relation, and closure on that patch and align
the scalar/coupling `±` sign. Conventional regularity now derives the selected
`C²` coframe/magnitude data, and the choice-free physical complexion module
derives the effective channel and exact activity equivalence. Pointwise all-
survivor correctness is proved on unique scalar closure; the two-closed-branch
locus is explicitly excluded. The compatible normal-gauge `C²` EMD realizer
belongs to the later converse and is not an input to the necessity detector.
Necessity composition is closed; complete benchmark routing and theorem
presentation now precede the separate converse.
See the [`research reset`](docs/RESEARCH_RESET.md) for the active theorem,
forbidden-input audit, exact-metric gates, and publication decision points.

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
- `docs/RESEARCH_RESET.md`: single operational plan, metric-only detector
  theorem, forbidden inputs, validation gates, and kill criteria.
- `docs/RESEARCH_STATE.md`: inherited results, corrections, and open questions.
- `docs/PROGRAM_SYNTHESIS.md`, `docs/HIGH_IMPACT_PROGRAM.md`, and
  `docs/REALIGNED_EXECUTION_PLAN.md`: archived redirects retained for old
  links; historical content is available through git history and is not an
  operational task source.
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
- `papers/coupling-detector/HUMAN_PROOF.md`: active proof draft for the exact
  third-order shear obstruction and generic fourth-order recovery theorem.
- `RainichKaluza/AxiomAudit.lean`: printed axiom dependencies for advertised
  theorems.
- `ROADMAP.md`: compact task-level view of the active research reset.
- `RELEASE_NOTES.md`: draft pinned-release claim and verification boundary.
