# High-impact Rainich--Kaluza program

Date adopted: 2026-08-10

Execution was realigned on 2026-08-11. The operational order, dependency
gates, and the distinction between uplift-module completion and the official
curvature-only Phase-IV exit are maintained in
[`REALIGNED_EXECUTION_PLAN.md`](REALIGNED_EXECUTION_PLAN.md).

## North-star result

The project now aims at a constructive local recognition theorem of the
following form.

> On an explicitly stated generic Lorentzian branch, a four-dimensional
> metric is locally the circle reduction of a five-dimensional Ricci-flat
> metric if and only if it satisfies a finite list of intrinsic curvature and
> curvature-derivative conditions. When the conditions hold, the scalar,
> Maxwell duality orbit, EMD coupling magnitude, and five-dimensional metric
> can be constructed locally from the four-dimensional metric. The theorem
> classifies all discrete and degenerate ambiguities.

This statement is a target, not a current theorem. Its value would be the
coupled and constructive nature of the result: separate scalar and Maxwell
geometrization theorems are known, but the Ricci tensor here contains only
their sum.

## What would count as a field-level contribution

The work should produce at least one of the following, preferably the first
two together:

1. a finite-order necessary-and-sufficient metric-only Kaluza uplift theorem;
2. an intrinsic differential reconstruction of the EMD coupling magnitude
   `a²`, with Kaluza gravity recognized by `a²=3`;
3. a uniqueness theorem or a genuine two-uplift theorem for the discrete
   scalar reflection branches;
4. a new exact Kaluza solution generated from the curvature-only conditions;
5. extraction of hidden scalar multipoles from four-dimensional curvature,
   confirmed on exact rotating solutions and tied to a clean observable.

Lean verification is a correctness multiplier for these results. It is not a
substitute for their mathematical-physics novelty.

## Generic branch for the first theorem

The initial local theorem may assume:

- a smooth four-dimensional Lorentzian manifold;
- non-null Maxwell sector, so the Maxwell stress has real `+q` and `-q`
  principal planes with `q>0`;
- nonzero, non-null scalar gradient;
- real diagonalizable mixed Ricci endomorphism with the required spectral
  gaps and no extra eigenvalue-sum resonances;
- constant ranks and smooth spectral projectors on a simply connected
  neighborhood.

Every excluded branch must be listed. None may be silently absorbed into the
word “generic.”

## Phase I — recover the differential coupling

Use the convention-fixed action

`L = √(-g)[R - ¼ exp(aφ) F² - ½(dφ)²]`.

Define

`v=dφ`, `𝓕=exp(aφ/2)F`.

The Bianchi and Maxwell equations become

`d𝓕 = (a/2) v∧𝓕`,

`d(*𝓕) = -(a/2) v∧(*𝓕)`.                              (HC1)

Unlike the pointwise Einstein equation, (HC1) contains `a` explicitly. The
first goal is to express all four terms in (HC1) through reconstructed
curvature data and prove:

- existence of a common constant coupling is an intrinsic differential
  condition;
- on a nondegenerate wedge channel that coupling is unique after fixing the
  global orientation of `v`;
- changing `v→-v` changes `a→-a`, so the convention-independent metric datum
  is `a²`;
- the Kaluza branch is selected by `a²=3`.

### Phase-I exit criterion

An explicit curvature-derived compatibility tensor or scalar `a_geom²`, a
proof of its branch behavior, and positive/adversarial exact-metric tests.

Current status: the rescaled identities are convention-checked, and Lean
proves abstract uniqueness of the signed coupling on either nonzero channel,
an explicit linear-probe recovery formula, and invariance of `a²` under the
global scalar-orientation reversal. On the non-null three-form branch, Lean
also verifies the coordinate-free Lorentzian-pairing formulas

`a = 2⟪d𝓕,v∧𝓕⟫ / ⟪v∧𝓕,v∧𝓕⟫`,

`a² = 4⟪d𝓕,d𝓕⟫ / ⟪v∧𝓕,v∧𝓕⟫`,

including agreement of the primal and dual channels. Reconstruction of these
channel data from curvature is the next step.

## Phase II — settle differential branch selection

Construct the two smooth scalar covector candidates from spectral projectors,
not from a chosen eigenbasis. For candidates `v₊=α+β` and `v₋=α-β`, the
repository already proves abstractly that both can be closed only if
`dα=dβ=0`.

The remaining curvature work is to:

- express `dα` and `dβ` through curvature and derivatives of the projectors;
- prove whether generically zero, one, or two branches satisfy closure and
  (HC1);
- classify the exceptional separately integrable locus.

Current status: on any invariant block obeying `(R-aI)(R-bI)=0`, the
eigenvector-free polynomial `Pₐ=(R-bI)/(a-b)` is Lean-verified to be an
idempotent commuting with `R` and to generate the corresponding involutive
reflection. More importantly, the full simple-spectrum Lagrange projector

`Pₐ=((a-b)(a-c)(a-d))⁻¹(R-bI)(R-cI)(R-dI)`

is now Lean-verified to act as identity on its target eigenspace, vanish on
the other three, commute with `R`, be idempotent under an explicit four-space
spectral-decomposition hypothesis, and participate in a four-projector
resolution of the identity. No eigenbasis or eigenspace orientation is
chosen. The next geometric step is to promote the pointwise projectors to
smooth tensor fields. The universal derivative algebra is already in place:
if `p` is the projector for root `a`, `q` is a complementary projector for
root `b`, and `dR,dp` denote a directional evaluation of `∇R,∇p`, Lean proves

`q dp = (a-b)⁻¹ q(dR)p`,  `dp q = (a-b)⁻¹ p(dR)q`.

It also proves the vanishing target block `p(dp)p=0`. Eigenvalue derivatives
cancel from the off-diagonal formulas. Using the four-projector resolution of
the identity, Lean now assembles these blocks into the complete formula

`dp = Σ_{j≠i}(aᵢ-aⱼ)⁻¹[Pⱼ(dR)Pᵢ + Pᵢ(dR)Pⱼ]`.

The branch-selection layer now proves this both abstractly and for genuine
differentiable one-form fields on an open convex coordinate patch: outside the
locus where the two spectral covector components are separately closed,
existence of one closed relative-sign branch implies that exactly one branch
is closed. Mathlib's Poincare lemma then produces a scalar potential for that
branch, unique up to an additive constant. Instantiating the projector
identities for smooth Ricci-projector fields, differentiating the scalar
amplitudes, and proving that at least one resulting branch is closed remain
the next curvature steps.

The scalar-amplitude part of that task is now verified at the evaluated
algebraic level: Lean gives explicit directional derivatives of `q²`, both
forced scalar diagonals, and both nonzero scalar amplitudes from derivatives
of the characteristic data and complementary roots. Smooth Levi-Civita
instantiation and antisymmetrization remain the Phase-II geometric gap.

### Phase-II exit criterion

A coordinate-free uniqueness theorem, a genuine two-uplift theorem, or a
sharp curvature obstruction explaining why neither branch closes.

## Phase III — reconstruct the Maxwell two-form

For each admissible scalar branch set `S=𝓡-V`. Impose the algebraic Maxwell
Rainich conditions and construct a local two-form `𝓕` up to complexion. Then
use (HC1) to determine the complexion differential and coupling
simultaneously.

This phase must distinguish:

- Maxwell stress reconstruction;
- two-form reconstruction up to duality;
- Bianchi and Maxwell differential closure;
- residual constant duality and orientation freedoms.

Current status: Phase III is complete at its generic local decision interface,
conditional on an upstream admissible scalar branch and its first jet. With
`S=𝓡-V` and `V²=tr(V)V`, Lean proves that the reconstruction equation is
equivalent to `S²=q²I`; matching traces make `S` tracefree. For `q≠0`, the
normalized residual `S/q` is Lean-verified to be an involution, and its
orthogonal projectors `½(I±S/q)` reconstruct the two Maxwell principal
subspaces and resolve the identity without eigenvectors.

At the canonical principal-frame level, Lean now proves that all nonzero
electric/magnetic amplitude pairs with the same stress magnitude form exactly
one duality orbit, with a unique constructively recovered unit parameter.
Differentiating that orbit gives a unique complexion rate. A nondegenerate
two-probe system then reconstructs the complexion rate and signed EMD coupling
simultaneously, with determinant `Δ=z₁y₂-z₂y₁`; scalar-orientation reversal
fixes the complexion rate and reverses the coupling. The recovered candidate
is now checked against explicit local exterior obstructions; see
`docs/PHASE_III_MAXWELL_RECONSTRUCTION.md`.

The canonical amplitudes have also been lifted to an explicit antisymmetric
four-dimensional tensor. Lean directly computes its Lorentzian Maxwell stress,
trace, square, energy sign, Hodge-square, and duality invariance. In particular,
every `q>0` canonical residual `diag(-q,-q,q,q)` has the real seed
`𝓕=√(2q)e⁰∧e¹`. The subsequent results construct the required smooth local
principal frame and its duality orbit, so the square-root step is complete on
the stated generic patch.

Finite-dimensional frame covariance is now complete in Lean: congruence
transport preserves two-form antisymmetry, the Maxwell stress transforms by
similarity, and the square law plus principal-projector relations survive.
The explicit positive-`q` seed therefore works in any supplied Lorentz frame.
The subsequent fixed-probe and overlap results construct those frames locally
and control the required transition algebra.

The frame construction is now explicit on a fixed local probe patch. Lean
proves indefinite Gram--Schmidt for a Lorentzian principal plane, ordinary
Gram--Schmidt for its spacelike complement, preservation of projector-range
membership, and cross-plane metric orthogonality. For any four ambient probes
whose projected Gram pivots satisfy the displayed strict sign conditions, the
formulas produce a full pseudo-orthonormal tetrad. Lean also proves that the
curvature-polynomial Maxwell projectors meet the required idempotence,
annihilation, and metric-self-adjointness hypotheses. The pointwise existence
step is now complete: in dimension four, trace zero of the normalized
involution forces both projector ranges to have rank two, while index-one
signature and a timelike witness in the physical minus range yield
noncollinear probes, a pseudo-orthonormal tetrad basis, and an explicit real
skew two-form whose Maxwell stress is exactly the supplied residual. Lean
already proves that the strict Gram signs persist on a neighborhood once the
associated scalar Gram functions are continuous. It now also proves that one
fixed probe quadruple produces a `C^n` tetrad, frame matrix, and transported
positive-`q` seed throughout that patch. The transpose coframe is proved
Lorentz, `K=G LᵀG` is its smooth two-sided inverse, and the seed stress is the
transported residual. The evaluated connection and exterior-form connector is
now complete in the same local trivialization.

The overlap group law is now formalized as well: duality parameters compose
associatively with explicit identity and inverse, and their action satisfies
the seed-transition cocycle. For a variable transition with rate `τ`, Lean now
proves the exact inhomogeneous law `ω↦ω+τ`. Consequently `ω-A` is invariant
when a local duality connection transforms as `A↦A+τ`; the nondegenerate
two-probe reconstruction transforms in precisely this way while the recovered
EMD coupling remains fixed. This is the local overlap law required by the
obstruction interface; global bundle topology is outside the local Phase-III
exit criterion.

The exterior product rule is no longer schematic. Lean now treats `dc,ds,ω,v`
as one-forms, the seed as two-forms, and their wedges as three-forms. It proves
the exact rotated Bianchi/Maxwell identities and reduces EMD closure to two
explicit seed-channel equations. A notable orbit theorem follows: for
`a≠0` with either `v∧𝓕₀` or `v∧*𝓕₀` active, constant duality rotations
preserving the same equations reduce to overall sign. The full circle remains
only on the verified zero-coupling or inactive-source exceptional loci.

The last local connector is now verified. For `K=L⁻¹` and `Ω=(dL)K`, Lean
differentiates the transported seed as

`d𝓕₀=Lᵀ(Ωᵀ𝓕can+(dq/2q)𝓕can+𝓕canΩ)L`

and proves `ΩG+GΩᵀ=0` from the differentiated Lorentz equation. In a coordinate
trivialization with the local coframe orientation matched to the spacetime
Hodge convention, the four directional derivatives of the seed and Hodge seed
exteriorize to alternating three-forms. Substitution into the EMD equations yields two explicit
curvature-jet obstruction forms with a necessary-and-sufficient simultaneous
vanishing theorem. Hence every generic local scalar branch now returns either
an empty list certified by an obstruction or a Maxwell/coupling orbit; on the
active nonzero-coupling locus that orbit is exactly the two overall signs.

### Phase-III exit criterion

A complete local list of reconstructed `(v,𝓕,a)` orbits determined by the
metric on the generic branch. **Reached conditionally on the Phase-II scalar
branch/first-jet input:** the Phase-III output is the exact pair of local
obstructions and the classified accepted orbit. Null, repeated-root, and
global topological branches remain explicitly excluded.

## Phase IV — constructive five-dimensional uplift

Integrate the closed scalar covector locally, construct `F` from `𝓕`, obtain a
local potential `A`, and assemble the convention-fixed Kaluza metric

`ĝ = exp(c₁φ) g + exp(c₂φ)(dz + c₃A)²`,

with all constants derived from the chosen normalization. Prove directly that
the reconstructed five-dimensional metric is Ricci-flat and prove the
converse reduction statement.

Entry status: the scalar integration and Maxwell unweighting steps are now
Lean-verified on the accepted generic patch. A differentiable closed scalar
branch has `v=dφ`, uniquely up to the expected additive constant and scalar
orientation. The actual exponentials `exp(∓aφ/2)` have the required derivative
jets, and vanishing of the Phase-III obstruction pair implies closure of both
the physical Maxwell field and its weighted dual flux. The test `a²=3` is
orientation invariant and permits a choice with convention-fixed `a=√3`.
Phase IV has now begun with the radial homotopy construction for the closed
physical two-form. Lean proves radial gauge, exposes an honest dominated
differentiation-under-the-integral interface, and proves that closedness plus
the one-variable fundamental theorem makes the integrated derivative candidate
have curvature `F`. It also proves the pointwise gauge-jet classification, the
field-level local theorem `A'-A=dχ` with uniqueness up to a constant, and gauge
invariance of `dz+cA` and the warped Kaluza metric expression. The full
convention-independent block pairing is now constructed and proved symmetric
and nondegenerate under the expected base hypotheses. The IV.1
analytic task is complete: `RadialPotentialSplice.lean` discharges the
domination hypotheses from the concise `C¹` closed package on a star-shaped
patch, identifying the candidate with `dA` uniformly in every evaluation
direction, so `dF=0 → dA=F` and the potential orbit `A+dχ` are Lean
theorems. The IV.2 constants `c₁=-1/√3, c₂=2/√3, c₃=1` are derived in
`docs/UPLIFT_CONVENTION.md` and verified as Lean identities, re-deriving
`a²=3` from the five-dimensional origin. The IV.3 coordinate layer now
proves the block congruence assembly, explicit inverse-metric formulas,
`det ĝ = u⁴·v·det g` with Lorentz-sign preservation, the orthogonal-family
signature lift, and all six Christoffel blocks at a normal-gauge point (the
Maxwell shear carrying exactly the weight `e^{√3φ}`). The second-jet layer
and all Ricci blocks are complete. Lean identifies `R̂₅₅` with the scalar
equation, `R̂_{n5}` with the weighted Maxwell equation, and `R̂_{np}` with
the EMD Einstein residual plus `g_{np}/(2√3)` times the scalar residual. A
named mixed-order symmetry theorem closes the opposite block, and a single
forward-and-converse theorem now proves that the full `5×5` Ricci tensor
vanishes exactly when the normal-frame EMD system holds. The smooth
coordinate-germ wrapper in `KaluzaFieldReduction.lean` now starts from actual
`C²` fields in base normal coordinates and radial gauge. These generate all
required commuting jets by Schwarz's theorem; the uplift extends
circle-invariantly to the local product,
and its point value, first derivative, and full second derivative are proved
equal to the audited metric jets. `CoordinateRicci.lean` now defines the
ansatz-independent coordinate Levi--Civita connection, its differentiated
connection, and Ricci contraction; the Kaluza expression is proved to be its
exact specialization, and the actual local-product derivatives satisfy the
resulting Ricci-flatness/EMD equivalence. The remaining geometric bridge is
now closed for every invertible affine coordinate change. The inverse metric
jet, connection, differentiated connection, and Ricci tensor obey their exact
transformation laws, and inverse-Jacobian contraction proves that the Ricci
pullback is injective. Thus Ricci-flatness is preserved and reflected even by
affine changes mixing base and circle directions. The nonlinear chart law is
complete in `NonlinearCoordinateRicci.lean`: a coordinate two-jet applied
to the metric first jet yields the exact inhomogeneous Christoffel law; a
coordinate three-jet supplies the forced inverse-Jacobian derivative and full
product-rule differentiated connection; and Lean proves that its Ricci
contraction transforms covariantly and that nonlinear pullback preserves and
reflects Ricci-flatness. The proof separately checks the pure-coordinate
third-derivative/quadratic cancellation and the mixed old-connection/Hessian
cancellation. The complete transformed metric second jet is constructed and
its differentiated first-kind cancellation is verified. The metric endpoint
also proves the nonlinear inverse-metric derivative product rule, the affine
first-kind raising contraction, and the inhomogeneous
metric-Hessian/third-derivative contraction. These assemble into the certified
product-rule Christoffel jet and yield unconditional coordinate-Ricci
covariance, preservation and reflection of Ricci-flatness, and the nonlinear
coordinate specialization of the actual Kaluza metric. The required
first-metric-jet symmetry is explicit. `IntrinsicKaluzaLocal.lean` packages
the overlap law as a chart-independent local pseudo-Riemannian theorem for the
actual componentwise `C²`, circle-invariant Kaluza product metric, with
nondegeneracy and displayed Lorentz signature explicit. Ricci-flatness in any
two nonlinear overlap jets agrees, and the intrinsic local predicate is
equivalent to EMD. Global circle topology is outside this local theorem.

### Phase-IV exit criterion

The north-star local if-and-only-if theorem, including uniqueness and all
stated gauge/discrete freedoms.

This exit has two necessary layers. The **uplift-module layer** is complete
for the explicit accepted-data certificate: intrinsic chart-independent
packaging, exhaustive IV.4 orbit classification, and the conditional
forward/converse assembly are proved. The **curvature-entry layer** closes the upstream Phase-II smooth
projector/antisymmetrization and scalar-branch existence-or-obstruction gap.
The first layer may be completed and used by exact-metric tests without
claiming that Phase IV itself has exited. The canonical dependency order is
specified in `REALIGNED_EXECUTION_PLAN.md`.

## Phase V — exact, adversarial, and generative tests

A reproducible validation harness may begin once the conditional intrinsic
uplift module is complete. This is an explicitly labeled validation track,
not a substitute for the curvature-entry layer of the Phase-IV theorem.

Minimum validation set:

1. a rotating dyonic `a=√3` solution passes and reconstructs a Ricci-flat
   uplift;
2. an analogous `a≠√3` EMD solution passes pointwise algebra but returns its
   non-Kaluza value of `a_geom²`;
3. scalar-plus-fluid or other mixed matter is rejected;
4. null, trace-zero, and eigenvalue-collision examples are routed to explicit
   degenerate branches rather than producing false positives.

The generative moonshot is to impose the curvature-only conditions on a new
metric ansatz and obtain a previously unknown exact Kaluza solution.

## Phase VI — observable mathematical physics

Only after the local theorem is secure:

- rebuild the rotating equal-dyon scalar-dipole calculation from cited exact
  solutions;
- determine whether the dipole and translated quadrupole can be extracted
  directly from asymptotic four-dimensional curvature;
- derive waveform modes and approximation order with independent analytic or
  numerical-relativity checks;
- reconnect the laboratory scalar-amplifier branch only if its EFT coupling
  has a defensible geometric origin and phenomenologically allowed scale.

## Kill criteria

The program should change direction if:

- the coupled differential conditions reduce trivially to separately known
  scalar and Maxwell reconstruction with no new orbit or compatibility
  content;
- the coupling cannot be identified even up to sign from any finite-order
  local curvature data, in which case the correct result should be a no-go
  theorem;
- generic smooth spectral projectors fail in the physically relevant
  Lorentzian branch;
- exact Kaluza and non-Kaluza EMD metrics cannot be separated by the proposed
  differential classifier.

A rigorous no-go or nonuniqueness theorem meeting one of these criteria may be
as valuable as the intended reconstruction theorem.
