# Draft theorem statements

These are manuscript-level working statements. “Verified” below means the
displayed finite-dimensional statement has a matching Lean declaration; it
does not transfer unstated geometric assumptions into Lean.

## Proposition A — characteristic factorization consequences

Let `S` be a tracefree endomorphism of a four-dimensional real vector space,
let `q≠0`, and assume `S²=q²I`. For every rank-one endomorphism `V=x⊗f`, the
endomorphism `S+V` has nonzero eigenvectors with eigenvalues `+q` and `-q`.
Both are roots of its actual characteristic polynomial, which therefore has
the factorization

`p(x)=(x²-q²)(x²-e₁x+e₂+q²)`.

Status: verified by the `AlgebraicEntrance.lean` theorem chain ending in
`charpoly_factorization_of_maxwellResidual_add_rankOne_canonical`. No separate
principal-plane multiplicity premise remains; the Maxwell square law itself
is still the named algebraic input.

Let a mixed Ricci endomorphism have characteristic polynomial

`p(λ)=(λ²-q²)(λ²-Rλ-c)`.

Then its spectrum contains the opposite pair `±q`, its characteristic
coefficients satisfy `e₃=-Rq²`, and

`C_KK=e₁²e₄-e₁e₂e₃+e₃²=0`.

If `R≠0`, then `q²=-e₃/R`.

Status: verified as coefficient algebra. The geometric derivation of the
factorization is not part of this proposition's Lean premise.

Conversely, if a monic quartic has nonzero opposite roots `+q` and `-q`, it
necessarily factors as

`(x²-q²)(x²-e₁x+e₂+q²)`.

Status: verified by `monicQuartic_factorization_of_opposite_roots` and
`characteristicData_eq_fromFactorization_of_opposite_roots`.

## Proposition B — the obstruction is not sufficient

There exist real monic quartic coefficients satisfying `C_KK=0` for which the
reconstructed value `q²=-e₃/e₁` is negative. Such data have no real protected
pair `±q`.

Status: verified by the explicit data `(e₁,e₂,e₃,e₄)=(1,0,1,-1)`.

## Proposition B2 — coordinate-free reconstruction equation

Let `A` be an associative real algebra and let `R=S+V` in `A`. If

`S²=q²I` and `V²=tr(V)V`,

then

`RV+VR-tr(V)V=R²-q²I`.

Status: verified by `reconstructionEquation_of_decomposition`. The statement
applies directly to matrix and endomorphism algebras. The selected EMD
normalization gives `R=S+V` and the repository now proves the rank-one scalar
square law basis-independently. The Maxwell square law remains an explicitly
named classical Rainich input.

## Theorem C — generic complementary-block classification

Let `a,b,q²∈ℝ` with `a≠b`, and let `T=a+b`. Consider a mixed two-dimensional
block `V` satisfying the component restriction of

`R V + V R - T V = R²-q²I`

in a Ricci eigenbasis with eigenvalues `a,b`. Then the equation fixes exactly
the diagonal entries

`Vᵃₐ=(a²-q²)/(a-b)`,

`Vᵇ_b=(b²-q²)/(b-a)`,

while its two off-diagonal entries are unconstrained by this equation because
`a+b-T=0`. The fixed diagonals automatically satisfy

`Vᵃₐ+Vᵇ_b=T`.

Status: verified by `solvesComplementaryBlock_iff` and
`reconstructedDiagonal_sum`.

## Corollary D — real symmetric rank-one completion

Under the assumptions of Theorem C, a real symmetric rank-one completion of
the forced diagonal block exists if and only if

`(a²-q²)(b²-q²)≤0`.

Status: verified. This corollary concerns ordinary symmetric rank-one
completion. In a definite-signature complementary block the signature-aware
condition refines it; on mixed-signature blocks the two tests are
incomparable.

## Theorem E — signature-aware scalar-block existence

Let `εₐ²=ε_b²=1` be the metric signs of the two complementary eigendirections.
There exist real covector components `x,y` such that their mixed scalar tensor

`Vⁱⱼ=½vⁱvⱼ`

solves the complementary Sylvester equations if and only if

`εₐ(a²-q²)/(a-b)≥0`,

`ε_b(b²-q²)/(b-a)≥0`.

For the resulting block, lowering the raised index gives a symmetric tensor and
the mixed block has zero determinant. If the first component is nonzero, the
pair `(x,y)` is unique up to the simultaneous sign `(x,y)↦(-x,-y)`.

Status: verified by `exists_scalarComplementaryBlock_iff`,
`scalarMixedBlock_metric_selfAdjoint`, and `scalarMixedBlock_rankOne`.
The discrete uniqueness clause is verified by
`scalarMixedBlock_components_unique_up_to_sign`.

## Theorem F — two-branch classification and pointwise uniqueness obstruction

Under the assumptions of Theorem E, any two scalar-generated solutions of the
complementary reconstruction equations are either the same mixed tensor or are
related by reversing the sign of exactly one scalar component. The simultaneous
global sign does not change the tensor.

If both scalar components are nonzero, the relative-sign partner is a distinct
mixed tensor. Let `J=diag(1,-1)` on the complementary eigenspace. Then

`J²=I`, `J diag(a,b)=diag(a,b) J`,

and the partner is `JVJ`. Thus conjugation by `J` preserves the Ricci data while
exchanging the two reconstructed scalar tensors.

More generally, in any associative real algebra, every involution commuting
with `R` maps solutions of

`RV+VR-tr(V)V=R²-q²I`

to solutions by conjugation.
If `P²=P` is a spectral projector commuting with `R`, the canonical reflection
`J=I-2P` is such an involution; this construction requires no eigenvector
orientation.

Status: verified by `scalarComplementarySolutions_eq_or_flip`,
`exists_distinct_relative_sign_solution`,
`secondSpectralReflection_commutes_with_Ricci`,
`secondSpectralReflection_preserves_Ricci`,
`secondSpectralReflection_conjugates`, and
`reconstructionEquation_conjugation_invariant`. The basis-independent
projector construction is verified by `reflectionOfIdempotent_sq`,
`reflectionOfIdempotent_commutes`, and
`reconstructionEquation_reflectionOfIdempotent`.

On a quadratic invariant block satisfying `(R-aI)(R-bI)=0`, `a≠b`, the
projector can be constructed without eigenvectors as

`Pₐ=(R-bI)/(a-b)`.

Its idempotence, commutation with `R`, correct action on both eigenspaces, and
the associated reflection are verified by the `twoRootProjector_*` and
`twoRootReflection_*` theorem families.

## Theorem G — simultaneous differential closure is exceptional

Write the two reflection-related covector candidates on the complementary
spectral plane as

`v₊=α+β`, `v₋=α-β`.

For any real-linear differential operator `d`,

`d v₊=0` and `d v₋=0` if and only if `dα=0` and `dβ=0`.

Thus, if one candidate is closed, its reflected partner is also closed exactly
when the two spectral components are separately closed. This identifies the
exceptional locus on which first-order differential data fail to select the
pointwise orbit.

Consequently, away from that separately closed locus, if at least one of the
two relative-sign branches is closed, exactly one is closed.

Status: verified by `both_relativeSign_branches_closed_iff` and
`reflected_branch_closed_iff_of_branch_closed`; the exact uniqueness clause is
verified by `relativeSign_closed_branch_unique_of_exists`. The theorem is
abstractly linear, while `CurvatureScalarBranchJet4.both_branches_closed_iff`
now gives its coordinate exterior instantiation for the reconstructed jets.
Neither theorem proves the existence of a closed branch.

## Proposition G2 — full simple-spectrum projector derivative

Let `Pᵢ` be one member of a four-projector resolution of the identity for an
operator `R` with distinct roots `aᵢ`. After evaluating a derivative in one
tangent direction, write `dR` and `dPᵢ` for the resulting endomorphisms. If
the differentiated spectral and idempotence identities hold, then

`dPᵢ = Σ_{j≠i}(aᵢ-aⱼ)⁻¹[Pⱼ(dR)Pᵢ + Pᵢ(dR)Pⱼ]`.

In particular `Pᵢ(dPᵢ)Pᵢ=0`, and derivatives of the eigenvalues do not occur
in the result.

Status: verified algebraically by `spectralProjectorDerivative_fourBlock` and
the `spectralProjectorDerivative_*_block` lemmas. The matrix Lagrange fields
are now proved `C^n` on every labeled simple-spectrum patch by
`contDiffOn_matrixFourRootProjectorField`. The ordinary coordinate derivative
identities are promoted to mixed-tensor covariant identities by the connection
derivation lemmas, and
`leviCivitaSpectralProjectorDerivative_fourBlock_of_coordinateJets` gives the
full Levi--Civita formula. `CurvatureScalarBranchJet4` then assembles the
amplitude derivatives and eigen-one-form jets into explicit `dα,dβ`. Whether
either relative-sign obstruction is forced to vanish by the full metric
hypotheses remains open. The decision itself is now exhaustive:
`plusOnly_iff`, `minusOnly_iff`, `bothClosed_iff`, and `neitherClosed_iff`
identify the unique-plus, unique-minus, two-branch, and no-branch loci, while
`neither_curvatureBranch_closesOn_of_witnesses` supplies the patch-level
finite rejection certificate.

## Proposition G3 — Maxwell residual and principal splitting

Let `V` obey `V²=tr(V)V` and define `S=R-V`. Then

`RV+VR-tr(V)V=R²-q²I`

if and only if

`S²=q²I`.

If the supplied traces of `R` and `V` agree, `S` is tracefree. On a non-null
branch with `q≠0`, `J_M=S/q` satisfies `J_M²=I`, and

`Π₊=½(I+J_M)`, `Π₋=½(I-J_M)`

are orthogonal idempotents whose sum is the identity.

Status: verified by `reconstructionEquation_iff_maxwellResidual_sq`,
`maxwellResidual_trace_zero`, `normalizedMaxwellResidual_sq`, and the
`maxwell*Projector_*` family. This reconstructs the Maxwell stress principal
splitting, not a two-form square root; the Lorentzian energy condition,
duality complexion, and Maxwell differential equations remain open.

## Proposition G4 — canonical duality orbit and coupled differential probes

In a compatible Maxwell principal frame, let `(E,B)` and `(E',B')` be
nonzero amplitude pairs. They have equal canonical stress magnitude

`E²+B²=E'²+B'²`

if and only if a unit pair `(c,s)`, `c²+s²=1`, maps one to the other by

`E'=cE-sB`, `B'=sE+cB`.

The parameter is unique and is constructed by normalized dot and determinant
pairings. If `(c,s)` is differentiated, the circle tangency equation is
equivalent to a unique rate `ω` satisfying `dc=-ωs`, `ds=ωc`.

For two evaluated channels `xᵢ=ωzᵢ+(a/2)yᵢ`, define
`Δ=z₁y₂-z₂y₁`. If `Δ≠0`, then

`ω=(x₁y₂-x₂y₁)/Δ`,

`a=2(z₁x₂-z₂x₁)/Δ`,

and the pair `(ω,a)` is unique. Reversing `(y₁,y₂)` leaves `ω` unchanged and
reverses `a`.

Status: the canonical orbit is verified by
`exists_dualityParameter_iff_same_magnitude` and
`dualityParameter_unique`; the infinitesimal statement by
`duality_tangent_iff_existsUnique_complexionRate`; and the two-probe result by
`complexion_coupling_pair_unique` and its recovery formulas. Lifting the
canonical amplitudes and probes to smooth Lorentzian two-forms remains open.

## Proposition G5 — canonical Lorentzian two-form seed

In an oriented orthonormal frame of signature `(-,+,+,+)`, define

`𝓕=E e⁰∧e¹+B e²∧e³`.

Then `𝓕` is antisymmetric,

`𝓕_{mn}𝓕^{mn}=2(B²-E²)`,

and its mixed Maxwell stress is

`T(𝓕)=diag(-ρ,-ρ,ρ,ρ)`, `ρ=(E²+B²)/2`.

Consequently `tr(T)=0`, `T²=ρ²I`, and the canonical energy density is
nonnegative. The selected canonical Hodge action squares to minus the identity,
and the unit duality orbit is exactly `c𝓕+s(*𝓕)`, with invariant stress. For
every `q>0`, `E=√(2q), B=0` gives a real two-form whose stress is
`diag(-q,-q,q,q)`.

Status: verified by `canonicalMaxwellTwoForm_transpose`,
`canonicalMaxwellTwoForm_invariant`, `maxwellStressMixed_canonical`,
`canonicalMaxwellStress_sq`, `canonicalMaxwellStress_energy_nonneg`,
`canonicalHodgeStar_sq`, `canonicalTwoForm_duality`, and
`exists_canonicalMaxwellTwoForm_of_pos`. Smooth transport from abstract
principal projector bundles to such oriented frames remains open.

## Proposition G6 — Lorentz-frame covariance of the local seed

Let `L` be a supplied Lorentz frame matrix with inverse `K`, satisfying the
explicit left/right inverse and metric identities. Transport a covariant
two-form and mixed stress by

`𝓕↦Lᵀ𝓕L`, `T↦KTL`.

Then antisymmetry is preserved, the matrix Maxwell stress of the transported
two-form equals the transported original stress, and scalar square laws are
preserved. Idempotent principal projectors remain idempotent and complementary
projector pairs continue to resolve the identity. Consequently the explicit
positive-`q` canonical seed transports to a real two-form realizing the
transported canonical residual.

Status: verified by `transportTwoForm_transpose`,
`matrixMaxwellStress_lorentzTransport`, `transportMixed_sq`,
`transportMixed_idempotent`, `transportMixed_projectors_sum`, and
`matrixMaxwellStress_transported_seed`. The theorem assumes the frame
identities; constructing smooth frames from the curvature-derived projector
subbundles and controlling their overlap cocycles remains open.

## Proposition G7 — pointwise adapted principal tetrad and real seed

Let `S` be a tracefree metric-self-adjoint endomorphism on a four-dimensional
index-one Lorentz space with `S²=q²I`, `q>0`. Let `P₋,P₊` be the polynomial
projectors of `J=S/q`, and assume the physical `-1` principal range contains a
timelike vector. Then both projector ranges have dimension two and admit
projected probes from which indefinite/definite Gram--Schmidt produces a
pseudo-orthonormal principal tetrad. The tetrad is linearly independent, hence
defines a basis. In that basis there is an explicit real skew bilinear form
with canonical positive-`q` Maxwell matrix, and its Maxwell stress equals `S`.

Status: verified by `maxwellProjectors_finrank_range_eq_two`,
`exists_maxwellPrincipalTetrad`,
`IsPseudoOrthonormalPrincipalTetrad.linearIndependent`,
`principalTetradBasis`, and
`exists_adaptedPrincipalMaxwellTwoForm_stress_eq`, together with the explicit
Gram--Schmidt lemmas. The strict Gram signs persist locally
for continuous Gram data by `principalGramSigns_eventually`. Smooth fixed-probe
assembly is Proposition G9; orientation and the manifold exterior-form
connector remain.

## Proposition G8 — duality overlap cocycle

Unit duality parameters compose by complex multiplication of their coordinate
pairs. This composition is associative, has `(1,0)` as identity and `(c,-s)`
as inverse, and its action on canonical Maxwell amplitudes respects
composition. Successive local seed changes therefore satisfy the expected
overlap cocycle.

If a seed is changed by a constant unit duality parameter, the reconstructed
infinitesimal complexion rate `ω=c ds-s dc` is unchanged. More generally, for
a variable transition `(u,v)` with transition rate `τ=u dv-v du`, the product
rule gives

`ω' = ω + τ`.

Therefore a local duality connection coefficient satisfying `A'=A+τ` makes
the corrected quantity `ω-A` independent of the chosen seed. Under the
corresponding evaluated-channel shift `xᵢ'=xᵢ+τzᵢ`, the reconstructed raw rate
has the same inhomogeneous transformation and the reconstructed EMD coupling
is invariant. Transition rates add under composition and negate under
inversion, so these derivative data satisfy the expected triple-overlap
cocycle identities.

Status: verified by `dualityCompose_assoc`, the identity/inverse lemmas,
`duality_overlap_cocycle`, `complexionRate_constant_duality_invariant`,
`complexionRate_variable_duality_add`,
`complexionRate_dualityComposeDerivative`,
`complexionRate_dualityInverseDerivative`,
`gaugeCorrectedComplexionRate_invariant`,
`complexionRateFromChannels_gauge_shift`, and
`couplingFromComplexionChannels_gauge_invariant`. The remaining obligation is
to realize these pointwise derivative variables as smooth transition maps and
connection one-forms on the principal-plane bundles.

## Proposition G9 — smooth fixed-probe tetrad and Maxwell seed

In a normed local trivialization, let the metric and the two principal
projectors be `C^n`. Fix one ambient probe quadruple whose projected Gram
pivots remain on the strict Lorentzian/spacelike branches. Then the projected
vectors, Gram--Schmidt tetrad, tetrad matrix, and transported positive-`q`
Maxwell seed are all `C^n` on that patch. The seed is pointwise skew and, under
the supplied Lorentz inverse identities, its Maxwell stress is the transported
canonical residual.

Status: verified by `contDiffOn_smoothProjectedPrincipalTetrad`,
`contDiffOn_smoothPrincipalCoframeMatrix`,
`smoothPrincipalCoframeMatrix_lorentz`, `contDiffOn_smoothLorentzInverse`,
`contDiffOn_smoothTransportedPositiveQSeed`,
`smoothTransportedPositiveQSeed_transpose`, and
`smoothTransportedPositiveQSeed_stress_of_lorentz`. Instantiating the
connection and exterior derivative intrinsically on the tangent bundle
remains open.

## Proposition G10 — exterior complexion reduction and duality collapse

Let `(𝓕₀,𝓖₀)` be a seed/Hodge pair and let `(c,s)` be a unit duality parameter
with one-form derivative `dc=-sω`, `ds=cω`. Then

`d𝓕_θ = ω∧𝓖_θ + c d𝓕₀ + s d𝓖₀`,

`d𝓖_θ = -ω∧𝓕_θ - s d𝓕₀ + c d𝓖₀`.

Consequently the two EMD closure equations are equivalent to two explicit
seed-channel three-form equations. Moreover, if `a≠0` and at least one of
`v∧𝓕₀`, `v∧𝓖₀` is nonzero, a constant unit duality rotation preserving the
same EMD equations has `(c,s)=(±1,0)`. For `a=0`, or when both source channels
vanish, the full constant duality circle remains.

Status: verified by `ExteriorDualityJet.rotatedDF_eq`,
`ExteriorDualityJet.rotatedDG_eq`, `emdExteriorClosure_iff_seedChannels`,
`constantDuality_eq_sign_of_emd`,
`constantDuality_emd_of_zero_coupling`, and
`constantDuality_emd_of_inactive_source`.

## Proposition G11 — transported Maxwell-seed first jet

Let `L` be a Lorentz coframe, `K=L⁻¹`, and let `dL,dq` denote evaluation of
their first derivatives in one tangent direction. For

`𝓕₀=Lᵀ𝓕can(q)L`, `𝓕can(q)=√(2q)e⁰∧e¹`,

set `Ω=(dL)K`. On `q>0`,

`d𝓕₀=Lᵀ(Ωᵀ𝓕can+(dq/2q)𝓕can+𝓕canΩ)L`.

The derivative remains skew. If the Lorentz equation is differentiated, then
`ΩG+GΩᵀ=0`, so the non-amplitude part of the seed derivative is exactly a
Lorentz-connection action. The identical formula holds for the transported
canonical Hodge partner.

Status: verified by
`canonicalPositiveQAmplitudeDerivative_eq_logarithmic`,
`transportedTwoFormDerivative_eq_connectionTransport`,
`lorentzFrameConnection_mem_lorentzLie`,
`transportedPositiveQSeedDerivative_eq_connectionFormula`, and
`transportedPositiveQHodgeSeedDerivative_eq_connectionFormula`.

## Proposition G12 — local exterior obstruction and generic orbit list

In an oriented four-dimensional coordinate trivialization, with the Lorentz
coframe orientation matched to the spacetime Hodge convention, exteriorize
the four directional first derivatives of the transported seed and Hodge seed by cyclic
antisymmetrization. Both outputs are alternating three-forms. Substituting
them into Proposition G10 gives two explicit obstruction forms

`𝓞_F(L,dL,q,dq,ω,v,a)`, `𝓞_G(L,dL,q,dq,ω,v,a)`.

The local rescaled Bianchi and Maxwell equations hold if and only if

`𝓞_F=0`, `𝓞_G=0`.

Thus, for every scalar branch and every candidate `(ω,a)` recovered from
nondegenerate channels, the remaining Phase-III test is a finite exact
vanishing test. On an accepted branch with `a≠0` and active scalar source,
the constant duality orbit is exactly the two overall signs. The full circle
is retained only on the previously classified exceptional loci.

Status: verified by `matrixExteriorDerivative_alternating`,
`matrixOneWedgeTwoTensor_alternating`,
`localPositiveQSeedExteriorDerivative_alternating`,
`localPositiveQHodgeSeedExteriorDerivative_alternating`,
`localPositiveQ_emdClosure_iff_obstructions_zero`, and
`localPositiveQ_constantDuality_eq_sign`. This is the generic local Phase-III
exit theorem conditional on the upstream scalar branch and its first jet; it
does not claim the null, repeated-root, or global topological cases.

## Proposition G13 — generic scalar-branch integration

Let `U` be an open convex coordinate patch and let `α,β` be differentiable
one-form fields representing the two spectral components of the reconstructed
scalar covector. Then the two relative-sign branches `α+β` and `α-β` are both
closed if and only if `α` and `β` are separately closed. Away from that
exceptional locus, if either relative-sign branch is closed, exactly one is
closed.

Every such closed branch has a scalar potential `φ` on `U`, with `dφ=v`.
The potential is unique up to an additive constant. Reversing the scalar
orientation sends `(v,φ)` to `(-v,-φ)`.

Status: verified by `both_relativeSign_scalarOneForms_closed_iff`,
`relativeSign_scalarPotential_exists_unique_branch`,
`exists_scalarPotential_of_closed`,
`scalarPotential_unique_up_to_constant`, and
`neg_isScalarPotentialOn`. The potential theorem specializes Mathlib's
Poincare lemma for one-forms on convex sets. The theorem is conditional on the
existence of a closed relative-sign branch; deriving that existence from the
curvature conditions remains part of the overall sufficiency problem.

## Proposition G14 — closed physical fields and the uplift handoff

Suppose the local Phase-III obstruction pair vanishes for the accepted scalar
branch and reconstructed rescaled Maxwell pair `(𝓕,𝓖)`. Let `v=dφ`. The
weights

`r₋=exp(-aφ/2)`, `r₊=exp(aφ/2)`

have derivatives

`dr₋=-(a/2)r₋v`, `dr₊=(a/2)r₊v`.

Consequently the product rule and the two rescaled EMD equations give

`d(r₋𝓕)=0`, `d(r₊𝓖)=0`.

The first closed two-form is the physical Maxwell field required for the
Kaluza uplift; the second is its closed weighted dual flux. If the recovered
orientation-independent coupling satisfies `a²=3`, one of the two scalar
orientations has the convention-fixed value `a=√3`.

Status: verified by `hasFDerivAt_negativeEMDWeight`,
`hasFDerivAt_positiveEMDWeight`,
`closed_unscaledMaxwell_of_rescaled_bianchi`,
`closed_weightedHodgeFlux_of_rescaled_maxwell`,
`localPositiveQ_obstructions_give_closed_exponentialWeightJets`, and
`kaluzaCoupling_has_positive_orientation`. This is the formal entry point to
Phase IV.

## Proposition G15 — radial homotopy curvature core

For a continuous alternating two-form field `F` on a star-shaped coordinate
patch centered at the origin, define

`A_x(v)=∫₀¹ t F_(tx)(x,v) dt`.

Then `A_0=0` and `A_x(x)=0`. Let `DF` be a supplied first derivative satisfying
alternation in the form slots and the cyclic closedness identity. The
antisymmetrization of the formally differentiated radial integrand is

`d/dt [t² F_(tx)(u,v)]`.

Consequently, whenever the displayed derivative and integrability hypotheses
hold, the antisymmetrization of the integrated derivative candidate equals
`F_x(u,v)`. At a single point every alternating `F` has a potential jet, and
two jets with the same curvature differ by a symmetric jet. At field level,
two differentiable potentials with equal curvature obey `A'-A=dχ` locally,
with `χ` unique up to a constant. Moreover the Kaluza expressions `dz+cA` and
`u g+v(dz+cA)²` are invariant under the paired connection/fiber gauge shift;
the full bilinear block is symmetric and nondegenerate whenever the base
metric is symmetric and nondegenerate and the two warp factors are nonzero.

Status: the radial operator, radial gauge, dominated differentiation
interface, fundamental-calculus identity, pointwise and field-level gauge
orbits, and symmetric nondegenerate Kaluza block assembly with gauge invariance
are verified in `RadialGaugePotential.lean`. The field-level splice is now
also complete: `RadialPotentialSplice.lean` discharges the dominated
differentiation hypotheses from the `C¹` closed package `IsC1ClosedTwoFormOn`
on a star-shaped patch and proves `dA=F` together with the local potential
orbit; see Proposition G16.

## Proposition G16 — local two-form exactness under the `C¹` package

Let `U` be an open patch, star-shaped about the origin of its chart, and let
`F` be an alternating two-form field on `U`, differentiable with continuous
derivative field `DF` satisfying the cyclic closedness identity. Then the
radial gauge potential `A` of Proposition G15 is Frechet differentiable at
every point of `U`, its derivative is the integrated operator-valued
candidate, and

`dA = F`

holds on all of `U`. In particular every such closed `C¹` two-form field has
a differentiable local gauge potential, and on a convex patch the complete
set of potentials is `A + dχ` with `χ` unique up to an additive constant. The
uniform bound feeding the dominated differentiation theorem comes from a
tube-lemma compactness argument on a neighborhood of the compact radial
segment and requires no finite-dimensionality of the model space.

Status: verified by `hasFDerivAt_radialGaugePotential`,
`radialPotentialTotalDerivative_apply`, `radialGaugePotential_gaugeCurvature`,
`radialGaugePotential_isGaugePotentialOn`,
`exists_gaugePotentialOn_of_closed`, and
`exists_gaugePotentialOn_orbit_of_closed` in `RadialPotentialSplice.lean`,
with the package `IsC1ClosedTwoFormOn` and the derived slot alternation
`IsC1ClosedTwoFormOn.deriv_alternating`. The uplift convention constants are
derived in `docs/UPLIFT_CONVENTION.md` and verified in
`UpliftConvention.lean`.

## Proposition G17 — block assembly, inverse, determinant, and Christoffel
blocks

Over the five-dimensional index set `Fin 4 ⊕ Unit`, the Kaluza block metric
is the unipotent congruence transform `ĝ = Pᵀ(u·g ⊕ v)P` with
`P = [[1,0],[c·Aᵀ,1]]`. Consequently: the entry formulas
`ĝ_{μν} = u g_{μν} + vc²A_μA_ν`, `ĝ_{μ5} = vcA_μ`, `ĝ_{55} = v` hold; the
explicit inverse `ĝ^{μν} = u⁻¹g^{μν}`, `ĝ^{μ5} = -u⁻¹c(g⁻¹A)^μ`,
`ĝ^{55} = v⁻¹ + u⁻¹c²A·g⁻¹A` is a two-sided inverse whenever `u, v ≠ 0` and
`g⁻¹` inverts `g`; and `det ĝ = u⁴·v·det g`, so at the derived convention
`det ĝ < 0` iff `det g < 0`. Any `g`-orthogonal family with diagonal values
`eps` lifts, by the compensating fiber shifts `-c·A(e_i)` together with the
pure fiber vector, to a `ĝ`-orthogonal family with diagonal values
`(u·eps, v)`: positive warps preserve index one.

At a normal-gauge point — base normal coordinates `g = diag d`, `∂g = 0`,
radial gauge `A = 0`, both justified by verified freedoms — the raw
Christoffel formula applied to the assembled first jet of the ansatz
evaluates to exactly six blocks: the conformal-warp connection
`(k₁/2)(δ^μ_ν φ₁_ρ + δ^μ_ρ φ₁_ν - g_{νρ}φ₁^μ)`, the Maxwell shear
`(vc/2u)F_ν{}^μ`, the fiber-gradient force `-(k₂v/2u)φ₁^μ`, the symmetrized
gauge jet `(c/2)(∂_νA_ρ + ∂_ρA_ν)`, the dilaton rate `(k₂/2)φ₁_ν`, and zero.
Under the derived convention the Maxwell-shear prefactor is exactly the EMD
weight `e^{√3φ}`.

Status: verified in `KaluzaBlockAssembly.lean`
(`kaluzaBlockMetric_eq_fromBlocks`, `kaluzaBlockMetricInverse_eq_fromBlocks`,
`kaluzaBlockMetric_mul_inverse`, `kaluzaBlockMetricInverse_mul`,
`kaluzaBlockMetric_det`, `conventionKaluzaBlockMetric_det_neg_iff`,
`kaluzaMetricPairing_lift_orthogonal`) and `KaluzaChristoffel.lean` (the
`kaluzaNormalGaugeChristoffel_*` block family,
`kaluzaNormalGaugeChristoffel_symm`,
`kaluzaNormalGaugePointInverse_eq_blockInverse`, `conventionKaluzaWarpRatio`,
and the convention corollaries). The second-derivative jet layer is now
complete; see Proposition G18. The base-fiber and base-base Ricci blocks and
the forward/converse Ricci-flatness theorems are the remaining IV.3
obligations.

## Proposition G18 — the fifth Einstein equation is the scalar equation

Extend the normal-gauge data by the scalar Hessian, the second gauge jet,
and the second base-metric jet. Assemble the second derivative of the block
metric by the chain rule, define the inverse-metric derivative by
`∂ĝ⁻¹ = -ĝ⁻¹(∂ĝ)ĝ⁻¹` (certified against the point metric by the
differentiated inverse identity), differentiate the raw Christoffel formula
by the product rule, and form the raw Ricci contraction with circle
derivatives zero. Then the fiber-fiber Ricci block evaluates in closed form
to

`R̂_55 = -(k₂v/2u)[□φ + (k₁ + k₂/2)(∂φ)²] + (v²c²/4u²)F²`,

with `□φ`, `(∂φ)²`, `F²` the diagonal-frame contractions, and the
Christoffel trace along a base direction is `(2k₁ + k₂/2)φ₁`, the logarithmic
derivative of `√(u⁴v)`. At the derived convention the Einstein-frame
condition eliminates the `(∂φ)²` term and the warp ratio is the EMD weight,
giving

`R̂_55 = -(e^{√3φ}/√3) · (□φ - (√3/4) e^{√3φ} F²)`.

Hence `R̂_55 = 0` exactly when `□φ = (√3/4) e^{√3φ} F²`: the fifth Einstein
equation of the uplift is the convention-fixed `a = √3` EMD scalar equation.

Status: verified in `KaluzaRicci.lean` by
`kaluzaNormalGaugeInverseJet_defining`, the inverse-jet entry lemmas,
`kaluzaNormalGaugeChristoffel_trace_base`,
`kaluzaNormalGaugeChristoffel_trace_fiber`,
`kaluzaNormalGaugeRicci_fiber_traceTerm`,
`kaluzaNormalGaugeRicci_fiber_squareTerm`,
`kaluzaNormalGaugeRicci_fiber_fiber`, and
`conventionKaluzaRicci_fiber_fiber`.

## Target Theorem H — local generalized Rainich–Kaluza reconstruction

On a generic non-null branch satisfying explicit spectral, Lorentzian-sign,
smoothness, and differential conditions, a four-dimensional metric is locally
the reduction of five-dimensional Ricci-flat Kaluza geometry if and only if:

1. its Ricci endomorphism admits the Kaluza factorization and passes the
   signature-aware scalar-block test;
2. the reconstructed centralizer orbit contains a smooth scalar covector whose
   sign/relative-sign data obey the required closure condition;
3. the residual traceless tensor satisfies Maxwell–Rainich algebraic and
   differential conditions;
4. the reconstructed scalar and Maxwell complexion satisfy the EMD scalar
   equation with `a=√3`.

Status: research target, not yet a theorem. It must not appear in an abstract as
proved until full tangent-space spectral assembly and differential sufficiency
are complete.
