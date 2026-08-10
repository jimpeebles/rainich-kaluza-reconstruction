# Draft theorem statements

These are manuscript-level working statements. “Verified” below means the
displayed finite-dimensional statement has a matching Lean declaration; it
does not transfer unstated geometric assumptions into Lean.

## Proposition A — characteristic factorization consequences

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
abstractly linear; it does not prove the existence of a closed branch or the
manifold exterior-derivative hypotheses.

## Proposition G2 — full simple-spectrum projector derivative

Let `Pᵢ` be one member of a four-projector resolution of the identity for an
operator `R` with distinct roots `aᵢ`. After evaluating a derivative in one
tangent direction, write `dR` and `dPᵢ` for the resulting endomorphisms. If
the differentiated spectral and idempotence identities hold, then

`dPᵢ = Σ_{j≠i}(aᵢ-aⱼ)⁻¹[Pⱼ(dR)Pᵢ + Pᵢ(dR)Pⱼ]`.

In particular `Pᵢ(dPᵢ)Pᵢ=0`, and derivatives of the eigenvalues do not occur
in the result.

Status: verified algebraically by `spectralProjectorDerivative_fourBlock` and
the `spectralProjectorDerivative_*_block` lemmas. The current Lean theorem
takes the differentiated identities as hypotheses. Smooth vector-bundle and
Levi-Civita instantiation remains open.

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
`constantDuality_emd_of_inactive_source`. Curvature construction of the seed
derivative three-forms remains open.

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
