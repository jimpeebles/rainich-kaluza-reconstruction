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

Status: verified. This corollary concerns rank one over the reals and is weaker
than Lorentzian scalar-covector factorization.

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

## Target Theorem G — local generalized Rainich–Kaluza reconstruction

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
