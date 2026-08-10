# Phase III — Maxwell two-form reconstruction

## Entry point now proved

For every scalar candidate `V` surviving the pointwise and differential
selection layers, define

`S = 𝓡 - V`.

Under the verified rank-one scalar law `V²=tr(V)V`, Lean now proves the exact
equivalence

`𝓡V + V𝓡 - tr(V)V = 𝓡²-q²I  ↔  S²=q²I`.

If `tr(𝓡)=tr(V)`, the residual is also tracefree. Thus the reconstruction
equation is not merely motivated by a Maxwell decomposition: every accepted
solution automatically reaches the central algebraic Maxwell--Rainich square
identity.

On the non-null branch choose `q≠0` with the stated sign convention and set

`J_M = S/q`.

Lean proves `J_M²=I`. Hence

`Π₊ = ½(I+J_M)`, `Π₋ = ½(I-J_M)`

are orthogonal idempotents resolving the identity. They reconstruct the two
Maxwell principal subspaces without eigenvectors. This is stress/principal-
plane reconstruction, not yet reconstruction of a two-form.

## Remaining local theorem

The Phase-III theorem must add the Lorentzian hypotheses under which a smooth,
self-adjoint, tracefree `S` satisfying `S²=q²I`, `q>0`, is the stress tensor of
a real non-null two-form `𝓕`. The output is a local duality orbit

`𝓕_θ = cos(θ) 𝓕₀ + sin(θ) *𝓕₀`.

The algebraic stress fixes the principal planes and the magnitude but not the
complexion `θ`. The differential equations must then determine `dθ` together
with the EMD coupling:

`d𝓕 = (a/2)v∧𝓕`,

`d(*𝓕) = -(a/2)v∧(*𝓕)`.

## Canonical duality orbit now proved

In a compatible principal frame, encode a candidate seed by its electric and
magnetic amplitudes `(E,B)`. Lean proves constructively that two nonzero pairs
have the same canonical stress magnitude `E²+B²` if and only if a unit
duality parameter `(c,s)`, `c²+s²=1`, maps one to the other. The parameter is
recovered by

`c=(EE'+BB')/(E²+B²)`,

`s=(EB'-BE')/(E²+B²)`,

and is unique. Thus the canonical non-null square-root ambiguity is exactly
one duality circle, including the overall sign; it is not an additional
unclassified branch.

This amplitude model is now realized as an actual antisymmetric tensor in a
four-dimensional orthonormal frame of signature `(-,+,+,+)`:

`𝓕₀ = E e⁰∧e¹ + B e²∧e³`.

Lean evaluates the Lorentzian tensor formula directly and obtains

`𝓕₀² = 2(B²-E²)`,

`T(𝓕₀)=diag(-ρ,-ρ,ρ,ρ)`, `ρ=(E²+B²)/2`.

It verifies trace zero, `T²=ρ²I`, nonnegative canonical energy density, and
Hodge-square `**𝓕₀=-𝓕₀`. For every `q>0`, the explicit seed
`E=√(2q), B=0` has stress `diag(-q,-q,q,q)`. Canonical duality is exactly
`c𝓕₀+s(*𝓕₀)` and leaves this stress invariant.

The construction is now Lean-verified under arbitrary supplied Lorentz frame
transport. If `L` and `K=L⁻¹` obey the explicit Lorentz identities, then

`𝓕 ↦ Lᵀ𝓕L`, `T ↦ KTL`.

Antisymmetry, the scalar square law, idempotence of the principal projectors,
and their resolution of the identity are preserved. In particular the
positive-`q` canonical seed transports to a real local two-form whose stress
is the transported residual. This removes coordinate-frame dependence from
the local algebraic square-root construction.

The principal frame can now be constructed explicitly from local probes.
Given the two curvature-polynomial projectors `P₋,P₊`, project two ambient
vectors into each plane. On the open branch where the first projected plane
has Lorentzian Gram signs and the complementary plane has positive Gram signs,
Lean-verified indefinite/definite Gram--Schmidt produces a full
pseudo-orthonormal tetrad. The normalization stays inside each projector range,
and self-adjoint complementary projectors make every cross-plane inner product
zero. Lean also verifies that the Maxwell projectors satisfy the required
idempotence, annihilation, and self-adjointness conditions.

The pointwise probe-existence gap is now closed. In four dimensions, trace zero
of the normalized involution forces both polynomial projector ranges to have
dimension two. In an index-one Lorentz space, a timelike vector in the physical
`-1` principal range then supplies the Lorentzian plane signature; linear
independence in each rank-two range supplies noncollinear probes. Lean derives
a pseudo-orthonormal principal tetrad, proves it linearly independent and hence
a basis, and equips that basis with an explicit real skew bilinear form having
the canonical positive-`q` Maxwell matrix. Lean further proves that its
Maxwell stress, computed in the adapted Lorentz basis and transported back to
the abstract space, is exactly the original residual `S`. The physical sign assignment is
important: for `diag(-q,-q,q,q)`, the timelike plane is the `-1` eigenspace.

The fixed-probe smooth-family theorem is now complete in a normed local
trivialization. Lean proves compositionally that smooth metric and projector
fields make the projected probes, both Gram--Schmidt frames, the tetrad matrix,
and the transported positive-`q` Maxwell seed `C^n` on every strict sign
patch. Together with local persistence of the signs, one successful pointwise
probe choice therefore supplies a smooth seed on a sufficiently small patch;
no further pointwise choice is made. Lean also proves that the transpose
coframe is Lorentz, that `K=G LᵀG` is its smooth two-sided inverse, and that
the resulting smooth seed has the transported residual as its stress. The
remaining connector is intrinsic tangent-bundle/exterior-derivative
instantiation and identification of its derivatives with curvature forms.

The remaining overlap algebra is also explicit. Lean proves that unit duality
parameters compose associatively, have an identity and inverse, and satisfy
the expected seed-transition cocycle. For a variable transition parameter
with rate `τ=u dv-v du`, the product rule gives the exact transformation

`ω' = ω + τ`.

Thus constant transitions leave `ω` unchanged, while a local connection
coefficient transforming by `A'=A+τ` makes `ω-A` overlap invariant. Lean also
proves that transition rates add under composition and negate under inversion,
the differentiated cocycle identities required on triple overlaps. It further
proves that the two-channel reconstruction is covariant under
`xᵢ'=xᵢ+τzᵢ`: it returns `ω'=ω+τ` and the same coupling `a`. Nonconstant
transition algebra is therefore no longer open; the remaining task is its
smooth bundle/connection realization.

Differentiating `c²+s²=1`, Lean proves that `c dc+s ds=0` is equivalent to
existence of a unique complexion rate `ω`:

`dc=-ωs`, `ds=ωc`, `ω=c ds-s dc`.

Finally, two scalar probe channels `xᵢ=ωzᵢ+(a/2)yᵢ` recover `ω` and `a`
simultaneously whenever `Δ=z₁y₂-z₂y₁≠0`:

`ω=(x₁y₂-x₂y₁)/Δ`,

`a=2(z₁x₂-z₂x₁)/Δ`.

Lean proves joint uniqueness and the orientation law: reversing the scalar
source leaves `ω` fixed and sends `a→-a`. The locus `Δ=0` is therefore the
exact evaluated-channel degeneracy where complexion and coupling cannot be
separated by those probes.

The product-rule substitution has now also been lifted from scalar channels
to exterior-form types. For a seed pair `(𝓕₀,𝓖₀)` and a one-form complexion
`ω`, Lean proves

`d𝓕_θ = ω∧𝓖_θ + c d𝓕₀ + s d𝓖₀`,

`d𝓖_θ = -ω∧𝓕_θ - s d𝓕₀ + c d𝓖₀`,

and gives an exact iff reduction of the two EMD equations to two seed-channel
three-form equations. This reveals a useful orbit result: if `a≠0` and at
least one of `v∧𝓕₀`, `v∧𝓖₀` is nonzero, a constant duality rotation preserving
the same EMD equations must have `(c,s)=(±1,0)`. The full constant circle
survives on the exceptional zero-coupling or inactive-source locus. Thus the
dilaton generically collapses the algebraic duality circle to overall sign.

## Proof work packages

1. **Geometric algebraic Rainich lemma.** Instantiate self-adjointness,
   Lorentz signature, trace zero, the square identity, and the energy sign;
   construct a seed two-form from the two principal planes. **The pointwise
   theorem is Lean-verified in finite dimension: rank two follows from trace,
   the energy-sign witness selects the Lorentzian principal plane, and an
   adapted basis carries an explicit real skew positive-`q` seed whose Maxwell
   stress is exactly the supplied residual. Smooth exterior-form realization
   remains.**
2. **Duality-orbit theorem.** The canonical amplitude-level orbit and its
   uniqueness are complete in Lean. Lift this statement to actual Lorentzian
   two-forms constructed from the principal planes.
3. **Smooth local seed.** State the orientability/trivialization hypotheses
   under which the principal-plane projectors yield a smooth local `𝓕₀`.
   **Finite-dimensional Lorentz-frame covariance, pointwise existence of
   suitable projected probes from rank/signature, explicit Gram--Schmidt, and
   continuous persistence of the strict sign patch are complete in Lean. The
   fixed-probe tetrad, frame matrix, and transported seed are now proved
   `C^n` in a normed local trivialization. The Lorentz coframe, its explicit
   smooth inverse, and the stress equality are complete. Intrinsic bundle
   orientation and the manifold exterior-form connector remain. The
   pointwise overlap cocycle and variable-transition connection law are
   complete.**
4. **Complexion equation.** The unit-circle derivative and nondegenerate
   two-probe solution for `(ω,a)` are complete in Lean. Substitute the actual
   `𝓕_θ` into the rescaled Bianchi/Maxwell equations and identify the geometric
   channel data `x,z,y`. **The abstract exterior-form product rule and exact
   iff reduction to two seed-channel equations are complete; construction of
   those forms from the curvature seed remains.**
5. **Integrability and orbit list.** Give necessary and sufficient closure
   conditions, classify residual constant duality freedom, and combine with
   the scalar relative-sign branches. **The duality overlap group, cocycle,
   variable-rate gauge law, corrected overlap invariant, and gauge invariance
   of the recovered coupling are complete in Lean. The constant-duality orbit
   is now classified: generically only overall sign survives, while the full
   circle remains for zero coupling or inactive scalar-source channels.**

## Exit condition

For every admissible metric branch, produce the complete local list of
`(v,𝓕,a)` orbits or a curvature-derived obstruction showing that the list is
empty. The current repository has completed the residual square identity,
trace cancellation, principal involution/projectors, canonical Lorentzian
two-form seed, pointwise adapted principal basis, and Lorentz-frame transport,
canonical duality orbit,
infinitesimal complexion, and evaluated two-channel `(ω,a)` recovery. It has
now has a smooth fixed-probe tetrad, Lorentz coframe/inverse, and seed in local
trivializations and the
exact exterior product-rule reduction. It has not yet constructed the
intrinsic bundle connection/exterior derivatives or identified the
seed-channel three-forms with curvature-derived exterior data.
