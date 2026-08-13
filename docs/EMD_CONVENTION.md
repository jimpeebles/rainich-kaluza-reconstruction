# Convention-fixed EMD provenance

This note fixes the normalization used by the algebraic reconstruction layer.
It follows equations (1)--(4) of Lü, Mao, and Wu, *Asymptotic Structure of
Einstein-Maxwell-Dilaton Theory and Its Five Dimensional Origin* (2019),
<https://arxiv.org/abs/1909.00970>.

## Action and Kaluza coupling

Use Lorentz signature `(-,+,+,+)` and

`L = √(-g) [ R - ¼ e^(aφ) F_{μν}F^{μν} - ½ ∂_μφ ∂^μφ ]`,

with `F=dA`. The Kaluza reduction of five-dimensional vacuum gravity is the
case `a=√3` in this normalization.

The rearranged Einstein equation is

`R_{μν} = ½ e^(aφ) (F_{μρ}F_ν{}^ρ - ¼ g_{μν}F²)
          + ½ ∂_μφ ∂_νφ`.                              (E1)

Its trace is

`R = ½ (∂φ)²`.                                         (E2)

## Mixed-endomorphism decomposition

Let `v_μ=∂_μφ` and raise the first index in (E1). Define

`S^μ{}_ν = ½ e^(aφ)(F^{μρ}F_{νρ} - ¼ δ^μ{}_ν F²)`,

`V^μ{}_ν = ½ v^μv_ν`.

Then the mixed Ricci endomorphism satisfies

`𝓡 = S + V`,                                           (E3)

and `tr(S)=0`, `tr(V)=R`.

The scalar part is rank one. In basis-free language it is the endomorphism
`y ↦ ½ v(y) v^♯`. Therefore

`V² = tr(V) V = R V`.                                  (E4)

Theorem `rankOneEndomorphism_sq_eq_trace_smul` proves (E4) for every finite
free real module, independently of coordinates.

## Maxwell square law

For the four-dimensional Maxwell stress endomorphism

`T^μ{}_ν = F^{μρ}F_{νρ} - ¼ δ^μ{}_ν F²`,

the classical algebraic Rainich identity is

`T² = 1/16 [(F_{μν}F^{μν})² + (F_{μν}(*F)^{μν})²] I`.

Consequently the scaled Maxwell part in (E3) satisfies

`S² = q² I`,

`q² = e^(2aφ)/64 [(F²)² + (F·*F)²]`.                  (E5)

On the non-null Maxwell branch `q²>0`. The project treats (E5) as an
established four-dimensional Rainich input; a future tensor-library layer may
formalize its exterior-algebra derivation.

## Reconstruction equation

Equations (E3)--(E5) imply, without assuming that `S` and `V` commute,

`𝓡V + V𝓡 - R V = 𝓡² - q²I`.                           (E6)

This noncommutative implication is Lean-verified by
`reconstructionEquation_of_decomposition`.

## Rescaled differential equations and the coupling

The Bianchi and Maxwell equations in this convention are

`dF=0`, `d(exp(aφ) *F)=0`.                              (E7)

Define the scalar covector and exponentially rescaled Maxwell two-form

`v=dφ`, `𝓕=exp(aφ/2)F`.                                (E8)

For direct comparison with the Ricci residual `S`, it is useful to introduce

`H=𝓕/√2`.                                               (E8b)

The ordinary Maxwell stress of `H` is exactly `S`. Equivalently, the ordinary
Maxwell stress of `𝓕` is `2S`. The constant factor does not change either
exterior equation or any coupling ratio.

The product and chain rules give

`d𝓕=(a/2)v∧𝓕`.                                         (E9)

Also `exp(aφ)*F=exp(aφ/2)*𝓕`, so the second equation in (E7) gives

`d(*𝓕)=-(a/2)v∧(*𝓕)`.                                  (E10)

Equations (E9)--(E10) are important because the pointwise Einstein equation
absorbs `exp(aφ)` into `𝓕` and therefore cannot identify `a`, whereas these
differential equations contain it explicitly. Once the global sign of the
reconstructed `v` is fixed, either nonzero wedge channel determines `a`
uniquely. Reversing `v` reverses `a`, so the convention-independent metric
target is `a²`; Kaluza reduction is selected by `a²=3`.

If the Lorentzian pairing of the three-form `Y=v∧𝓕` with itself is nonzero,
(E9) yields the coordinate-free formulas

`a = 2⟪d𝓕,Y⟫/⟪Y,Y⟫`,

`a² = 4⟪d𝓕,d𝓕⟫/⟪Y,Y⟫`.                                (E11)

The dual equation gives the same value of `a²`. `CouplingInvariant.lean`
verifies (E11), its orientation behavior, and primal/dual agreement for an
arbitrary real bilinear pairing, so an indefinite Lorentzian pairing is
allowed. The non-null denominator is an explicit branch restriction.

`DifferentialCoupling.lean` formalizes the abstract compatibility equations,
coupling uniqueness on a nonzero channel, probe formulas for `a` and `a²`, and
the `(v,a)↦(-v,-a)` orientation symmetry. `ExteriorComplexion.lean`,
`LocalExteriorSeed.lean`, `PhaseIVReadiness.lean`, and
`RadialGaugePotential.lean` now formalize the local
exterior product rules, explicit seed-channel obstruction forms, scalar
integration, exponential unweighting, and closure of the physical Maxwell
field for every accepted generic local branch, followed by the radial
potential candidate and its convention-independent Kaluza gauge algebra.
`RadialPotentialSplice.lean` completes the local two-form Poincare theorem
`dF=0 → dA=F` under a `C¹` closed regularity package, and
`UpliftConvention.lean` fixes the uplift constants derived in
`docs/UPLIFT_CONVENTION.md`.

### Metric-seed correction (2026-08-12)

Formula (E11) uses the physical exponentially rescaled form `𝓕`. Curvature
determines `S` and therefore directly constructs a canonical principal-plane
seed `(F₀,*F₀)` for `H=𝓕/√2`, not the physical representative `H` itself.
If

`H=cos(θ)F₀+sin(θ)*F₀`,

the complete first seed-derivative channels determine only

`A=a cos(2θ)` and `η=dθ+(a sin(2θ)/2)Jv`.

They have an exact shear kernel and cannot recover `a²` at metric order three.
For constant `a`, one derivative later

`dA+2Bη-B²Jv=0`, with `B=a sin(2θ)`,

generically recovers `B` and hence `a²=A²+B²`. The proof and precise branch
condition are in
[`../papers/coupling-detector/TECHNICAL_SUPPLEMENT.md`](../papers/coupling-detector/TECHNICAL_SUPPLEMENT.md)
and `GeometricCouplingDetector.lean`. Older evaluated two-probe theorems remain
correct abstract linear algebra; their unknowns must not be interpreted as
physical `(dθ,a)` before this seed-to-physical distinction is resolved.

The scalar equation in the curvature-seed normalization is

`□φ=(a/2)H²=-2qA`,

because the canonical seed has amplitude `E=√(2q)` and `H²=-4q cos(2θ)`.
Thus its independent cosine-channel check is `A=-□φ/(2q)`.

## Scope boundary

This note fixes the field-equation provenance and derives the rescaled
differential identities. The repository now gives an exact conditional local
decision for those identities. For every realized curvature patch it also
classifies exactly which of the two scalar candidates admit local potentials,
including the no-potential case. It now constructs the Frechet-jet realization
automatically from constituent amplitude/eigen-one-form coordinate jets. The
two normalized fixed-probe eigen-one-form identities are proved by explicit
matrix-probe, normalization, and metric-dual differentiation; exact rational
and square-root differentiation also proves both scalar-amplitude identities.
The concrete generic constituent seam is complete. Degenerate branches are
not covered. The uniform analytic
splice identifying the
radial derivative candidate with `dA`, the uplift constants, and the
conditional intrinsic forward/converse five-dimensional uplift are complete;
the remaining sufficiency obligation is their curvature-only composition.
