# Uplift convention derivation (Phase IV.2)

This note derives — rather than imports — the constants in the Kaluza uplift
ansatz

`ĝ = exp(c₁φ) g + exp(c₂φ) (dz + c₃A)²`

from the five-dimensional Einstein–Hilbert action and the convention-fixed
four-dimensional action of `docs/EMD_CONVENTION.md`,

`L₄ = √(-g)[R - ¼ e^(√3 φ) F² - ½ (∂φ)²]`,   signature `(-,+,+,+)`.

The result, proved consistent below, is

`c₁ = -1/√3`, `c₂ = +2/√3`, `c₃ = 1`,

so that

`ĝ = exp(-φ/√3) g + exp(2φ/√3) (dz + A)²`.

The Lean definitions and verified identities live in
`RainichKaluza/UpliftConvention.lean`.

## Inputs

Both identities below are standard; they are stated with every sign so the
computation can be audited line by line. Cross-checks: Pope, *Kaluza–Klein
theory* lecture notes, §1.3; the four-dimensional action is equation (1) of
Lü–Mao–Wu, arXiv:1909.00970, quoted in `docs/EMD_CONVENTION.md`.

**(I1) Circle reduction of the Einstein–Hilbert density.** For a
circle-invariant five-dimensional metric in the fiber form

`ĝ = g̃ + e^(2σ) (dz + 𝒜)²`,   `∂_z` Killing, `σ, 𝒜, g̃` functions of `x`,

one has `√(-ĝ) = e^σ √(-g̃)` and

`R̂ = R̃ - 2□̃σ - 2(∂σ)²_g̃ - ¼ e^(2σ) 𝔉_{μν}𝔉^{μν}(g̃)`,   `𝔉 = d𝒜`.

Hence, using `√(-g̃) e^σ (□̃σ + (∂σ)²) = ∂_μ(√(-g̃) e^σ ∂^μσ)`,

`√(-ĝ) R̂ = √(-g̃) e^σ [R̃ - ¼ e^(2σ) 𝔉²] + total derivative`.   (U1)

**(I2) Four-dimensional conformal identity.** For `g̃ = e^(2ω) g` in
dimension `n = 4`,

`√(-g̃) = e^(4ω) √(-g)`,
`R̃ = e^(-2ω) [R - 6 □ω - 6 (∂ω)²]`,
`𝔉²(g̃) = e^(-4ω) 𝔉²(g)`.   (U2)

(The `n`-dimensional coefficients are `2(n-1)` and `(n-1)(n-2)`.)

## Reduction of the ansatz

Write the ansatz as `ω = c₁φ/2`, `σ = c₂φ/2`, `𝒜 = c₃A`, so `𝔉 = c₃F` with
`F = dA`. Substituting (U2) into (U1):

`√(-ĝ) R̂ = √(-g) e^((2ω+σ)) [R - 6□ω - 6(∂ω)²]
            - ¼ c₃² √(-g) e^(3σ) F² + t.d.`   (U3)

The three exponent bookkeepings in the Maxwell term are: `e^(4ω)` from the
volume, `e^σ` from the fiber volume, `e^(2σ)` from (U1), and `e^(-4ω)` from
raising the two index pairs of `F²` with `g̃`; they combine to `e^(3σ)`.

Matching (U3) against `L₄` imposes three conditions.

**(C1) Einstein frame.** The coefficient of `R` must be one for all `φ`:

`2ω + σ = 0  ⇔  c₂ = -2c₁`.

With (C1) the `□ω` term in (U3) has unit prefactor and integrates away, so no
kinetic cross-terms survive.

**(C2) Canonical scalar kinetic term.**

`6 (∂ω)² = 6 (c₁/2)² (∂φ)² ≐ ½ (∂φ)²  ⇔  c₁² = 1/3`.

**(C3) Maxwell term.**

`c₃² e^(3σ) F² ≐ e^(√3 φ) F²  ⇔  c₃² = 1 and (3/2) c₂ = √3`.

## Solution and consistency

(C3) gives `c₂ = 2/√3 > 0`; (C1) then gives `c₁ = -1/√3`; and (C2) holds
automatically, `(-1/√3)² = 1/3`. This last step is a genuine consistency
check, not a free choice: (C1)+(C2) alone force `c₁ = ∓1/√3`, hence a Maxwell
exponent `(3/2)c₂ = ±√3`. The five-dimensional origin therefore *re-derives*
the Kaluza value

`a² = ((3/2) c₂)² = 3`,

matching `IsKaluzaCoupling` and the orientation theorem
`kaluzaCoupling_has_positive_orientation`: the repository's positive
convention `a = +√3` selects the branch with `c₁ < 0 < c₂`. Finally `c₃ = ±1`;
we fix `c₃ = +1`, since the residual overall Maxwell sign is exactly the
surviving constant-duality freedom already classified in Phase III
(`localPositiveQ_constantDuality_eq_sign`).

## The five recorded conventions of IV.2

1. **Sign relating the Kaluza radius scalar to `φ`.** The proper circle
   radius is `ρ(x) = ℓ e^(c₂φ/2) = ℓ e^(φ/√3)` for a reference radius `ℓ`:
   larger `φ` means a larger circle. A dilaton normalized as in Pope's notes
   (Maxwell factor `e^(-√3 φ_P)`) is `φ_P = -φ`.
2. **Normalization of `A`.** `c₃ = 1`: the one-form `A` in the fiber term
   `(dz + A)²` is literally the potential whose `F = dA` enters
   `-¼ e^(√3φ) F²`, with no rescaling; only its global sign is free, and that
   sign is part of the Phase-III duality orbit, not new uplift freedom.
3. **Circle coordinate and signature.** `z` has period `2πℓ`; the fiber term
   enters with a plus sign, so the fiber is spacelike and `ĝ` has Lorentz
   signature `(-,+,+,+,+)` whenever `g` has signature `(-,+,+,+)`. Both warp
   factors are positive exponentials, so the block pairing is nondegenerate
   by `kaluzaMetricPairing_nondegenerate`; the full signature statement is an
   IV.3 obligation.
4. **Gauge transformation of `z`.** Under `A ↦ A + dχ` the compensating
   fifth-coordinate shift is `z ↦ z - χ` (fiber components `ξ ↦ ξ - dχ(X)`,
   i.e. `c = c₃ = 1` in `gaugeShiftFiber`), leaving `dz + A` and the whole
   block metric invariant: `kaluzaFiberOneForm_gauge_invariant`,
   `kaluzaMetricPairing_gauge_invariant`. Global periodicity of `χ` is bundle
   topology and stays outside the local claim.
5. **Additive constant of `φ`.** For `k` constant,
   `ĝ(φ+k, g, A) = ĝ(φ, e^(c₁k) g, e^(c₂k/2) A)` with the circle coordinate
   rescaled by `z ↦ e^(c₂k/2) z` (equivalently: circumference
   `2πℓ ↦ 2πℓ e^(c₂k/2)`). The additive constant of `φ` is therefore a
   modulus trading the circle circumference against a constant homothety of
   the base metric and a rescaling of `A`; only the combination is physical.
   This is the Lean theorem `conventionKaluzaMetricPairing_addConstant`.

## What this note does not do

This convention derivation itself does not compute the five-dimensional
Christoffel or Ricci blocks. Those calculations are now carried out at the
coordinate-jet level in `KaluzaChristoffel.lean`, `KaluzaRicci.lean`,
`KaluzaRicciMixed.lean`, and `KaluzaRicciBase.lean`; the remaining step is
their smooth local-product/normal-coordinate wrapper.
