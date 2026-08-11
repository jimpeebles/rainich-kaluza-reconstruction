import RainichKaluza.RadialGaugePotential

/-!
# Convention-fixed Kaluza uplift constants (Phase IV.2)

`docs/UPLIFT_CONVENTION.md` derives the constants of the uplift ansatz

`ĝ = exp(c₁φ) g + exp(c₂φ) (dz + c₃A)²`

from the five-dimensional Einstein–Hilbert action against the repository's
convention-fixed four-dimensional EMD action: `c₁ = -1/√3`, `c₂ = 2/√3`,
`c₃ = 1`.  This file turns those derived constants into Lean definitions and
verifies, exactly, the three matching conditions of the derivation:

* the Einstein-frame condition `c₂ = -2c₁`;
* the canonical scalar normalization `c₁² = 1/3`
  (equivalently `6(c₁/2)² = 1/2`);
* the Maxwell-exponent condition `(3/2)c₂ = √3`, which in particular
  *re-derives* the Kaluza coupling test `a² = 3` from the five-dimensional
  origin.

It then instantiates the convention-independent warped block pairing of
`RadialGaugePotential.lean` at the derived constants, inheriting symmetry,
nondegeneracy, and Kaluza gauge invariance, and proves the additive-constant
modulus law: shifting `φ` by a constant trades exactly into a homothety of
the base metric and a rescaling of the gauge field and fiber components.
-/

namespace RainichKaluza

/-- Warp exponent `c₁` of the four-dimensional base metric in the Kaluza
uplift, derived in `docs/UPLIFT_CONVENTION.md`. -/
noncomputable def kaluzaBaseWarpExponent : ℝ :=
  -(Real.sqrt 3)⁻¹

/-- Warp exponent `c₂` of the circle fiber in the Kaluza uplift. -/
noncomputable def kaluzaFiberWarpExponent : ℝ :=
  2 * (Real.sqrt 3)⁻¹

/-- Gauge-field normalization `c₃` in the fiber one-form `dz + c₃A`. -/
def kaluzaGaugeNormalization : ℝ := 1

private theorem sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 :=
  Real.sqrt_pos.mpr (by norm_num)

private theorem sqrt_three_ne_zero : Real.sqrt 3 ≠ 0 :=
  ne_of_gt sqrt_three_pos

private theorem mul_self_sqrt_three :
    Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

/-- The base warp exponent is negative: the four-dimensional block shrinks
as the dilaton grows. -/
theorem kaluzaBaseWarpExponent_neg : kaluzaBaseWarpExponent < 0 := by
  unfold kaluzaBaseWarpExponent
  exact neg_lt_zero.mpr (inv_pos.mpr sqrt_three_pos)

/-- The fiber warp exponent is positive: the circle grows with the
dilaton. -/
theorem kaluzaFiberWarpExponent_pos : 0 < kaluzaFiberWarpExponent := by
  unfold kaluzaFiberWarpExponent
  positivity

/-- **Einstein-frame condition (C1).** The reduced Einstein–Hilbert term has
unit coefficient exactly when `c₂ = -2c₁`. -/
theorem kaluzaWarpExponents_einsteinFrame :
    kaluzaFiberWarpExponent = -2 * kaluzaBaseWarpExponent := by
  unfold kaluzaFiberWarpExponent kaluzaBaseWarpExponent
  ring

/-- Equivalent form of (C1): `c₁ + c₂/2 = 0`. -/
theorem kaluzaWarpExponents_conformal_sum :
    kaluzaBaseWarpExponent + kaluzaFiberWarpExponent / 2 = 0 := by
  rw [kaluzaWarpExponents_einsteinFrame]
  ring

/-- **Canonical scalar normalization (C2), square form.** `c₁² = 1/3`. -/
theorem kaluzaBaseWarpExponent_sq :
    kaluzaBaseWarpExponent ^ 2 = 1 / 3 := by
  have h1 : kaluzaBaseWarpExponent ^ 2 = ((Real.sqrt 3)⁻¹) ^ 2 := by
    unfold kaluzaBaseWarpExponent
    ring
  rw [h1, inv_pow, sq, mul_self_sqrt_three]
  norm_num

/-- **Canonical scalar normalization (C2).** The reduced kinetic term
`6(∂(c₁φ/2))²` equals the convention-fixed `½(∂φ)²`. -/
theorem kaluzaWarpExponents_scalarNormalization :
    6 * (kaluzaBaseWarpExponent / 2) ^ 2 = 1 / 2 := by
  have h := kaluzaBaseWarpExponent_sq
  nlinarith [h]

/-- **Maxwell-exponent condition (C3).** The reduced Maxwell factor
`exp(3(c₂/2)φ)` is exactly the convention-fixed `exp(√3 φ)`. -/
theorem kaluzaUpliftMaxwellExponent_eq_sqrt_three :
    3 * (kaluzaFiberWarpExponent / 2) = Real.sqrt 3 := by
  unfold kaluzaFiberWarpExponent
  field_simp
  linarith [mul_self_sqrt_three]

/-- The five-dimensional origin re-derives the Kaluza coupling test: the
Maxwell exponent produced by the derived warp constants satisfies
`a² = 3`. -/
theorem kaluzaUpliftMaxwellExponent_isKaluzaCoupling :
    IsKaluzaCoupling (3 * (kaluzaFiberWarpExponent / 2)) := by
  rw [kaluzaUpliftMaxwellExponent_eq_sqrt_three]
  unfold IsKaluzaCoupling
  rw [sq, mul_self_sqrt_three]

/-- Base warp factor `exp(c₁φ)`. -/
noncomputable def kaluzaBaseWarp (phi : ℝ) : ℝ :=
  Real.exp (kaluzaBaseWarpExponent * phi)

/-- Fiber warp factor `exp(c₂φ)`. -/
noncomputable def kaluzaFiberWarp (phi : ℝ) : ℝ :=
  Real.exp (kaluzaFiberWarpExponent * phi)

/-- Half fiber warp `exp(c₂φ/2)`: the rescaling of the circle coordinate,
gauge field, and fiber components induced by a constant dilaton shift. -/
noncomputable def kaluzaHalfFiberWarp (phi : ℝ) : ℝ :=
  Real.exp (kaluzaFiberWarpExponent * phi / 2)

theorem kaluzaBaseWarp_pos (phi : ℝ) : 0 < kaluzaBaseWarp phi :=
  Real.exp_pos _

theorem kaluzaFiberWarp_pos (phi : ℝ) : 0 < kaluzaFiberWarp phi :=
  Real.exp_pos _

theorem kaluzaBaseWarp_ne_zero (phi : ℝ) : kaluzaBaseWarp phi ≠ 0 :=
  ne_of_gt (kaluzaBaseWarp_pos phi)

theorem kaluzaFiberWarp_ne_zero (phi : ℝ) : kaluzaFiberWarp phi ≠ 0 :=
  ne_of_gt (kaluzaFiberWarp_pos phi)

/-- Constant dilaton shifts multiply the base warp. -/
theorem kaluzaBaseWarp_add (phi k : ℝ) :
    kaluzaBaseWarp (phi + k) = kaluzaBaseWarp phi * kaluzaBaseWarp k := by
  unfold kaluzaBaseWarp
  rw [← Real.exp_add]
  ring_nf

/-- Constant dilaton shifts multiply the fiber warp. -/
theorem kaluzaFiberWarp_add (phi k : ℝ) :
    kaluzaFiberWarp (phi + k) = kaluzaFiberWarp phi * kaluzaFiberWarp k := by
  unfold kaluzaFiberWarp
  rw [← Real.exp_add]
  ring_nf

/-- The half fiber warp squares to the fiber warp. -/
theorem kaluzaHalfFiberWarp_mul_self (k : ℝ) :
    kaluzaHalfFiberWarp k * kaluzaHalfFiberWarp k = kaluzaFiberWarp k := by
  unfold kaluzaHalfFiberWarp kaluzaFiberWarp
  rw [← Real.exp_add]
  ring_nf

section ConventionPairing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The convention-fixed Kaluza block pairing: the convention-independent
warped pairing of `RadialGaugePotential.lean` evaluated at the derived
constants `u = exp(c₁φ)`, `v = exp(c₂φ)`, `c = c₃ = 1`. -/
noncomputable def conventionKaluzaMetricPairing
    (phi : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (X Y : E) (xi eta : ℝ) : ℝ :=
  kaluzaMetricPairing (kaluzaBaseWarp phi) (kaluzaFiberWarp phi)
    kaluzaGaugeNormalization g A X Y xi eta

/-- The convention-fixed pairing is symmetric for a symmetric base
metric. -/
theorem conventionKaluzaMetricPairing_symmetric
    (phi : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (hg : ∀ X Y, g X Y = g Y X) (X Y : E) (xi eta : ℝ) :
    conventionKaluzaMetricPairing phi g A X Y xi eta =
      conventionKaluzaMetricPairing phi g A Y X eta xi :=
  kaluzaMetricPairing_symmetric _ _ _ g A hg X Y xi eta

/-- The convention-fixed pairing is nondegenerate over a nondegenerate base
metric: the exponential warp factors never vanish. -/
theorem conventionKaluzaMetricPairing_nondegenerate
    (phi : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (hg : ∀ X, (∀ Y, g X Y = 0) → X = 0)
    (X : E) (xi : ℝ)
    (hzero : ∀ Y eta,
      conventionKaluzaMetricPairing phi g A X Y xi eta = 0) :
    X = 0 ∧ xi = 0 :=
  kaluzaMetricPairing_nondegenerate _ _ _ g A
    (kaluzaBaseWarp_ne_zero phi) (kaluzaFiberWarp_ne_zero phi) hg X xi hzero

/-- The convention-fixed pairing is invariant under the Kaluza gauge shift
`A ↦ A + dχ`, `ξ ↦ ξ - dχ(X)` with the derived `c₃ = 1`. -/
theorem conventionKaluzaMetricPairing_gauge_invariant
    (phi : ℝ) (g : ContinuousBilinForm E) (A dchi : E →L[ℝ] ℝ)
    (X Y : E) (xi eta : ℝ) :
    conventionKaluzaMetricPairing phi g (gaugeShiftOneForm A dchi) X Y
        (gaugeShiftFiber kaluzaGaugeNormalization dchi X xi)
        (gaugeShiftFiber kaluzaGaugeNormalization dchi Y eta) =
      conventionKaluzaMetricPairing phi g A X Y xi eta :=
  kaluzaMetricPairing_gauge_invariant _ _ _ g A dchi X Y xi eta

/-- **Additive-constant modulus law (IV.2, item 5).** Shifting the dilaton by
a constant `k` produces the same five-dimensional block pairing as keeping
the dilaton and instead applying the homothety `g ↦ exp(c₁k) g` to the base
metric while rescaling the gauge field and both fiber components by the half
fiber warp `exp(c₂k/2)`.  The additive constant of `φ` is therefore a
modulus trading circle circumference against a base homothety. -/
theorem conventionKaluzaMetricPairing_addConstant
    (phi k : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (X Y : E) (xi eta : ℝ) :
    conventionKaluzaMetricPairing (phi + k) g A X Y xi eta =
      conventionKaluzaMetricPairing phi (kaluzaBaseWarp k • g)
        (kaluzaHalfFiberWarp k • A) X Y
        (kaluzaHalfFiberWarp k * xi) (kaluzaHalfFiberWarp k * eta) := by
  have hhalf := kaluzaHalfFiberWarp_mul_self k
  unfold conventionKaluzaMetricPairing kaluzaMetricPairing
    kaluzaFiberOneForm kaluzaGaugeNormalization
  simp only [smul_apply, smul_eq_mul, one_mul]
  rw [kaluzaBaseWarp_add, kaluzaFiberWarp_add, ← hhalf]
  ring

end ConventionPairing

end RainichKaluza
