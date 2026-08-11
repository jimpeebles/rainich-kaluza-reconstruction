import RainichKaluza.KaluzaChristoffel

/-!
# Kaluza second jets, the Christoffel derivative, and the fiber Ricci block

Second half of the Phase-IV.3 block-curvature calculation, first
installment.  This file extends the normal-gauge evaluated layer of
`KaluzaChristoffel.lean` by the second-derivative data and proves the first
Ricci block identity.

The data at the normal-gauge point gain the symmetric scalar Hessian
`phi2`, the second gauge jet `A2 σ ρ μ = ∂_σ∂_ρ A_μ`, and the second metric
jet `g2 σ ρ μ ν = ∂_σ∂_ρ g_{μν}` (nonzero even in normal coordinates — it
carries the base curvature).  `kaluzaNormalGaugeMetricJet2` assembles the
second derivative of the block metric from the chain rule, with every term
containing an undifferentiated `A` or a first derivative of `g` dropped at
the point.  `kaluzaNormalGaugeInverseJet` is the derivative of the inverse
metric, defined by `∂ĝ⁻¹ = -ĝ⁻¹(∂ĝ)ĝ⁻¹` and certified against the point
metric by the differentiated inverse identity
`kaluzaNormalGaugeInverseJet_defining`.  `kaluzaNormalGaugeChristoffelJet`
is the product-rule derivative of the raw Christoffel formula, and
`kaluzaNormalGaugeRicci` is the raw Ricci contraction

`R̂_{NP} = ∂_M Γ̂^M_{NP} - ∂_N Γ̂^M_{MP} + Γ̂^M_{MQ}Γ̂^Q_{NP} - Γ̂^M_{NQ}Γ̂^Q_{MP}`

with circle derivatives set to zero by invariance.

**Main theorem** (`kaluzaNormalGaugeRicci_fiber_fiber`): the fiber-fiber
Ricci block evaluates in closed form to

`R̂_55 = -(k₂v/2u)[□φ + (k₁ + k₂/2)(∂φ)²] + (v²c²/4u²)F²`,

where `□φ`, `(∂φ)²`, and `F²` are the diagonal-frame contractions.  Under
the derived convention the Einstein-frame condition kills the `(∂φ)²` term
and the warp ratio is the EMD weight, so
(`conventionKaluzaRicci_fiber_fiber`)

`R̂_55 = -(e^{√3φ}/√3)·(□φ - (√3/4) e^{√3φ} F²)`:

the fifth Einstein equation *is* the convention-fixed EMD scalar equation.
The base-fiber and base-base Ricci blocks (Maxwell and Einstein equations)
are completed from this jet layer in `KaluzaRicciMixed.lean` and
`KaluzaRicciBase.lean`.
-/

namespace RainichKaluza

open Matrix

section SecondJet

/-- Point values of the block metric at the normal-gauge point:
`diag (u·d) ⊕ v`. -/
def kaluzaNormalGaugePointMetric (u v : ℝ) (d : Fin 4 → ℝ) :
    (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → ℝ
  | Sum.inl mu, Sum.inl nu => if mu = nu then u * d mu else 0
  | Sum.inr _, Sum.inr _ => v
  | _, _ => 0

/-- The point metric and the point inverse contract to the identity. -/
theorem kaluzaNormalGaugePointMetric_mul_inverse (u v : ℝ)
    (d : Fin 4 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (M N : Fin 4 ⊕ Unit) :
    (∑ A : Fin 4 ⊕ Unit, kaluzaNormalGaugePointMetric u v d M A *
      kaluzaNormalGaugePointInverse u v d A N) =
      if M = N then 1 else 0 := by
  rcases M with mu | _ <;> rcases N with nu | _
  · rw [Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse,
      ite_mul, mul_ite, zero_mul, mul_zero]
    rcases eq_or_ne mu nu with rfl | h
    · have hdm := hd mu
      simp
      field_simp
    · simp [h]
  · rw [Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse]
  · rw [Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse]
  · rw [Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse,
      mul_inv_cancel₀ hv]

/-- Second derivative of the block metric at the normal-gauge point,
assembled by the chain rule with `A = 0` and `∂g = 0` at the point.  The
`g2` slot carries the base curvature data; `phi2` is the scalar Hessian;
`A2` is the symmetric second gauge jet. -/
def kaluzaNormalGaugeMetricJet2 (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ)
    (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (sigma rho : Fin 4) :
    (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → ℝ
  | Sum.inl mu, Sum.inl nu =>
      u * g2 sigma rho mu nu +
        (k₁ * phi2 sigma rho + k₁ ^ 2 * phi1 sigma * phi1 rho) * u *
          Matrix.diagonal d mu nu +
        v * c ^ 2 * (A1 sigma mu * A1 rho nu + A1 rho mu * A1 sigma nu)
  | Sum.inl mu, Sum.inr _ =>
      v * c * (A2 sigma rho mu +
        k₂ * (phi1 sigma * A1 rho mu + phi1 rho * A1 sigma mu))
  | Sum.inr _, Sum.inl nu =>
      v * c * (A2 sigma rho nu +
        k₂ * (phi1 sigma * A1 rho nu + phi1 rho * A1 sigma nu))
  | Sum.inr _, Sum.inr _ =>
      (k₂ * phi2 sigma rho + k₂ ^ 2 * phi1 sigma * phi1 rho) * v

/-- Mixed second derivative `∂_R ∂_X ĝ_{MN}` with a five-dimensional second
slot: circle derivatives vanish by invariance. -/
def kaluzaNormalGaugeDoubleJet (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ)
    (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4) :
    (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → ℝ
  | Sum.inl x, M, N =>
      kaluzaNormalGaugeMetricJet2 u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R x M N
  | Sum.inr _, _, _ => 0

/-- Derivative of the inverse block metric at the normal-gauge point:
`∂ĝ⁻¹ = -ĝ⁻¹(∂ĝ)ĝ⁻¹`, evaluated. -/
noncomputable def kaluzaNormalGaugeInverseJet (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (R : Fin 4) (M N : Fin 4 ⊕ Unit) : ℝ :=
  -∑ A : Fin 4 ⊕ Unit, ∑ B : Fin 4 ⊕ Unit,
    kaluzaNormalGaugePointInverse u v d M A *
      kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 (Sum.inl R) A B *
      kaluzaNormalGaugePointInverse u v d B N

/-- Base-base entry of the inverse jet. -/
theorem kaluzaNormalGaugeInverseJet_base_base (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hd : ∀ i, d i ≠ 0) (R : Fin 4) (m q : Fin 4) :
    kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R
        (Sum.inl m) (Sum.inl q) =
      if m = q then -(k₁ * phi1 R * u⁻¹ * (d m)⁻¹) else 0 := by
  unfold kaluzaNormalGaugeInverseJet
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type, kaluzaNormalGaugePointInverse,
    kaluzaNormalGaugeMetricJet, Matrix.diagonal_apply, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases eq_or_ne m q with rfl | h
  · have hdm := hd m
    simp
    linear_combination
      (k₁ * phi1 R * u⁻¹ * d m * ((d m)⁻¹) ^ 2) * mul_inv_cancel₀ hu +
        (k₁ * phi1 R * u⁻¹ * (d m)⁻¹) * mul_inv_cancel₀ hdm
  · simp [h]

/-- Base-fiber entry of the inverse jet. -/
theorem kaluzaNormalGaugeInverseJet_base_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) (R : Fin 4) (m : Fin 4) :
    kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R
        (Sum.inl m) (Sum.inr ()) =
      -(c * u⁻¹ * (d m)⁻¹ * A1 R m) := by
  unfold kaluzaNormalGaugeInverseJet
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type, kaluzaNormalGaugePointInverse,
    kaluzaNormalGaugeMetricJet, ite_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq]
  linear_combination (c * u⁻¹ * (d m)⁻¹ * A1 R m) * mul_inv_cancel₀ hv

/-- Fiber-base entry of the inverse jet. -/
theorem kaluzaNormalGaugeInverseJet_fiber_base (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) (R : Fin 4) (q : Fin 4) :
    kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R
        (Sum.inr ()) (Sum.inl q) =
      -(c * u⁻¹ * (d q)⁻¹ * A1 R q) := by
  unfold kaluzaNormalGaugeInverseJet
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type, kaluzaNormalGaugePointInverse,
    kaluzaNormalGaugeMetricJet, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq']
  linear_combination (c * u⁻¹ * (d q)⁻¹ * A1 R q) * mul_inv_cancel₀ hv

/-- Fiber-fiber entry of the inverse jet. -/
theorem kaluzaNormalGaugeInverseJet_fiber_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) (R : Fin 4) :
    kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R
        (Sum.inr ()) (Sum.inr ()) =
      -(k₂ * phi1 R * v⁻¹) := by
  unfold kaluzaNormalGaugeInverseJet
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type, kaluzaNormalGaugePointInverse,
    kaluzaNormalGaugeMetricJet, zero_mul, mul_zero,
    ]
  refine Or.inl ?_
  linear_combination (k₂ * phi1 R) * inv_mul_cancel₀ hv

/-- **Differentiated inverse identity.** The inverse jet is certified
against the point metric: `(∂ĝ)ĝ⁻¹ + ĝ(∂ĝ⁻¹) = 0` entrywise — the
evaluated derivative of `ĝ ĝ⁻¹ = 1`. -/
theorem kaluzaNormalGaugeInverseJet_defining (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (R : Fin 4) (M N : Fin 4 ⊕ Unit) :
    (∑ A : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1 (Sum.inl R) M A *
          kaluzaNormalGaugePointInverse u v d A N) +
      (∑ A : Fin 4 ⊕ Unit,
        kaluzaNormalGaugePointMetric u v d M A *
          kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R A N) = 0 := by
  rcases M with m | _ <;> rcases N with q | _
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse,
      kaluzaNormalGaugeMetricJet, Matrix.diagonal_apply, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq',
      kaluzaNormalGaugeInverseJet_base_base u v c k₁ k₂ d phi1 A1 hu hd,
      ]
    rcases eq_or_ne m q with rfl | h
    · have hdm := hd m
      simp
      ring
    · simp [h]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    have hdm := hd m
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse,
      kaluzaNormalGaugeMetricJet, ite_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq, 
      kaluzaNormalGaugeInverseJet_base_fiber u v c k₁ k₂ d phi1 A1 hv]
    field_simp
    ring
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse,
      kaluzaNormalGaugeMetricJet, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq',
      kaluzaNormalGaugeInverseJet_base_base u v c k₁ k₂ d phi1 A1 hu hd,
      kaluzaNormalGaugeInverseJet_fiber_base u v c k₁ k₂ d phi1 A1 hv]
    ring
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [kaluzaNormalGaugePointMetric, kaluzaNormalGaugePointInverse,
      kaluzaNormalGaugeMetricJet, zero_mul, mul_zero,
      
      kaluzaNormalGaugeInverseJet_base_fiber u v c k₁ k₂ d phi1 A1 hv,
      kaluzaNormalGaugeInverseJet_fiber_fiber u v c k₁ k₂ d phi1 A1 hv]
    ring

end SecondJet

section ChristoffelJet

/-- Derivative of the first-kind Christoffel symbols:
`∂_R Γ_{Q,NP} = ½(∂_R∂_N ĝ_{QP} + ∂_R∂_P ĝ_{QN} - ∂_R∂_Q ĝ_{NP})`. -/
noncomputable def kaluzaNormalGaugeChristoffelFirstKindJet
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ)
    (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4) (Q N P : Fin 4 ⊕ Unit) : ℝ :=
  (kaluzaNormalGaugeDoubleJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R N Q P +
    kaluzaNormalGaugeDoubleJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R P Q N -
    kaluzaNormalGaugeDoubleJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R Q N P) / 2

/-- Product-rule derivative of the raw Christoffel formula at the
normal-gauge point. -/
noncomputable def kaluzaNormalGaugeChristoffelJet (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4) (M N P : Fin 4 ⊕ Unit) : ℝ :=
  ∑ Q : Fin 4 ⊕ Unit,
    (kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R M Q *
      kaluzaNormalGaugeChristoffelFirstKind u v c k₁ k₂ d phi1 A1 Q N P +
    kaluzaNormalGaugePointInverse u v d M Q *
      kaluzaNormalGaugeChristoffelFirstKindJet u v c k₁ k₂ d phi1 phi2
        A1 A2 g2 R Q N P)

/-- Raw Ricci contraction at the normal-gauge point, with circle
derivatives zero by invariance:
`R̂_{NP} = ∂_M Γ̂^M_{NP} - ∂_N Γ̂^M_{MP} + Γ̂^M_{MQ}Γ̂^Q_{NP} - Γ̂^M_{NQ}Γ̂^Q_{MP}`. -/
noncomputable def kaluzaNormalGaugeRicci (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N P : Fin 4 ⊕ Unit) : ℝ :=
  (∑ m : Fin 4, kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2
      A1 A2 g2 m (Sum.inl m) N P) -
    Sum.elim
      (fun n => ∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2
          A1 A2 g2 n M M P)
      (fun _ => 0) N +
    (∑ Q : Fin 4 ⊕ Unit,
      (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M Q) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q N P) -
    (∑ M : Fin 4 ⊕ Unit, ∑ Q : Fin 4 ⊕ Unit,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M N Q *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q M P)

end ChristoffelJet

section FiberRicci

/-- Per-direction closed form of the base-row Christoffel derivative in the
fiber-fiber slots. -/
theorem kaluzaNormalGaugeChristoffelJet_base_fiber_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0) (R m : Fin 4) :
    kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R
        (Sum.inl m) (Sum.inr ()) (Sum.inr ()) =
      ((k₁ * k₂ - k₂ ^ 2) * v * u⁻¹ / 2) *
          ((d m)⁻¹ * phi1 R * phi1 m) -
        (k₂ * v * u⁻¹ / 2) * ((d m)⁻¹ * phi2 R m) := by
  unfold kaluzaNormalGaugeChristoffelJet
  rw [Fintype.sum_sum_type]
  simp [kaluzaNormalGaugeInverseJet_base_base u v c k₁ k₂ d phi1 A1 hu hd,
    kaluzaNormalGaugeInverseJet_base_fiber u v c k₁ k₂ d phi1 A1 hv,
    kaluzaNormalGaugePointInverse, kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeChristoffelFirstKindJet, kaluzaNormalGaugeDoubleJet,
    kaluzaNormalGaugeMetricJet, kaluzaNormalGaugeMetricJet2, ite_mul,
    zero_mul, mul_zero, Finset.sum_ite_eq, 
    Finset.sum_add_distrib]
  field_simp
  ring

/-- Trace of the Christoffel blocks along a base direction:
`Γ̂^M_{Mq} = (2k₁ + k₂/2)φ₁_q`, the evaluated `∂_q log √|ĝ|` of
`det ĝ = u⁴·v·det g`. -/
theorem kaluzaNormalGaugeChristoffel_trace_base (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0) (q : Fin 4) :
    (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M
          (Sum.inl q)) =
      (2 * k₁ + k₂ / 2) * phi1 q := by
  rw [Fintype.sum_sum_type]
  have hbase : ∀ mu : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inl mu) (Sum.inl mu) (Sum.inl q) =
      k₁ / 2 * phi1 q := by
    intro mu
    rw [kaluzaNormalGaugeChristoffel_base_base_base u v c k₁ k₂ d phi1 A1
      hu mu mu q (hd mu)]
    have hdm := hd mu
    rcases eq_or_ne mu q with rfl | h
    · simp only [Matrix.diagonal_apply, if_true]
      field_simp
      ring
    · simp [h]
  have hfiber :
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inr ()) (Sum.inr ()) (Sum.inl q) = k₂ / 2 * phi1 q := by
    rw [kaluzaNormalGaugeChristoffel_symm,
      kaluzaNormalGaugeChristoffel_fiber_base_fiber u v c k₁ k₂ d phi1 A1
        hv q]
  have hunit : (∑ b : Unit,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inr b) (Sum.inr b) (Sum.inl q)) = k₂ / 2 * phi1 q := by
    simpa using hfiber
  rw [Finset.sum_congr rfl fun mu _ => hbase mu, hunit]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Trace of the Christoffel blocks along the fiber direction vanishes. -/
theorem kaluzaNormalGaugeChristoffel_trace_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ) :
    (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M
          (Sum.inr ())) = 0 := by
  rw [Fintype.sum_sum_type]
  have hbase : ∀ mu : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inl mu) (Sum.inl mu) (Sum.inr ()) = 0 := by
    intro mu
    rw [kaluzaNormalGaugeChristoffel_base_base_fiber]
    ring
  have hunit : (∑ b : Unit,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
        (Sum.inr b) (Sum.inr b) (Sum.inr ())) = 0 := by
    simpa using
      kaluzaNormalGaugeChristoffel_fiber_fiber_fiber u v c k₁ k₂ d phi1 A1
  rw [Finset.sum_congr rfl fun mu _ => hbase mu, hunit]
  simp

/-- Trace-times-Christoffel contribution to the fiber Ricci block. -/
theorem kaluzaNormalGaugeRicci_fiber_traceTerm (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0) :
    (∑ Q : Fin 4 ⊕ Unit,
        (∑ M : Fin 4 ⊕ Unit,
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M Q) *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
            (Sum.inr ()) (Sum.inr ())) =
      -((2 * k₁ + k₂ / 2) * (k₂ * v * u⁻¹ / 2)) *
        (∑ m : Fin 4, (d m)⁻¹ * phi1 m * phi1 m) := by
  rw [Fintype.sum_sum_type]
  have hbase : ∀ q : Fin 4,
      (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M
          (Sum.inl q)) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl q)
          (Sum.inr ()) (Sum.inr ()) =
      (-((2 * k₁ + k₂ / 2) * (k₂ * v * u⁻¹ / 2))) *
        ((d q)⁻¹ * phi1 q * phi1 q) := by
    intro q
    rw [kaluzaNormalGaugeChristoffel_trace_base u v c k₁ k₂ d phi1 A1
        hu hv hd q,
      kaluzaNormalGaugeChristoffel_base_fiber_fiber u v c k₁ k₂ d phi1 A1 q]
    ring
  have hunit : (∑ b : Unit,
      (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M
          (Sum.inr b)) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
          (Sum.inr ()) (Sum.inr ())) = 0 := by
    simp [kaluzaNormalGaugeChristoffel_trace_fiber u v c k₁ k₂ d phi1 A1]
  rw [Finset.sum_congr rfl fun q _ => hbase q, hunit, add_zero,
    ← Finset.mul_sum]

/-- Quadratic Christoffel contribution to the fiber Ricci block. -/
theorem kaluzaNormalGaugeRicci_fiber_squareTerm (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (A1 : Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) :
    (∑ M : Fin 4 ⊕ Unit, ∑ Q : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M
            (Sum.inr ()) Q *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q M
            (Sum.inr ())) =
      -(v ^ 2 * c ^ 2 * (u⁻¹) ^ 2 / 4) *
          (∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
            ((A1 m q - A1 q m) * (A1 m q - A1 q m))) -
        (k₂ ^ 2 * v * u⁻¹ / 2) *
          (∑ m : Fin 4, (d m)⁻¹ * phi1 m * phi1 m) := by
  rw [Fintype.sum_sum_type]
  have hbaseM : ∀ mu : Fin 4,
      (∑ Q : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl mu)
            (Sum.inr ()) Q *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
            (Sum.inl mu) (Sum.inr ())) =
      (∑ q : Fin 4, (-(v ^ 2 * c ^ 2 * (u⁻¹) ^ 2 / 4)) *
          ((d mu)⁻¹ * (d q)⁻¹ *
            ((A1 mu q - A1 q mu) * (A1 mu q - A1 q mu)))) +
        (-(k₂ ^ 2 * v * u⁻¹ / 4)) * ((d mu)⁻¹ * phi1 mu * phi1 mu) := by
    intro mu
    rw [Fintype.sum_sum_type]
    have hq : ∀ q : Fin 4,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl mu)
            (Sum.inr ()) (Sum.inl q) *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl q)
            (Sum.inl mu) (Sum.inr ()) =
        (-(v ^ 2 * c ^ 2 * (u⁻¹) ^ 2 / 4)) *
          ((d mu)⁻¹ * (d q)⁻¹ *
            ((A1 mu q - A1 q mu) * (A1 mu q - A1 q mu))) := by
      intro q
      rw [kaluzaNormalGaugeChristoffel_symm u v c k₁ k₂ d phi1 A1
          (Sum.inl mu) (Sum.inr ()) (Sum.inl q),
        kaluzaNormalGaugeChristoffel_base_base_fiber u v c k₁ k₂ d phi1 A1
          mu q,
        kaluzaNormalGaugeChristoffel_base_base_fiber u v c k₁ k₂ d phi1 A1
          q mu]
      ring
    have hqUnit : (∑ b : Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl mu)
            (Sum.inr ()) (Sum.inr b) *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
            (Sum.inl mu) (Sum.inr ())) =
        (-(k₂ ^ 2 * v * u⁻¹ / 4)) * ((d mu)⁻¹ * phi1 mu * phi1 mu) := by
      have h2 := kaluzaNormalGaugeChristoffel_base_fiber_fiber u v c k₁ k₂
        d phi1 A1 mu
      have h3 := kaluzaNormalGaugeChristoffel_fiber_base_fiber u v c k₁ k₂
        d phi1 A1 hv mu
      have hstep :
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl mu)
              (Sum.inr ()) (Sum.inr ()) *
            kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
              (Sum.inl mu) (Sum.inr ()) =
          (-(k₂ ^ 2 * v * u⁻¹ / 4)) * ((d mu)⁻¹ * phi1 mu * phi1 mu) := by
        rw [h2, h3]
        ring
      simpa using hstep
    rw [Finset.sum_congr rfl fun q _ => hq q, hqUnit]
  have hfiberM : (∑ b : Unit, ∑ Q : Fin 4 ⊕ Unit,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
          (Sum.inr ()) Q *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
          (Sum.inr b) (Sum.inr ())) =
      ∑ q : Fin 4, (-(k₂ ^ 2 * v * u⁻¹ / 4)) *
        ((d q)⁻¹ * phi1 q * phi1 q) := by
    have hinner : (∑ Q : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
            (Sum.inr ()) Q *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
            (Sum.inr ()) (Sum.inr ())) =
        ∑ q : Fin 4, (-(k₂ ^ 2 * v * u⁻¹ / 4)) *
          ((d q)⁻¹ * phi1 q * phi1 q) := by
      rw [Fintype.sum_sum_type]
      have hq : ∀ q : Fin 4,
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
              (Sum.inr ()) (Sum.inl q) *
            kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl q)
              (Sum.inr ()) (Sum.inr ()) =
          (-(k₂ ^ 2 * v * u⁻¹ / 4)) * ((d q)⁻¹ * phi1 q * phi1 q) := by
        intro q
        rw [kaluzaNormalGaugeChristoffel_symm u v c k₁ k₂ d phi1 A1
            (Sum.inr ()) (Sum.inr ()) (Sum.inl q),
          kaluzaNormalGaugeChristoffel_fiber_base_fiber u v c k₁ k₂ d phi1
            A1 hv q,
          kaluzaNormalGaugeChristoffel_base_fiber_fiber u v c k₁ k₂ d phi1
            A1 q]
        ring
      have hqUnit : (∑ b : Unit,
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
              (Sum.inr ()) (Sum.inr b) *
            kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
              (Sum.inr ()) (Sum.inr ())) = 0 := by
        have h0 := kaluzaNormalGaugeChristoffel_fiber_fiber_fiber u v c
          k₁ k₂ d phi1 A1
        simp [h0]
      rw [Finset.sum_congr rfl fun q _ => hq q, hqUnit, add_zero]
    simpa using hinner
  rw [Finset.sum_congr rfl fun mu _ => hbaseM mu, hfiberM,
    Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

/-- **Fiber-fiber Ricci block.** The fifth diagonal component of the Ricci
tensor of the warped Kaluza metric, in closed form:

`R̂_55 = -(k₂v/2u)[□φ + (k₁ + k₂/2)(∂φ)²] + (v²c²/4u²)F²`. -/
theorem kaluzaNormalGaugeRicci_fiber_fiber (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0) :
    kaluzaNormalGaugeRicci u v c k₁ k₂ d phi1 phi2 A1 A2 g2
        (Sum.inr ()) (Sum.inr ()) =
      -(k₂ * v * u⁻¹ / 2) *
          ((∑ m : Fin 4, (d m)⁻¹ * phi2 m m) +
            (k₁ + k₂ / 2) *
              (∑ m : Fin 4, (d m)⁻¹ * phi1 m * phi1 m)) +
        v ^ 2 * c ^ 2 * (u⁻¹) ^ 2 / 4 *
          (∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
            ((A1 m q - A1 q m) * (A1 m q - A1 q m))) := by
  unfold kaluzaNormalGaugeRicci
  simp only [Sum.elim_inr]
  have h1 : (∑ m : Fin 4,
      kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 m
        (Sum.inl m) (Sum.inr ()) (Sum.inr ())) =
      ((k₁ * k₂ - k₂ ^ 2) * v * u⁻¹ / 2) *
          (∑ m : Fin 4, (d m)⁻¹ * phi1 m * phi1 m) -
        (k₂ * v * u⁻¹ / 2) * (∑ m : Fin 4, (d m)⁻¹ * phi2 m m) := by
    have hterm : ∀ m : Fin 4,
        kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 m
          (Sum.inl m) (Sum.inr ()) (Sum.inr ()) =
        ((k₁ * k₂ - k₂ ^ 2) * v * u⁻¹ / 2) *
            ((d m)⁻¹ * phi1 m * phi1 m) -
          (k₂ * v * u⁻¹ / 2) * ((d m)⁻¹ * phi2 m m) :=
      fun m => kaluzaNormalGaugeChristoffelJet_base_fiber_fiber u v c k₁ k₂
        d phi1 phi2 A1 A2 g2 hu hv hd m m
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h1,
    kaluzaNormalGaugeRicci_fiber_traceTerm u v c k₁ k₂ d phi1 A1 hu hv hd,
    kaluzaNormalGaugeRicci_fiber_squareTerm u v c k₁ k₂ d phi1 A1 hv]
  ring

/-- **The fifth Einstein equation is the EMD scalar equation.** At the
derived convention, the Einstein-frame condition removes the `(∂φ)²` term
and the warp ratio is the EMD weight, so the fiber-fiber Ricci block is
proportional to the convention-fixed scalar field equation:

`R̂_55 = -(e^{√3φ}/√3) · (□φ - (√3/4) e^{√3φ} F²)`.

In particular `R̂_55 = 0` iff `□φ = (√3/4) e^{√3φ} F²`, the `a = √3` EMD
scalar equation of `docs/EMD_CONVENTION.md`. -/
theorem conventionKaluzaRicci_fiber_fiber (phi0 : ℝ) (d : Fin 4 → ℝ)
    (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inr ()) (Sum.inr ()) =
      -(Real.exp (Real.sqrt 3 * phi0) * (Real.sqrt 3)⁻¹) *
        ((∑ m : Fin 4, (d m)⁻¹ * phi2 m m) -
          Real.sqrt 3 / 4 * Real.exp (Real.sqrt 3 * phi0) *
            (∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
              ((A1 m q - A1 q m) * (A1 m q - A1 q m)))) := by
  have hs3 : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hratio := conventionKaluzaWarpRatio phi0
  rw [kaluzaNormalGaugeRicci_fiber_fiber _ _ _ _ _ d phi1 phi2 A1 A2 g2
    (kaluzaBaseWarp_ne_zero phi0) (kaluzaFiberWarp_ne_zero phi0) hd,
    kaluzaWarpExponents_conformal_sum, zero_mul, add_zero]
  have hcoef1 : kaluzaFiberWarpExponent * kaluzaFiberWarp phi0 *
      (kaluzaBaseWarp phi0)⁻¹ / 2 =
      Real.exp (Real.sqrt 3 * phi0) * (Real.sqrt 3)⁻¹ := by
    unfold kaluzaFiberWarpExponent
    linear_combination (Real.sqrt 3)⁻¹ * hratio
  have hcoef2 : kaluzaFiberWarp phi0 ^ 2 * kaluzaGaugeNormalization ^ 2 *
      ((kaluzaBaseWarp phi0)⁻¹) ^ 2 / 4 =
      Real.exp (Real.sqrt 3 * phi0) ^ 2 / 4 := by
    unfold kaluzaGaugeNormalization
    have hsq : (kaluzaFiberWarp phi0 * (kaluzaBaseWarp phi0)⁻¹) ^ 2 =
        Real.exp (Real.sqrt 3 * phi0) ^ 2 := by
      rw [hratio]
    linear_combination hsq / 4
  have hs3' : (Real.sqrt 3)⁻¹ * Real.sqrt 3 = 1 := inv_mul_cancel₀ hs3
  linear_combination
    (-(∑ m : Fin 4, (d m)⁻¹ * phi2 m m)) * hcoef1 +
      (∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
        ((A1 m q - A1 q m) * (A1 m q - A1 q m))) * hcoef2 -
      (Real.exp (Real.sqrt 3 * phi0) ^ 2 / 4 *
        (∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
          ((A1 m q - A1 q m) * (A1 m q - A1 q m)))) * hs3'

end FiberRicci

end RainichKaluza
