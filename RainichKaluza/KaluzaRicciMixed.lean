import RainichKaluza.KaluzaRicci

/-!
# The mixed Kaluza Ricci block

This file proves the base--fiber component of the normal-gauge Ricci tensor.
At the convention-fixed warp exponents it is the weighted Maxwell equation.
-/

namespace RainichKaluza

open Matrix

section MixedRicci

/-- Per-direction derivative of the base--fiber Christoffel block.  The final
term is invisible if one differentiates the already gauge-specialized closed
form; retaining it is essential for gauge-covariant cancellation in Ricci. -/
theorem kaluzaNormalGaugeChristoffelJet_base_base_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (R m n : Fin 4) :
    kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R
        (Sum.inl m) (Sum.inl n) (Sum.inr ()) =
      v * c * u⁻¹ * (d m)⁻¹ / 2 *
        (A2 R n m - A2 R m n +
          (k₂ - k₁) * phi1 R * (A1 n m - A1 m n) -
          k₂ * phi1 m * A1 R n) := by
  unfold kaluzaNormalGaugeChristoffelJet
  rw [Fintype.sum_sum_type]
  simp [kaluzaNormalGaugeInverseJet_base_base u v c k₁ k₂ d phi1 A1 hu hd,
    kaluzaNormalGaugeInverseJet_base_fiber u v c k₁ k₂ d phi1 A1 hv,
    kaluzaNormalGaugePointInverse, kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeChristoffelFirstKindJet, kaluzaNormalGaugeDoubleJet,
    kaluzaNormalGaugeMetricJet, kaluzaNormalGaugeMetricJet2, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_add_distrib]
  field_simp
  ring

/-- The fiber-row derivative which cancels the diagonal base-row derivatives
in `∂_R Γ̂^M_{M5}`. -/
theorem kaluzaNormalGaugeChristoffelJet_fiber_fiber_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hv : v ≠ 0) (R : Fin 4) :
    kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R
        (Sum.inr ()) (Sum.inr ()) (Sum.inr ()) =
      k₂ * v * c * u⁻¹ / 2 *
        (∑ q : Fin 4, (d q)⁻¹ * phi1 q * A1 R q) := by
  unfold kaluzaNormalGaugeChristoffelJet
  rw [Fintype.sum_sum_type]
  simp [kaluzaNormalGaugeInverseJet_fiber_base u v c k₁ k₂ d phi1 A1 hv,
    kaluzaNormalGaugeInverseJet_fiber_fiber u v c k₁ k₂ d phi1 A1 hv,
    kaluzaNormalGaugePointInverse, kaluzaNormalGaugeChristoffelFirstKind,
    kaluzaNormalGaugeChristoffelFirstKindJet, kaluzaNormalGaugeDoubleJet,
    kaluzaNormalGaugeMetricJet, kaluzaNormalGaugeMetricJet2, zero_mul,
    Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The differentiated fiber trace vanishes, as required by circle
invariance: `∂_R Γ̂^M_{M5}=0`. -/
theorem kaluzaNormalGaugeChristoffelJet_trace_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (R : Fin 4) :
    (∑ M : Fin 4 ⊕ Unit,
      kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R
        M M (Sum.inr ())) = 0 := by
  rw [Fintype.sum_sum_type]
  have hbase : ∀ m : Fin 4,
      kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R
          (Sum.inl m) (Sum.inl m) (Sum.inr ()) =
        -(k₂ * v * c * u⁻¹ / 2 * ((d m)⁻¹ * phi1 m * A1 R m)) := by
    intro m
    rw [kaluzaNormalGaugeChristoffelJet_base_base_fiber u v c k₁ k₂ d
      phi1 phi2 A1 A2 g2 hu hv hd R m m]
    ring
  have hunit : (∑ b : Unit,
      kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 R
        (Sum.inr b) (Sum.inr b) (Sum.inr ())) =
      k₂ * v * c * u⁻¹ / 2 *
        (∑ q : Fin 4, (d q)⁻¹ * phi1 q * A1 R q) := by
    simpa using kaluzaNormalGaugeChristoffelJet_fiber_fiber_fiber
      u v c k₁ k₂ d phi1 phi2 A1 A2 g2 hv R
  rw [Finset.sum_congr rfl fun m _ => hbase m, hunit,
    Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

/-- Trace-times-Christoffel contribution to the mixed Ricci block. -/
theorem kaluzaNormalGaugeRicci_mixed_traceTerm
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hd : ∀ i, d i ≠ 0) (n : Fin 4) :
    (∑ Q : Fin 4 ⊕ Unit,
      (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M Q) *
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
        (Sum.inl n) (Sum.inr ())) =
      (2 * k₁ + k₂ / 2) * (v * c * u⁻¹ / 2) *
        (∑ q : Fin 4, (d q)⁻¹ * phi1 q * (A1 n q - A1 q n)) := by
  rw [Fintype.sum_sum_type]
  have hbase : ∀ q : Fin 4,
      (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M
          (Sum.inl q)) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl q)
          (Sum.inl n) (Sum.inr ()) =
      (2 * k₁ + k₂ / 2) * (v * c * u⁻¹ / 2) *
        ((d q)⁻¹ * phi1 q * (A1 n q - A1 q n)) := by
    intro q
    rw [kaluzaNormalGaugeChristoffel_trace_base u v c k₁ k₂ d phi1 A1
        hu hv hd q,
      kaluzaNormalGaugeChristoffel_base_base_fiber u v c k₁ k₂ d phi1 A1
        q n]
    ring
  have hunit : (∑ b : Unit,
      (∑ M : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M M
          (Sum.inr b)) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
          (Sum.inl n) (Sum.inr ())) = 0 := by
    simp [kaluzaNormalGaugeChristoffel_trace_fiber u v c k₁ k₂ d phi1 A1]
  rw [Finset.sum_congr rfl fun q _ => hbase q, hunit, add_zero,
    ← Finset.mul_sum]

/-- Base/base part of the quadratic Christoffel contraction in the mixed
Ricci block. -/
theorem kaluzaNormalGaugeRicci_mixed_square_baseBase
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (hu : u ≠ 0) (hd : ∀ i, d i ≠ 0)
    (n : Fin 4) :
    (∑ m : Fin 4, ∑ q : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl m) (Sum.inl n) (Sum.inl q) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl q) (Sum.inl m) (Sum.inr ())) =
      k₁ * (v * c * u⁻¹ / 2) *
        (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) := by
  have hpair : ∀ m q : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl m) (Sum.inl n) (Sum.inl q) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl q) (Sum.inl m) (Sum.inr ()) =
      (k₁ / 2 * ((if m = n then phi1 q else 0) +
          (if m = q then phi1 n else 0) -
          Matrix.diagonal d n q * (d m)⁻¹ * phi1 m)) *
        (v * c * u⁻¹ * (d q)⁻¹ * (A1 m q - A1 q m) / 2) := by
    intro m q
    rw [kaluzaNormalGaugeChristoffel_base_base_base u v c k₁ k₂ d phi1 A1
        hu m n q (hd m),
      kaluzaNormalGaugeChristoffel_base_base_fiber u v c k₁ k₂ d phi1 A1
        q m]
  rw [Finset.sum_congr rfl fun m _ =>
    Finset.sum_congr rfl fun q _ => hpair m q]
  fin_cases n <;>
    simp [Fin.sum_univ_four, Matrix.diagonal_apply] <;>
    field_simp [hd] <;>
    ring

/-- Base-row/fiber-column part of the mixed quadratic contraction. -/
theorem kaluzaNormalGaugeRicci_mixed_square_baseFiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (hv : v ≠ 0) (n : Fin 4) :
    (∑ m : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl m) (Sum.inl n) (Sum.inr ()) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inr ()) (Sum.inl m) (Sum.inr ())) =
      (k₂ / 2) * (v * c * u⁻¹ / 2) *
        (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) := by
  have hterm : ∀ m : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl m) (Sum.inl n) (Sum.inr ()) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inr ()) (Sum.inl m) (Sum.inr ()) =
      (k₂ / 2) * (v * c * u⁻¹ / 2) *
        ((d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) := by
    intro m
    rw [kaluzaNormalGaugeChristoffel_base_base_fiber u v c k₁ k₂ d phi1 A1
        m n,
      kaluzaNormalGaugeChristoffel_fiber_base_fiber u v c k₁ k₂ d phi1 A1
        hv m]
    ring
  rw [Finset.sum_congr rfl fun m _ => hterm m, ← Finset.mul_sum]

/-- Fiber-row/base-column part of the mixed quadratic contraction. -/
theorem kaluzaNormalGaugeRicci_mixed_square_fiberBase
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (hv : v ≠ 0) (n : Fin 4) :
    (∑ q : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inr ()) (Sum.inl n) (Sum.inl q) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl q) (Sum.inr ()) (Sum.inr ())) =
      -(k₂ / 2) * (v * c * u⁻¹ / 2) *
        (∑ q : Fin 4, (d q)⁻¹ * phi1 q * (A1 n q + A1 q n)) := by
  have hterm : ∀ q : Fin 4,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inr ()) (Sum.inl n) (Sum.inl q) *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1
          (Sum.inl q) (Sum.inr ()) (Sum.inr ()) =
      -(k₂ / 2) * (v * c * u⁻¹ / 2) *
        ((d q)⁻¹ * phi1 q * (A1 n q + A1 q n)) := by
    intro q
    rw [kaluzaNormalGaugeChristoffel_fiber_base_base u v c k₁ k₂ d phi1 A1
        hv n q,
      kaluzaNormalGaugeChristoffel_base_fiber_fiber u v c k₁ k₂ d phi1 A1
        q]
    ring
  rw [Finset.sum_congr rfl fun q _ => hterm q, ← Finset.mul_sum]

/-- Complete quadratic Christoffel contraction in the mixed Ricci block. -/
theorem kaluzaNormalGaugeRicci_mixed_squareTerm
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hd : ∀ i, d i ≠ 0) (n : Fin 4) :
    (∑ M : Fin 4 ⊕ Unit, ∑ Q : Fin 4 ⊕ Unit,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M
          (Sum.inl n) Q *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q M
          (Sum.inr ())) =
      (v * c * u⁻¹ / 2) *
        (k₁ * (∑ m : Fin 4,
          (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) -
        k₂ * (∑ m : Fin 4, (d m)⁻¹ * phi1 m * A1 m n)) := by
  rw [Fintype.sum_sum_type]
  have hbaseM : ∀ m : Fin 4,
      (∑ Q : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl m)
            (Sum.inl n) Q *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
            (Sum.inl m) (Sum.inr ())) =
      (∑ q : Fin 4,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl m)
            (Sum.inl n) (Sum.inl q) *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl q)
            (Sum.inl m) (Sum.inr ())) +
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl m)
            (Sum.inl n) (Sum.inr ()) *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
            (Sum.inl m) (Sum.inr ()) := by
    intro m
    rw [Fintype.sum_sum_type]
    simp
  have hfiberM : (∑ b : Unit, ∑ Q : Fin 4 ⊕ Unit,
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
          (Sum.inl n) Q *
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
          (Sum.inr b) (Sum.inr ())) =
      ∑ q : Fin 4,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
            (Sum.inl n) (Sum.inl q) *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inl q)
            (Sum.inr ()) (Sum.inr ()) := by
    rw [show (∑ b : Unit, ∑ Q : Fin 4 ⊕ Unit,
        kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr b)
            (Sum.inl n) Q *
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
            (Sum.inr b) (Sum.inr ())) =
        ∑ Q : Fin 4 ⊕ Unit,
          kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 (Sum.inr ())
              (Sum.inl n) Q *
            kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 Q
              (Sum.inr ()) (Sum.inr ()) by simp,
      Fintype.sum_sum_type]
    simp [kaluzaNormalGaugeChristoffel_fiber_fiber_fiber u v c k₁ k₂ d
      phi1 A1]
  rw [Finset.sum_congr rfl fun m _ => hbaseM m, hfiberM,
    Finset.sum_add_distrib,
    kaluzaNormalGaugeRicci_mixed_square_baseBase u v c k₁ k₂ d phi1 A1
      hu hd n,
    kaluzaNormalGaugeRicci_mixed_square_baseFiber u v c k₁ k₂ d phi1 A1
      hv n,
    kaluzaNormalGaugeRicci_mixed_square_fiberBase u v c k₁ k₂ d phi1 A1
      hv n]
  have hBS :
      (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) -
        (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m + A1 m n)) =
      -2 * (∑ m : Fin 4, (d m)⁻¹ * phi1 m * A1 m n) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  linear_combination (k₂ / 2 * (v * c * u⁻¹ / 2)) * hBS

/-- **Base--fiber Ricci block.** In a normal frame and radial gauge it is the
weighted divergence of the Maxwell curvature:

`R̂_{n5} = (vc/2u) Σ_m d_m⁻¹ [∂_m F_{nm} + (3k₂/2) φ_m F_{nm}]`.

Here `F_{nm}=A1 n m-A1 m n`. -/
theorem kaluzaNormalGaugeRicci_base_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (n : Fin 4) :
    kaluzaNormalGaugeRicci u v c k₁ k₂ d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inr ()) =
      (v * c * u⁻¹ / 2) *
        (∑ m : Fin 4, (d m)⁻¹ *
          ((A2 m n m - A2 m m n) +
            (3 * k₂ / 2) * phi1 m * (A1 n m - A1 m n))) := by
  have hfirst :
      (∑ m : Fin 4,
        kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2 g2 m
          (Sum.inl m) (Sum.inl n) (Sum.inr ())) =
      (v * c * u⁻¹ / 2) *
        ((∑ m : Fin 4, (d m)⁻¹ * (A2 m n m - A2 m m n)) +
          (k₂ - k₁) *
            (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) -
          k₂ * (∑ m : Fin 4, (d m)⁻¹ * phi1 m * A1 m n)) := by
    rw [Finset.sum_congr rfl fun m _ =>
      kaluzaNormalGaugeChristoffelJet_base_base_fiber u v c k₁ k₂ d
        phi1 phi2 A1 A2 g2 hu hv hd m m n]
    have hinside :
        (∑ m : Fin 4, (d m)⁻¹ *
          ((A2 m n m - A2 m m n) +
            (k₂ - k₁) * phi1 m * (A1 n m - A1 m n) -
            k₂ * phi1 m * A1 m n)) =
        (∑ m : Fin 4, (d m)⁻¹ * (A2 m n m - A2 m m n)) +
          (k₂ - k₁) *
            (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) -
          k₂ * (∑ m : Fin 4, (d m)⁻¹ * phi1 m * A1 m n) := by
      calc
        _ = ∑ m : Fin 4,
            ((d m)⁻¹ * (A2 m n m - A2 m m n) +
              (k₂ - k₁) *
                ((d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) -
              k₂ * ((d m)⁻¹ * phi1 m * A1 m n)) := by
                apply Finset.sum_congr rfl
                intro m _
                ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ = (v * c * u⁻¹ / 2) *
          (∑ m : Fin 4, (d m)⁻¹ *
            ((A2 m n m - A2 m m n) +
              (k₂ - k₁) * phi1 m * (A1 n m - A1 m n) -
              k₂ * phi1 m * A1 m n)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            ring
      _ = _ := by rw [hinside]
  have htarget :
      (∑ m : Fin 4, (d m)⁻¹ *
        ((A2 m n m - A2 m m n) +
          (3 * k₂ / 2) * phi1 m * (A1 n m - A1 m n))) =
      (∑ m : Fin 4, (d m)⁻¹ * (A2 m n m - A2 m m n)) +
        (3 * k₂ / 2) *
          (∑ m : Fin 4, (d m)⁻¹ * phi1 m * (A1 n m - A1 m n)) := by
    calc
      _ = ∑ m : Fin 4,
          ((d m)⁻¹ * (A2 m n m - A2 m m n) +
            (3 * k₂ / 2) *
              ((d m)⁻¹ * phi1 m * (A1 n m - A1 m n))) := by
            apply Finset.sum_congr rfl
            intro m _
            ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold kaluzaNormalGaugeRicci
  simp only [Sum.elim_inl]
  rw [hfirst,
    kaluzaNormalGaugeChristoffelJet_trace_fiber u v c k₁ k₂ d phi1 phi2
      A1 A2 g2 hu hv hd n,
    kaluzaNormalGaugeRicci_mixed_traceTerm u v c k₁ k₂ d phi1 A1 hu hv hd n,
    kaluzaNormalGaugeRicci_mixed_squareTerm u v c k₁ k₂ d phi1 A1 hu hv hd n,
    htarget]
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
/-- The opposite mixed Ricci block agrees with the base--fiber block when
`A2` is a genuine second jet (its derivative slots commute).  This closes the
last component needed to pass from the upper block calculation to the full
Ricci tensor. -/
theorem kaluzaNormalGaugeRicci_fiber_base_eq_base_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hA2 : ∀ a b mu, A2 a b mu = A2 b a mu)
    (n : Fin 4) :
    kaluzaNormalGaugeRicci u v c k₁ k₂ d phi1 phi2 A1 A2 g2
        (Sum.inr ()) (Sum.inl n) =
      kaluzaNormalGaugeRicci u v c k₁ k₂ d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inr ()) := by
  fin_cases n <;>
    unfold kaluzaNormalGaugeRicci <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_four,
      kaluzaNormalGaugeChristoffelJet, kaluzaNormalGaugeChristoffelFirstKindJet,
      kaluzaNormalGaugeChristoffelFirstKind,
      kaluzaNormalGaugeInverseJet, kaluzaNormalGaugePointInverse,
      kaluzaNormalGaugeDoubleJet, kaluzaNormalGaugeMetricJet2,
      kaluzaNormalGaugeMetricJet, kaluzaNormalGaugeChristoffel,
      Matrix.diagonal_apply,
      hA2 0 1, hA2 0 2, hA2 0 3, hA2 1 2, hA2 1 3, hA2 2 3] <;>
    field_simp [hu, hv, hd] <;>
    ring

/-- Convention-fixed weighted Maxwell residual in a diagonal normal frame,
using the orientation `F_{nm}=A1 n m-A1 m n`. -/
noncomputable def conventionWeightedMaxwellResidual
    (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ) (n : Fin 4) : ℝ :=
  ∑ m : Fin 4, (d m)⁻¹ *
    ((A2 m n m - A2 m m n) +
      Real.sqrt 3 * phi1 m * (A1 n m - A1 m n))

/-- **The mixed fifth Einstein equation is the weighted Maxwell equation.**
At the derived convention,

`R̂_{n5} = (e^{√3φ}/2) · ∇^m(e^{√3φ}F_{nm})/e^{√3φ}`.

The displayed residual is the normal-coordinate expansion of the weighted
Maxwell divergence. -/
theorem conventionKaluzaRicci_base_fiber
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0) (n : Fin 4) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inr ()) =
      Real.exp (Real.sqrt 3 * phi0) / 2 *
        conventionWeightedMaxwellResidual d phi1 A1 A2 n := by
  rw [kaluzaNormalGaugeRicci_base_fiber _ _ _ _ _ d phi1 phi2 A1 A2 g2
    (kaluzaBaseWarp_ne_zero phi0) (kaluzaFiberWarp_ne_zero phi0) hd n]
  have hratio := conventionKaluzaWarpRatio phi0
  have hexp := kaluzaUpliftMaxwellExponent_eq_sqrt_three
  unfold kaluzaGaugeNormalization conventionWeightedMaxwellResidual
  rw [show kaluzaFiberWarp phi0 * 1 * (kaluzaBaseWarp phi0)⁻¹ / 2 =
      Real.exp (Real.sqrt 3 * phi0) / 2 by linear_combination hratio / 2]
  apply congrArg (fun z : ℝ => Real.exp (Real.sqrt 3 * phi0) / 2 * z)
  apply Finset.sum_congr rfl
  intro m _
  congr 2
  linear_combination hexp * (phi1 m * (A1 n m - A1 m n))

/-- The mixed Ricci component vanishes exactly when the weighted Maxwell
residual vanishes. -/
theorem conventionKaluzaRicci_base_fiber_eq_zero_iff
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0) (n : Fin 4) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inr ()) = 0 ↔
      conventionWeightedMaxwellResidual d phi1 A1 A2 n = 0 := by
  rw [conventionKaluzaRicci_base_fiber phi0 d phi1 phi2 A1 A2 g2 hd n]
  exact mul_eq_zero_iff_left
    (div_ne_zero (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0))

/-- Convention-fixed scalar-equation residual appearing in the fiber Ricci
block. -/
noncomputable def conventionScalarEquationResidual
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (∑ m : Fin 4, (d m)⁻¹ * phi2 m m) -
    Real.sqrt 3 / 4 * Real.exp (Real.sqrt 3 * phi0) *
      (∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
        ((A1 m q - A1 q m) * (A1 m q - A1 q m)))

/-- The fiber Ricci component vanishes exactly when the convention-fixed
scalar residual vanishes.  This turns the earlier prose inference into an
explicit audited `↔` theorem. -/
theorem conventionKaluzaRicci_fiber_fiber_eq_zero_iff
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inr ()) (Sum.inr ()) = 0 ↔
      conventionScalarEquationResidual phi0 d phi2 A1 = 0 := by
  rw [conventionKaluzaRicci_fiber_fiber phi0 d phi1 phi2 A1 A2 g2 hd]
  unfold conventionScalarEquationResidual
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hcoef :
      -(Real.exp (Real.sqrt 3 * phi0) * (Real.sqrt 3)⁻¹) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (Real.exp_ne_zero _) (inv_ne_zero hsqrt))
  exact mul_eq_zero_iff_left hcoef

end MixedRicci

end RainichKaluza
