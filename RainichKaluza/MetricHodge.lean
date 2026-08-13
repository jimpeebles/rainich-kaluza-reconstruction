import RainichKaluza.LocalExteriorSeed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Coordinate metric Hodge operator in four dimensions

This file makes the Hodge channel used by the curvature detector an explicit
formula in the metric.  The orientation is the standard coordinate
orientation and the Lorentz signature convention is `(-,+,+,+)`.
-/

namespace RainichKaluza

open scoped Matrix

/-- Four-dimensional alternating symbol with `epsilon(0,1,2,3)=+1`. -/
def leviCivitaSymbol4 (i j k l : Fin 4) : ℝ :=
  if
      (i = 0 ∧ j = 1 ∧ k = 2 ∧ l = 3) ∨
      (i = 0 ∧ j = 2 ∧ k = 3 ∧ l = 1) ∨
      (i = 0 ∧ j = 3 ∧ k = 1 ∧ l = 2) ∨
      (i = 1 ∧ j = 0 ∧ k = 3 ∧ l = 2) ∨
      (i = 1 ∧ j = 2 ∧ k = 0 ∧ l = 3) ∨
      (i = 1 ∧ j = 3 ∧ k = 2 ∧ l = 0) ∨
      (i = 2 ∧ j = 0 ∧ k = 1 ∧ l = 3) ∨
      (i = 2 ∧ j = 1 ∧ k = 3 ∧ l = 0) ∨
      (i = 2 ∧ j = 3 ∧ k = 0 ∧ l = 1) ∨
      (i = 3 ∧ j = 0 ∧ k = 2 ∧ l = 1) ∨
      (i = 3 ∧ j = 1 ∧ k = 0 ∧ l = 2) ∨
      (i = 3 ∧ j = 2 ∧ k = 1 ∧ l = 0)
  then 1
  else if
      (i = 0 ∧ j = 1 ∧ k = 3 ∧ l = 2) ∨
      (i = 0 ∧ j = 2 ∧ k = 1 ∧ l = 3) ∨
      (i = 0 ∧ j = 3 ∧ k = 2 ∧ l = 1) ∨
      (i = 1 ∧ j = 0 ∧ k = 2 ∧ l = 3) ∨
      (i = 1 ∧ j = 2 ∧ k = 3 ∧ l = 0) ∨
      (i = 1 ∧ j = 3 ∧ k = 0 ∧ l = 2) ∨
      (i = 2 ∧ j = 0 ∧ k = 3 ∧ l = 1) ∨
      (i = 2 ∧ j = 1 ∧ k = 0 ∧ l = 3) ∨
      (i = 2 ∧ j = 3 ∧ k = 1 ∧ l = 0) ∨
      (i = 3 ∧ j = 0 ∧ k = 1 ∧ l = 2) ∨
      (i = 3 ∧ j = 1 ∧ k = 2 ∧ l = 0) ∨
      (i = 3 ∧ j = 2 ∧ k = 0 ∧ l = 1)
    then -1
    else 0

/-- Matrix whose four columns are the coordinate basis vectors selected by
`i,j,k,l`.  Its determinant is the alternating symbol. -/
def coordinateBasisColumnTuple4 (i j k l : Fin 4) : Matrix4 :=
  fun r c => if r = ![i, j, k, l] c then 1 else 0

private theorem matrix4_det_expansion (A : Matrix4) :
    Matrix.det A =
      A 0 0 *
          (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 -
            A 1 2 * A 2 1 * A 3 3 + A 1 2 * A 2 3 * A 3 1 +
            A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
        A 0 1 *
          (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 -
            A 1 2 * A 2 0 * A 3 3 + A 1 2 * A 2 3 * A 3 0 +
            A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
        A 0 2 *
          (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 -
            A 1 1 * A 2 0 * A 3 3 + A 1 1 * A 2 3 * A 3 0 +
            A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
        A 0 3 *
          (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 -
            A 1 1 * A 2 0 * A 3 2 + A 1 1 * A 2 2 * A 3 0 +
            A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply]
  have hsucc2 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
  have hcast2 : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := by decide
  have hsa12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have hsa22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  rw [hsucc2, hcast2, hsa12, hsa22]
  ring

set_option maxHeartbeats 2000000 in
/-- The explicit alternating symbol is the determinant of the corresponding
coordinate-basis column tuple.  This is the finite bridge from the component
formula below to determinant covariance. -/
theorem coordinateBasisColumnTuple4_det (i j k l : Fin 4) :
    Matrix.det (coordinateBasisColumnTuple4 i j k l) =
      leviCivitaSymbol4 i j k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [coordinateBasisColumnTuple4, leviCivitaSymbol4,
      matrix4_det_expansion]

/-- Component expansion of a four-by-four determinant using the repository's
explicit alternating symbol. -/
theorem matrix4_det_eq_leviCivita_sum (A : Matrix4) :
    Matrix.det A =
      ∑ i, ∑ j, ∑ k, ∑ l,
        leviCivitaSymbol4 i j k l *
          A i 0 * A j 1 * A k 2 * A l 3 := by
  rw [matrix4_det_expansion]
  simp [leviCivitaSymbol4, Fin.sum_univ_succ]
  ring

/-- A four-dimensional alternating-symbol contraction transforms by the
determinant.  This is the component covariance identity needed by metric
Hodge naturality. -/
theorem leviCivitaSymbol4_covariant
    (L : Matrix4) (i j k l : Fin 4) :
    (∑ a, ∑ b, ∑ c, ∑ d,
        leviCivitaSymbol4 a b c d *
          L a i * L b j * L c k * L d l) =
      Matrix.det L * leviCivitaSymbol4 i j k l := by
  let P := coordinateBasisColumnTuple4 i j k l
  have hLP : L * P = fun r c => ![L r i, L r j, L r k, L r l] c := by
    ext r c
    fin_cases c <;>
      simp [P, coordinateBasisColumnTuple4, Matrix.mul_apply]
  calc
    (∑ a, ∑ b, ∑ c, ∑ d,
        leviCivitaSymbol4 a b c d *
          L a i * L b j * L c k * L d l) = Matrix.det (L * P) := by
      rw [matrix4_det_eq_leviCivita_sum, hLP]
      simp
    _ = Matrix.det L * Matrix.det P := Matrix.det_mul L P
    _ = Matrix.det L * leviCivitaSymbol4 i j k l := by
      rw [coordinateBasisColumnTuple4_det]

private theorem fin4_sum_rotate3
    {A : Type*} [AddCommMonoid A]
    (f : Fin 4 → Fin 4 → Fin 4 → A) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    (∑ i, ∑ j, ∑ k, f i j k) =
        ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, f i j k := by
      rw [Finset.sum_comm]

set_option maxHeartbeats 2000000 in
/-- Two-index cofactor form of alternating-symbol covariance.  Contracting
two slots of the four-index determinant law with a supplied inverse leaves
the complementary two-by-two minors. -/
theorem leviCivitaSymbol4_inverse_contraction
    (L K : Matrix4) (hLK : L * K = 1)
    (i j m n : Fin 4) :
    Matrix.det L *
        (∑ k, ∑ l,
          leviCivitaSymbol4 i j k l * K k m * K l n) =
      ∑ a, ∑ b,
        leviCivitaSymbol4 a b m n * L a i * L b j := by
  have hentry (c r : Fin 4) :
      (∑ k, L c k * K k r) = if c = r then 1 else 0 := by
    have h := congrArg (fun M : Matrix4 => M c r) hLK
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  calc
    Matrix.det L *
        (∑ k, ∑ l,
          leviCivitaSymbol4 i j k l * K k m * K l n) =
        ∑ k, ∑ l,
          (Matrix.det L * leviCivitaSymbol4 i j k l) *
            K k m * K l n := by
      simp only [Finset.mul_sum]
      ring_nf
    _ = ∑ k, ∑ l,
          (∑ a, ∑ b, ∑ c, ∑ d,
            leviCivitaSymbol4 a b c d *
              L a i * L b j * L c k * L d l) *
            K k m * K l n := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [leviCivitaSymbol4_covariant]
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
          leviCivitaSymbol4 a b c d * L a i * L b j *
            (∑ k, L c k * K k m) * (∑ l, L d l * K l n) := by
      calc
        (∑ k, ∑ l,
            (∑ a, ∑ b, ∑ c, ∑ d,
              leviCivitaSymbol4 a b c d *
                L a i * L b j * L c k * L d l) *
              K k m * K l n) =
            ∑ k, ∑ l, ∑ a, ∑ b, ∑ c, ∑ d,
              leviCivitaSymbol4 a b c d * L a i * L b j *
                L c k * L d l * K k m * K l n := by
          simp only [Finset.sum_mul]
        _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ k, ∑ l,
              leviCivitaSymbol4 a b c d * L a i * L b j *
                L c k * L d l * K k m * K l n := by
          rw [fin4_sum_rotate3]
          apply Finset.sum_congr rfl
          intro a _
          rw [fin4_sum_rotate3]
          apply Finset.sum_congr rfl
          intro b _
          rw [fin4_sum_rotate3]
          apply Finset.sum_congr rfl
          intro c _
          rw [fin4_sum_rotate3]
        _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ k, ∑ l,
              leviCivitaSymbol4 a b c d * L a i * L b j *
                L c k * K k m * L d l * K l n := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro d _
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          ring
        _ = ∑ a, ∑ b, ∑ c, ∑ d,
              leviCivitaSymbol4 a b c d * L a i * L b j *
                (∑ k, L c k * K k m) *
                (∑ l, L d l * K l n) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ a, ∑ b,
          leviCivitaSymbol4 a b m n * L a i * L b j := by
      simp_rw [hentry]
      simp

/-- The two-index alternating complement of a covariant matrix.  Metric
Hodge is this operator applied to the twice-raised two-form, times the
Lorentzian volume factor. -/
def alternatingComplement4 (C : Matrix4) : Matrix4 :=
  fun i j => ∑ k, ∑ l, leviCivitaSymbol4 i j k l * C k l

set_option maxHeartbeats 2000000 in
/-- Cofactor covariance of the alternating complement. -/
theorem alternatingComplement4_inverse_covariant
    (L K C : Matrix4) (hLK : L * K = 1) :
    (Matrix.det L) • alternatingComplement4 (K * C * Kᵀ) =
      transportTwoForm L (alternatingComplement4 C) := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, alternatingComplement4,
    transportTwoForm, Matrix.mul_apply, Matrix.transpose_apply]
  calc
    Matrix.det L *
        (∑ k, ∑ l,
          leviCivitaSymbol4 i j k l *
            (∑ x, (∑ x_1, K k x_1 * C x_1 x) * K l x)) =
        ∑ k, ∑ l, ∑ m, ∑ n,
          Matrix.det L * leviCivitaSymbol4 i j k l *
            K k m * K l n * C m n := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ m, ∑ n, ∑ k, ∑ l,
          Matrix.det L * leviCivitaSymbol4 i j k l *
            K k m * K l n * C m n := by
      rw [fin4_sum_rotate3]
      apply Finset.sum_congr rfl
      intro m _
      rw [fin4_sum_rotate3]
    _ = ∑ m, ∑ n,
          (Matrix.det L *
            (∑ k, ∑ l,
              leviCivitaSymbol4 i j k l * K k m * K l n)) *
            C m n := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ m, ∑ n,
          (∑ a, ∑ b,
            leviCivitaSymbol4 a b m n * L a i * L b j) * C m n := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [leviCivitaSymbol4_inverse_contraction L K hLK]
    _ = ∑ a, L a i *
          (∑ b,
            (∑ m, ∑ n, leviCivitaSymbol4 a b m n * C m n) *
              L b j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [fin4_sum_rotate3]
      apply Finset.sum_congr rfl
      intro a _
      rw [fin4_sum_rotate3]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ b, (∑ a,
          L a i *
            (∑ m, ∑ n, leviCivitaSymbol4 a b m n * C m n)) *
          L b j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      ring

/-- Coordinate Hodge star on covariant two-forms.  The leading minus sign
matches the repository convention `*(e⁰∧e¹)=e²∧e³` for the
standard coordinate orientation and `(-,+,+,+)` signature. -/
noncomputable def coordinateMetricHodgeTwoForm4
    (G F : Matrix4) : Matrix4 :=
  fun i j =>
    -(Real.sqrt (-Matrix.det G) / 2) *
      ∑ k, ∑ l, ∑ m, ∑ n,
        leviCivitaSymbol4 i j k l * G⁻¹ k m * G⁻¹ l n * F m n

set_option maxHeartbeats 2000000 in
/-- Matrix form of the coordinate Hodge formula: take the alternating
complement of the twice-raised two-form and multiply by the Lorentzian volume
factor. -/
theorem coordinateMetricHodgeTwoForm4_eq_alternatingComplement
    (G F : Matrix4) :
    coordinateMetricHodgeTwoForm4 G F =
      (-(Real.sqrt (-Matrix.det G) / 2)) •
        alternatingComplement4 (G⁻¹ * F * G⁻¹ᵀ) := by
  ext i j
  simp only [coordinateMetricHodgeTwoForm4, Matrix.smul_apply, smul_eq_mul,
    alternatingComplement4, Matrix.mul_apply, Matrix.transpose_apply]
  congr 1
  calc
    (∑ k, ∑ l, ∑ m, ∑ n,
        leviCivitaSymbol4 i j k l * G⁻¹ k m * G⁻¹ l n * F m n) =
        ∑ k, ∑ l, ∑ n, ∑ m,
          leviCivitaSymbol4 i j k l * G⁻¹ k m * F m n * G⁻¹ l n := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ k, ∑ l,
          leviCivitaSymbol4 i j k l *
            (∑ x, (∑ x_1, G⁻¹ k x_1 * F x_1 x) * G⁻¹ l x) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      ring

/-- The canonical Lorentz metric is symmetric. -/
theorem minkowskiMetric_transpose : minkowskiMetricᵀ = minkowskiMetric := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkowskiMetric]

/-- Inverse of a metric written in a supplied coframe and inverse frame. -/
theorem inverse_metric_congruence
    (G L K : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    G⁻¹ = K * minkowskiMetric * Kᵀ := by
  apply Matrix.inv_eq_right_inv
  rw [hG]
  calc
    (Lᵀ * minkowskiMetric * L) * (K * minkowskiMetric * Kᵀ) =
        Lᵀ * minkowskiMetric * (L * K) * minkowskiMetric * Kᵀ := by
      noncomm_ring
    _ = Lᵀ * (minkowskiMetric * minkowskiMetric) * Kᵀ := by
      rw [hLK]
      noncomm_ring
    _ = Lᵀ * Kᵀ := by rw [minkowskiMetric_sq, Matrix.mul_one]
    _ = (K * L)ᵀ := by rw [Matrix.transpose_mul]
    _ = 1 := by rw [hKL, Matrix.transpose_one]

/-- Determinant of a Lorentzian metric reconstructed from a coframe. -/
theorem det_metric_congruence
    (G L : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L) :
    Matrix.det G = -(Matrix.det L) ^ 2 := by
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    minkowskiMetric_det]
  ring

/-- The coordinate Lorentzian volume density of a coframe metric is the
absolute determinant of the coframe. -/
theorem sqrt_neg_det_metric_congruence
    (G L : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L) :
    Real.sqrt (-Matrix.det G) = |Matrix.det L| := by
  rw [det_metric_congruence G L hG]
  simp only [neg_neg]
  exact Real.sqrt_sq_eq_abs (Matrix.det L)

/-- Twice raising a transported two-form by the coframe metric is inverse
transport of the twice-raised frame two-form. -/
theorem raised_transport_congruence
    (G L K F : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    G⁻¹ * transportTwoForm L F * G⁻¹ᵀ =
      K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ := by
  rw [inverse_metric_congruence G L K hG hKL hLK]
  unfold transportTwoForm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    minkowskiMetric_transpose]
  have hT : Kᵀ * Lᵀ = 1 := by
    rw [← Matrix.transpose_mul, hLK, Matrix.transpose_one]
  calc
    K * minkowskiMetric * Kᵀ * (Lᵀ * F * L) *
        (K * (minkowskiMetric * Kᵀ)) =
        K * minkowskiMetric * (Kᵀ * Lᵀ) * F *
          (L * K) * minkowskiMetric * Kᵀ := by
      noncomm_ring
    _ = K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ := by
      rw [hT, hLK]
      noncomm_ring

/-- Matrix form of Hodge star in the canonical Minkowski frame. -/
theorem coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement
    (F : Matrix4) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric F =
      (-(1 / 2 : ℝ)) •
        alternatingComplement4
          (minkowskiMetric * F * minkowskiMetric) := by
  rw [coordinateMetricHodgeTwoForm4_eq_alternatingComplement,
    minkowskiMetric_det]
  have hinv : minkowskiMetric⁻¹ = minkowskiMetric :=
    Matrix.inv_eq_right_inv minkowskiMetric_sq
  rw [hinv, minkowskiMetric_transpose]
  norm_num

set_option maxHeartbeats 2000000 in
/-- **Coordinate Hodge naturality up to orientation.** For any invertible
coframe `L` with supplied inverse `K`, the explicit coordinate-metric Hodge
star of a transported two-form is exactly either the transported canonical
Hodge star or its negative.  The two alternatives are determined solely by
the sign of `det L`; no detector choice or geometric convention is assumed. -/
theorem coordinateMetricHodgeTwoForm4_congruence_up_to_orientation
    (G L K F : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    coordinateMetricHodgeTwoForm4 G (transportTwoForm L F) =
        transportTwoForm L
          (coordinateMetricHodgeTwoForm4 minkowskiMetric F) ∨
      coordinateMetricHodgeTwoForm4 G (transportTwoForm L F) =
        -transportTwoForm L
          (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
  have hdetNe : Matrix.det L ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det hKL
    simp [Matrix.det_mul, hzero] at h
  have hraised := raised_transport_congruence G L K F hG hKL hLK
  have hcofactor := alternatingComplement4_inverse_covariant L K
    (minkowskiMetric * F * minkowskiMetric) hLK
  rw [coordinateMetricHodgeTwoForm4_eq_alternatingComplement,
    sqrt_neg_det_metric_congruence G L hG, hraised]
  rcases lt_or_gt_of_ne hdetNe with hneg | hpos
  · right
    rw [abs_of_neg hneg]
    calc
      (-((-Matrix.det L) / 2)) •
          alternatingComplement4
            (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ) =
          (1 / 2 : ℝ) •
            ((Matrix.det L) • alternatingComplement4
              (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ)) := by
        rw [smul_smul]
        congr 1
        ring
      _ = (1 / 2 : ℝ) •
          transportTwoForm L
            (alternatingComplement4
              (minkowskiMetric * F * minkowskiMetric)) := by
        rw [hcofactor]
      _ = -transportTwoForm L
          (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
        rw [coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement]
        rw [transportTwoForm_smul]
        ext i j
        simp
  · left
    rw [abs_of_pos hpos]
    calc
      (-(Matrix.det L / 2)) •
          alternatingComplement4
            (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ) =
          (-(1 / 2 : ℝ)) •
            ((Matrix.det L) • alternatingComplement4
              (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ)) := by
        rw [smul_smul]
        congr 1
        ring
      _ = (-(1 / 2 : ℝ)) •
          transportTwoForm L
            (alternatingComplement4
              (minkowskiMetric * F * minkowskiMetric)) := by
        rw [hcofactor]
      _ = transportTwoForm L
          (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
        rw [coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement]
        exact (transportTwoForm_smul L _ (-(1 / 2 : ℝ))).symm

set_option maxHeartbeats 2000000 in
/-- **Orientation-reversing coordinate Hodge naturality.**  A coframe with
negative determinant sends the coordinate-metric Hodge star to the negative
of the transported canonical Hodge star.  This sign-resolved companion to
`coordinateMetricHodgeTwoForm4_congruence_of_det_pos` lets the detector prove
that its exact Hodge gate has selected the positive orientation. -/
theorem coordinateMetricHodgeTwoForm4_congruence_of_det_neg
    (G L K F : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hdet : Matrix.det L < 0) :
    coordinateMetricHodgeTwoForm4 G (transportTwoForm L F) =
      -transportTwoForm L
        (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
  have hraised := raised_transport_congruence G L K F hG hKL hLK
  have hcofactor := alternatingComplement4_inverse_covariant L K
    (minkowskiMetric * F * minkowskiMetric) hLK
  rw [coordinateMetricHodgeTwoForm4_eq_alternatingComplement,
    sqrt_neg_det_metric_congruence G L hG, hraised, abs_of_neg hdet]
  calc
    (-((-Matrix.det L) / 2)) •
        alternatingComplement4
          (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ) =
        (1 / 2 : ℝ) •
          ((Matrix.det L) • alternatingComplement4
            (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ)) := by
      rw [smul_smul]
      congr 1
      ring
    _ = (1 / 2 : ℝ) •
        transportTwoForm L
          (alternatingComplement4
            (minkowskiMetric * F * minkowskiMetric)) := by
      rw [hcofactor]
    _ = -transportTwoForm L
        (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
      rw [coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement]
      rw [transportTwoForm_smul]
      ext i j
      simp

set_option maxHeartbeats 2000000 in
/-- **Exact orientation-preserving coordinate Hodge naturality.** If the
coframe has positive determinant relative to the coordinate orientation, the
orientation ambiguity in Hodge naturality disappears: the coordinate-metric
Hodge star is exactly the transported canonical Hodge star. -/
theorem coordinateMetricHodgeTwoForm4_congruence_of_det_pos
    (G L K F : Matrix4) (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hdet : 0 < Matrix.det L) :
    coordinateMetricHodgeTwoForm4 G (transportTwoForm L F) =
      transportTwoForm L
        (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
  have hraised := raised_transport_congruence G L K F hG hKL hLK
  have hcofactor := alternatingComplement4_inverse_covariant L K
    (minkowskiMetric * F * minkowskiMetric) hLK
  rw [coordinateMetricHodgeTwoForm4_eq_alternatingComplement,
    sqrt_neg_det_metric_congruence G L hG, hraised, abs_of_pos hdet]
  calc
    (-(Matrix.det L / 2)) •
        alternatingComplement4
          (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ) =
        (-(1 / 2 : ℝ)) •
          ((Matrix.det L) • alternatingComplement4
            (K * (minkowskiMetric * F * minkowskiMetric) * Kᵀ)) := by
      rw [smul_smul]
      congr 1
      ring
    _ = (-(1 / 2 : ℝ)) •
        transportTwoForm L
          (alternatingComplement4
            (minkowskiMetric * F * minkowskiMetric)) := by
      rw [hcofactor]
    _ = transportTwoForm L
        (coordinateMetricHodgeTwoForm4 minkowskiMetric F) := by
      rw [coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement]
      exact (transportTwoForm_smul L _ (-(1 / 2 : ℝ))).symm

/-- The coordinate formula agrees exactly with the repository's canonical
Hodge convention in the Minkowski frame. -/
theorem coordinateMetricHodgeTwoForm4_minkowski
    (E B : ℝ) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (canonicalMaxwellTwoForm E B) =
      canonicalHodgeStar E B := by
  have hdiag : minkowskiMetric = Matrix.diagonal minkowskiSign := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minkowskiMetric, minkowskiSign]
  have hdet : Matrix.det minkowskiMetric = -1 := by
    rw [hdiag, Matrix.det_diagonal]
    simp [minkowskiSign, Fin.prod_univ_succ]
  have hinv : minkowskiMetric⁻¹ = minkowskiMetric := by
    exact Matrix.inv_eq_right_inv minkowskiMetric_sq
  ext i j
  unfold coordinateMetricHodgeTwoForm4
  rw [hdet, hinv]
  fin_cases i <;> fin_cases j <;>
    simp [leviCivitaSymbol4, canonicalHodgeStar, canonicalMaxwellTwoForm,
      minkowskiMetric, Fin.sum_univ_succ] <;> ring

/-- Canonical-seed specialization of exact orientation-preserving coordinate
Hodge naturality. -/
theorem coordinateMetricHodgeTwoForm4_canonical_of_det_pos
    (G L K : Matrix4) (E B : ℝ)
    (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hdet : 0 < Matrix.det L) :
    coordinateMetricHodgeTwoForm4 G
        (transportTwoForm L (canonicalMaxwellTwoForm E B)) =
      transportTwoForm L (canonicalHodgeStar E B) := by
  simpa only [coordinateMetricHodgeTwoForm4_minkowski E B] using
    coordinateMetricHodgeTwoForm4_congruence_of_det_pos
      G L K (canonicalMaxwellTwoForm E B) hG hKL hLK hdet

/-- A positive-magnitude canonical Hodge seed stays nonzero under any
invertible coframe transport. -/
theorem transportedCanonicalHodge_ne_zero
    (L K : Matrix4) (q : ℝ)
    (hq : 0 < q) (hLK : L * K = 1) :
    transportTwoForm L
        (canonicalHodgeStar (Real.sqrt (2 * q)) 0) ≠ 0 := by
  intro hzero
  have hid : transportTwoForm K
      (transportTwoForm L
        (canonicalHodgeStar (Real.sqrt (2 * q)) 0)) =
      canonicalHodgeStar (Real.sqrt (2 * q)) 0 := by
    rw [← transportTwoForm_mul K L, hLK]
    simp [transportTwoForm]
  have hcanzero : canonicalHodgeStar (Real.sqrt (2 * q)) 0 = 0 := by
    rw [← hid, hzero]
    simp [transportTwoForm]
  have hcomponent := congrArg (fun M : Matrix4 ↦ M 2 3) hcanzero
  have hsqrt : Real.sqrt (2 * q) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by linarith)
  exact hsqrt (by
    simpa [canonicalHodgeStar, canonicalMaxwellTwoForm] using hcomponent)

/-- Canonical-seed specialization of coordinate Hodge naturality. -/
theorem coordinateMetricHodgeTwoForm4_canonical_up_to_orientation
    (G L K : Matrix4) (E B : ℝ)
    (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1) :
    coordinateMetricHodgeTwoForm4 G
        (transportTwoForm L (canonicalMaxwellTwoForm E B)) =
        transportTwoForm L (canonicalHodgeStar E B) ∨
      coordinateMetricHodgeTwoForm4 G
        (transportTwoForm L (canonicalMaxwellTwoForm E B)) =
        -transportTwoForm L (canonicalHodgeStar E B) := by
  simpa only [coordinateMetricHodgeTwoForm4_minkowski E B] using
    coordinateMetricHodgeTwoForm4_congruence_up_to_orientation
      G L K (canonicalMaxwellTwoForm E B) hG hKL hLK

end RainichKaluza
