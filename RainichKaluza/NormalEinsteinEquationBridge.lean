import RainichKaluza.StagedEinsteinSourceBridge
import RainichKaluza.KaluzaRicciBase
import RainichKaluza.ActualPolynomialMetricRicci
import RainichKaluza.NormalGaugeEquationBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Normal Einstein-source to trace-reversed Ricci bridge

The curvature entrance naturally gives the Einstein tensor equal to the
trace-adjusted scalar-plus-Maxwell source.  The Kaluza backend instead tests
the equivalent trace-reversed Ricci equation.  This file proves that exact
four-dimensional algebraic conversion in the Minkowski normal frame.
-/

namespace RainichKaluza

open scoped Matrix

set_option maxHeartbeats 2000000

/-- Scalar curvature obtained by contracting a covariant Ricci matrix in the
Minkowski frame. -/
noncomputable def normalCovariantRicciScalar (Ric : Matrix4) : ℝ :=
  ∑ i, minkowskiSign i * Ric i i

/-- Covariant Einstein tensor built from a covariant Ricci matrix at a
Minkowski normal point. -/
noncomputable def normalCovariantEinsteinFromRicci
    (Ric : Matrix4) : Matrix4 :=
  fun i j => Ric i j -
    (normalCovariantRicciScalar Ric / 2) * minkowskiMetric i j

/-- Covariant ordinary Maxwell stress in the Minkowski frame. -/
noncomputable def normalCovariantMaxwellStress
    (F : Matrix4) : Matrix4 :=
  fun i j =>
    (∑ q, minkowskiSign q * F i q * F j q) -
      minkowskiMetric i j * normalTwoFormSq F / 4

/-- **Einstein source implies the trace-reversed Ricci source.**  In four
dimensions, tracing the Einstein equation removes the trace adjustment of
the scalar source, while the Maxwell stress remains tracefree. -/
theorem normalRicci_eq_traceReversedMatter_of_einsteinSource
    (Ric F : Matrix4) (v : OneForm4)
    (hF : Fᵀ = -F)
    (hEinstein : normalCovariantEinsteinFromRicci Ric =
      coordinateMatterEinsteinStressCovariant4
        minkowskiMetric minkowskiMetric v F) :
    Ric = fun i j =>
      (1 / 2 : ℝ) * v i * v j + normalCovariantMaxwellStress F i j := by
  have hFnorm := eq_lorentzSkewTwoForm4_of_transpose_eq_neg F hF
  have h00 := congrArg (fun A : Matrix4 => A 0 0) hEinstein
  have h11 := congrArg (fun A : Matrix4 => A 1 1) hEinstein
  have h22 := congrArg (fun A : Matrix4 => A 2 2) hEinstein
  have h33 := congrArg (fun A : Matrix4 => A 3 3) hEinstein
  rw [hFnorm] at h00 h11 h22 h33 ⊢
  ext i j
  have hij := congrArg (fun A : Matrix4 => A i j) hEinstein
  rw [hFnorm] at hij
  fin_cases i <;> fin_cases j <;>
    simp [normalCovariantEinsteinFromRicci,
      normalCovariantRicciScalar, normalCovariantMaxwellStress,
      coordinateMatterEinsteinStressCovariant4,
      coordinateMatterEinsteinStressMixed4,
      coordinateScalarEinsteinStressMixed4,
      coordinateMaxwellEinsteinStressMixed4,
      coordinateRaisedOneForm4, coordinateRaisedTwoForm4,
      normalTwoFormSq, normalRaisedTwoForm,
      lorentzSkewTwoForm4, minkowskiMetric, minkowskiSign,
      Fin.sum_univ_succ] at h00 h11 h22 h33 hij ⊢ <;>
    linarith

/-- The literal normal-coordinate Einstein/source equation, with the physical
Maxwell field normalized by `exp (sqrt 3 * phi / 2) / sqrt 2`, discharges the
trace-reversed Einstein block used by the Kaluza Ricci backend. -/
theorem conventionEinsteinEquationResidual_minkowski_eq_zero_of_einsteinSource
    (phi0 : ℝ) (v : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (hEinsteinSource :
      (fun i j ↦ coordinateEinsteinCovariant
        minkowskiMetric minkowskiMetric 0 g2 i j) =
      coordinateMatterEinsteinStressCovariant4
        minkowskiMetric minkowskiMetric v
        ((Real.exp (Real.sqrt 3 * phi0 / 2) / Real.sqrt 2) •
          gaugeCurvatureOfFirstJet A1)) :
    ∀ n p,
      conventionEinsteinEquationResidual phi0 minkowskiSign v A1 g2 n p = 0 := by
  let Ric : Matrix4 := fun i j ↦
    coordinateRicci minkowskiMetric 0 g2 i j
  let H : Matrix4 :=
    (Real.exp (Real.sqrt 3 * phi0 / 2) / Real.sqrt 2) •
      gaugeCurvatureOfFirstJet A1
  have hH : Hᵀ = -H := by
    dsimp [H]
    rw [gaugeCurvatureOfFirstJet_transpose]
    simp
  have hsource : normalCovariantEinsteinFromRicci Ric =
      coordinateMatterEinsteinStressCovariant4
        minkowskiMetric minkowskiMetric v H := by
    rw [← hEinsteinSource]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ric, normalCovariantEinsteinFromRicci,
        normalCovariantRicciScalar, coordinateEinsteinCovariant,
        coordinateScalarCurvature, minkowskiMetric, minkowskiSign,
        Fin.sum_univ_succ]
    all_goals ring
  have hRic := normalRicci_eq_traceReversedMatter_of_einsteinSource
    Ric H v hH hsource
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hexp :
      (Real.exp (Real.sqrt 3 * phi0 / 2)) ^ 2 =
        Real.exp (Real.sqrt 3 * phi0) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  intro n p
  have hnp := congrArg (fun T : Matrix4 ↦ T n p) hRic
  dsimp [Ric] at hnp
  rw [coordinateRicci_minkowski_zero g2 n p] at hnp
  unfold conventionEinsteinEquationResidual
  rw [show normalFrameBaseRicci minkowskiSign g2 n p =
      v n * v p / 2 + normalCovariantMaxwellStress H n p by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnp]
  fin_cases n <;> fin_cases p <;>
    simp [H, normalCovariantMaxwellStress, normalTwoFormSq,
      normalRaisedTwoForm, normalFrameMaxwellContraction,
      normalFrameMaxwellNormSq, gaugeCurvatureOfFirstJet,
      minkowskiMetric, minkowskiSign, Fin.sum_univ_succ] <;>
    field_simp [hsqrt] <;>
    rw [hsqrtSq, hexp] <;>
    ring

end RainichKaluza
