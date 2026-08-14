import RainichKaluza.PolynomialMetricJetRealization
import RainichKaluza.CoordinateRicciFirstJet
import RainichKaluza.ActualCoordinateRicciFirstJet

/-!
# Actual Ricci curvature of the active polynomial metric germ

This file connects the explicit cubic metric germ to the coordinate Ricci
tensor computed from its genuine nested Frechet derivatives.  It closes the
pointwise bridge between the formal Einstein two-jet used by the active
ambiguity construction and an actual smooth metric field.
-/

namespace RainichKaluza

open scoped Matrix Topology ContDiff

set_option maxHeartbeats 2000000

/-- At a Minkowski normal-coordinate point, the full coordinate Ricci
formula reduces to the normal-frame contraction of the metric two-jet. -/
theorem coordinateRicci_minkowski_zero
    (g2 : CoordinateMetricJet2 (Fin 4)) (n p : Fin 4) :
    coordinateRicci minkowskiMetric 0 g2 n p =
      normalFrameBaseRicci minkowskiSign g2 n p := by
  fin_cases n <;> fin_cases p <;>
    simp [coordinateRicci, coordinateChristoffelJet,
      coordinateInverseMetricJet, coordinateChristoffel,
      coordinateChristoffelFirstKind,
      coordinateChristoffelFirstKindJet, normalFrameBaseRicci,
      minkowskiMetric, minkowskiSign, Fin.sum_univ_succ] <;>
    ring

/-- The Ricci tensor obtained from the actual derivatives of the active
cubic metric germ has exactly the prescribed active Einstein source at the
origin.  No unrelated formal metric-jet arrays occur on the left-hand side. -/
theorem activeAmbiguityPolynomialMetricGerm_actualRicci_zero :
    actualCoordinateRicciCovariantField4
        activeAmbiguityPolynomialMetricGerm 0 =
      activeAmbiguityCovariantRicciSource := by
  rcases activeAmbiguityPolynomialMetricGerm_realizes_threeJet with
    ⟨h0, h1, h2, _h3⟩
  funext n p
  unfold actualCoordinateRicciCovariantField4
  rw [h0, h1, h2]
  have hinv : (minkowskiMetric⁻¹ : Matrix4) = minkowskiMetric :=
    Matrix.inv_eq_right_inv minkowskiMetric_sq
  rw [hinv]
  rw [coordinateRicci_minkowski_zero]
  exact activeAmbiguityFormalMetricJet2_einsteinEquation n p

/-- The algebraic first Ricci prolongation, now fed only by the genuine
nested Frechet derivatives of the cubic metric germ, is the prescribed
common first Ricci-source jet.  The remaining step to identify this
expression with the Frechet derivative of the *composed Ricci field* is a
chain-rule theorem through matrix inversion. -/
theorem activeAmbiguityPolynomialMetricGerm_actualJets_ricciFirst
    (r n p : Fin 4) :
    coordinateRicciFirstJet
        ((coordinateMetricMatrixField4
          activeAmbiguityPolynomialMetricGerm 0)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4
          activeAmbiguityPolynomialMetricGerm 0)
        (actualCoordinateMetricJet2Field4
          activeAmbiguityPolynomialMetricGerm 0)
        (actualCoordinateMetricJet3Field4
          activeAmbiguityPolynomialMetricGerm 0) r n p =
      activeAmbiguityCommonCovariantRicciSourceFirstJet r n p := by
  rcases activeAmbiguityPolynomialMetricGerm_realizes_threeJet with
    ⟨h0, h1, h2, h3⟩
  rw [h0, h1, h2, h3]
  have hinv : (minkowskiMetric⁻¹ : Matrix4) = minkowskiMetric :=
    Matrix.inv_eq_right_inv minkowskiMetric_sq
  rw [hinv]
  exact activeAmbiguityFormalMetricJet3_einsteinFirstProlongation r n p

/-- The active cubic metric germ is componentwise regular through the
second nested coordinate derivative at the origin. -/
theorem activeAmbiguityPolynomialMetricGerm_threeJetDifferentiableAt_zero :
    CoordinateMetricThreeJetDifferentiableAt4
      activeAmbiguityPolynomialMetricGerm 0 := by
  constructor
  · intro i j
    unfold activeAmbiguityPolynomialMetricGerm
    simp only [coordinateMetricMatrixField4_cubicMetricTaylorField4]
    unfold cubicMetricTaylorMatrixField4
    fun_prop
  · intro r i j
    unfold actualCoordinateMetricJet1Field4
    unfold activeAmbiguityPolynomialMetricGerm
    simp only [coordinateMetricMatrixField4_cubicMetricTaylorField4]
    rw [show (fun y ↦ scalarFieldCoordinateFDeriv
        (fun x ↦ cubicMetricTaylorMatrixField4 minkowskiMetric
          activeAmbiguityFormalMetricJet2
          activeAmbiguityFormalMetricJet3 x i j) y r) =
      fun y ↦ ∑ s, activeAmbiguityFormalMetricJet2 r s i j * y s +
        (1 / 2 : ℝ) * ∑ s, ∑ t,
          activeAmbiguityFormalMetricJet3 r s t i j * y s * y t by
      funext y
      exact scalarFieldCoordinateFDeriv_cubicMetricTaylorMatrixField4
        minkowskiMetric activeAmbiguityFormalMetricJet2
        activeAmbiguityFormalMetricJet3
        (fun a b i j ↦ normalCoordinateMetricJet2OfRicci_deriv_symm _
          activeAmbiguityCovariantRicciSource_transpose a b i j)
        (fun a b c i j ↦
          (activeAmbiguityFormalMetricJet3_symmetries a b c i j).1)
        (fun a b c i j ↦
          (activeAmbiguityFormalMetricJet3_symmetries a b c i j).2.1)
        y r i j]
    fun_prop
  · intro r s i j
    unfold actualCoordinateMetricJet2Field4 actualCoordinateMetricJet1Field4
    unfold activeAmbiguityPolynomialMetricGerm
    simp only [coordinateMetricMatrixField4_cubicMetricTaylorField4]
    let f : CurvatureCoordinateSpace4 → ℝ := fun x ↦
      cubicMetricTaylorMatrixField4 minkowskiMetric
        activeAmbiguityFormalMetricJet2
        activeAmbiguityFormalMetricJet3 x i j
    have hf : ContDiff ℝ 3 f := by
      dsimp [f]
      unfold cubicMetricTaylorMatrixField4
      fun_prop
    have hf1 : ContDiff ℝ 2 (fderiv ℝ f) :=
      hf.fderiv_right (m := 2) (by norm_num)
    have hf1s : ContDiff ℝ 2
        (fun y ↦ fderiv ℝ f y (curvatureCoordinateDirection s)) :=
      hf1.clm_apply contDiff_const
    have hf2 : ContDiff ℝ 1
        (fderiv ℝ (fun y ↦
          fderiv ℝ f y (curvatureCoordinateDirection s))) :=
      hf1s.fderiv_right (m := 1) (by norm_num)
    have hf2r : ContDiff ℝ 1
        (fun y ↦ fderiv ℝ
          (fun x ↦ fderiv ℝ f x (curvatureCoordinateDirection s)) y
            (curvatureCoordinateDirection r)) :=
      hf2.clm_apply contDiff_const
    exact hf2r.differentiable one_ne_zero 0

/-- **Genuine first Ricci jet of the active cubic metric germ.**  The actual
coordinate Fréchet derivative of its composed Ricci field is the prescribed
common active Einstein-source first jet.  This closes the earlier chain-rule
seam; the left side contains neither an independently supplied inverse-metric
jet nor a formal Ricci first-jet array. -/
theorem activeAmbiguityPolynomialMetricGerm_actualRicci_coordinateFDeriv_zero
    (r n p : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateRicciCovariantField4
          activeAmbiguityPolynomialMetricGerm y n p) 0 r =
      activeAmbiguityCommonCovariantRicciSourceFirstJet r n p := by
  rw [scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4
    activeAmbiguityPolynomialMetricGerm 0
    activeAmbiguityPolynomialMetricGerm_threeJetDifferentiableAt_zero
    (by
      rw [(activeAmbiguityPolynomialMetricGerm_realizes_threeJet).1]
      rw [minkowskiMetric_det]
      norm_num)]
  exact activeAmbiguityPolynomialMetricGerm_actualJets_ricciFirst r n p

end RainichKaluza
