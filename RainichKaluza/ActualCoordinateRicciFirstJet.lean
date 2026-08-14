import RainichKaluza.CoordinateRicciActualDerivative

/-!
# Actual coordinate Ricci as a function of the metric three-jet

This file specializes the generic coordinate Ricci chain rule to the
literal nested Frechet derivatives of an actual metric field.  The key
matrix-inverse step is proved entrywise from Cramer's formula and the
identity `G⁻¹G = 1` near a nonsingular point.

The result is fixed-coordinate.  It makes no chart-covariance claim.
-/

namespace RainichKaluza

open scoped Matrix Topology

set_option maxHeartbeats 2000000

/-- Entrywise differentiability of a real `4 × 4` matrix field at a point. -/
def MatrixFieldDifferentiableAt4
    (G : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  ∀ i j, DifferentiableAt ℝ (fun y ↦ G y i j) z

theorem MatrixFieldDifferentiableAt4.det
    {G : CurvatureCoordinateSpace4 → Matrix4}
    {z : CurvatureCoordinateSpace4}
    (hG : MatrixFieldDifferentiableAt4 G z) :
    DifferentiableAt ℝ (fun y ↦ Matrix.det (G y)) z := by
  simp_rw [Matrix.det_apply]
  rw [show (fun y ↦ ∑ σ, Equiv.Perm.sign σ •
      ∏ k, G y (σ k) k) =
      ∑ σ, fun y ↦ Equiv.Perm.sign σ • ∏ k, G y (σ k) k by rfl]
  apply DifferentiableAt.sum
  intro σ _
  apply DifferentiableAt.const_smul
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (g := fun k y ↦ G y (σ k) k)
    (g' := fun k ↦ fderiv ℝ (fun y ↦ G y (σ k) k) z)
    (fun k _ ↦ (hG (σ k) k).hasFDerivAt)).differentiableAt

theorem MatrixFieldDifferentiableAt4.adjugate
    {G : CurvatureCoordinateSpace4 → Matrix4}
    {z : CurvatureCoordinateSpace4}
    (hG : MatrixFieldDifferentiableAt4 G z) :
    MatrixFieldDifferentiableAt4 (fun y ↦ Matrix.adjugate (G y)) z := by
  intro i j
  rw [show (fun y ↦ Matrix.adjugate (G y) i j) =
      fun y ↦ Matrix.det ((G y).updateRow j (Pi.single i 1)) by
    funext y
    exact Matrix.adjugate_apply (G y) i j]
  apply MatrixFieldDifferentiableAt4.det
  intro r c
  simp only [Matrix.updateRow_apply]
  by_cases hr : r = j
  · simp only [if_pos hr]
    fun_prop
  · simp only [if_neg hr]
    exact hG r c

theorem differentiableAt_matrixNonsingInv_apply4
    (G : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hG : MatrixFieldDifferentiableAt4 G z)
    (hdet : Matrix.det (G z) ≠ 0)
    (i j : Fin 4) :
    DifferentiableAt ℝ (fun y ↦ (G y)⁻¹ i j) z := by
  rw [show (fun y ↦ (G y)⁻¹ i j) =
      fun y ↦ (Matrix.det (G y))⁻¹ * Matrix.adjugate (G y) i j by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl]
  exact (hG.det.inv hdet).mul (hG.adjugate i j)

/-- The actual coordinate derivative of the matrix inverse is
`-G⁻¹ (∂G) G⁻¹`. -/
theorem scalarFieldCoordinateFDeriv_matrixNonsingInv_apply4
    (G : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hG : MatrixFieldDifferentiableAt4 G z)
    (hdet : Matrix.det (G z) ≠ 0)
    (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv (fun y ↦ (G y)⁻¹ i j) z r =
      -∑ a : Fin 4, ∑ b : Fin 4,
        (G z)⁻¹ i a *
          scalarFieldCoordinateFDeriv (fun y ↦ G y a b) z r *
            (G z)⁻¹ b j := by
  let H : CurvatureCoordinateSpace4 → Matrix4 := fun y ↦ (G y)⁻¹
  have hH : MatrixFieldDifferentiableAt4 H z := by
    intro i' j'
    exact differentiableAt_matrixNonsingInv_apply4 G z hG hdet i' j'
  have hright : ∀ y, H y * G y =
      ((Matrix.det (G y))⁻¹ * Matrix.det (G y)) • (1 : Matrix4) := by
    intro y
    change (G y)⁻¹ * G y = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mul,
      Matrix.adjugate_mul, smul_smul]
  have hrightNear : H * G =ᶠ[nhds z] fun _ ↦ (1 : Matrix4) := by
    have hdetNear : ∀ᶠ y in nhds z, Matrix.det (G y) ≠ 0 := by
      exact hG.det.continuousAt.eventually_ne hdet
    filter_upwards [hdetNear] with y hy
    ext a b
    rw [Pi.mul_apply, hright y]
    simp [hy]
  have hderivZero (i' j' : Fin 4) : fderiv ℝ
      (fun y ↦ ∑ a : Fin 4, H y i' a * G y a j') z = 0 := by
    have hcomponent :
        (fun y ↦ ∑ a : Fin 4, H y i' a * G y a j') =ᶠ[nhds z]
          fun _ ↦ (if i' = j' then 1 else 0 : ℝ) := by
      filter_upwards [hrightNear] with y hy
      simpa [Matrix.mul_apply, Matrix.one_apply] using
        congrFun (congrFun hy i') j'
    rw [Filter.EventuallyEq.fderiv_eq hcomponent]
    simp
  have hproductDeriv (i' j' : Fin 4) : fderiv ℝ
      (fun y ↦ ∑ a : Fin 4, H y i' a * G y a j') z =
      ∑ a : Fin 4, ((H z i' a) • fderiv ℝ (fun y ↦ G y a j') z +
          (G z a j') • fderiv ℝ (fun y ↦ H y i' a) z) := by
    rw [show (fun y ↦ ∑ a : Fin 4, H y i' a * G y a j') =
        ∑ a : Fin 4, fun y ↦ H y i' a * G y a j' by rfl]
    rw [fderiv_sum]
    · apply Finset.sum_congr rfl
      intro a _
      change fderiv ℝ ((fun y ↦ H y i' a) *
          (fun y ↦ G y a j')) z = _
      rw [fderiv_mul (hH i' a) (hG a j')]
    · intro a _
      exact (hH i' a).mul (hG a j')
  have hderivMatrix :
      (show Matrix4 from fun a c ↦ scalarFieldCoordinateFDeriv
        (fun y ↦ H y a c) z r) * G z =
        -(H z * (show Matrix4 from fun a c ↦
          scalarFieldCoordinateFDeriv (fun y ↦ G y a c) z r)) := by
    ext i' j'
    have hzero := hderivZero i' j'
    rw [hproductDeriv i' j'] at hzero
    have hdirection := DFunLike.congr_fun hzero
      (curvatureCoordinateDirection r)
    simp only [sum_apply, add_apply, smul_apply, smul_eq_mul,
      zero_apply] at hdirection
    simp only [Matrix.mul_apply, Matrix.neg_apply]
    rw [Finset.sum_add_distrib] at hdirection
    exact eq_neg_of_add_eq_zero_right (by
      simpa [scalarFieldCoordinateFDeriv, mul_comm] using hdirection)
  have hunit : IsUnit (Matrix.det (G z)) :=
    isUnit_iff_ne_zero.mpr hdet
  have hsolve := congrArg (fun M : Matrix4 ↦ M * (G z)⁻¹) hderivMatrix
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv (G z) hunit,
    Matrix.mul_one] at hsolve
  change (show Matrix4 from fun a c ↦ scalarFieldCoordinateFDeriv
      (fun y ↦ H y a c) z r) i j = _
  rw [hsolve]
  simp only [Matrix.mul_apply, Matrix.neg_apply, Finset.sum_mul,
    neg_mul, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]

/-- Componentwise regularity needed to differentiate coordinate Ricci once.
These hypotheses are exactly regularity through the genuine nested metric
second derivative, i.e. an actual metric three-jet. -/
structure CoordinateMetricThreeJetDifferentiableAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop where
  metric : ∀ i j, DifferentiableAt ℝ
    (fun y ↦ coordinateMetricMatrixField4 g y i j) z
  first : ∀ r i j, DifferentiableAt ℝ
    (fun y ↦ actualCoordinateMetricJet1Field4 g y r i j) z
  second : ∀ r s i j, DifferentiableAt ℝ
    (fun y ↦ actualCoordinateMetricJet2Field4 g y r s i j) z

/-- **Primitive j3-to-dRicci factorization.**  At a nonsingular point, the
actual derivative of the composed coordinate Ricci field is exactly the
algebraic Ricci first-jet evaluator on the literal nested metric three-jet. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (r n p : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateRicciCovariantField4 g y n p) z r =
      coordinateRicciFirstJet
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (actualCoordinateMetricJet2Field4 g z)
        (actualCoordinateMetricJet3Field4 g z) r n p := by
  unfold actualCoordinateRicciCovariantField4
  apply coordinateRicci_actual_derivative
  · intro i j
    exact differentiableAt_matrixNonsingInv_apply4
      (coordinateMetricMatrixField4 g) z hreg.metric hdet i j
  · exact hreg.first
  · exact hreg.second
  · intro i j
    rw [scalarFieldCoordinateFDeriv_matrixNonsingInv_apply4
      (coordinateMetricMatrixField4 g) z hreg.metric hdet r i j]
    rfl
  · intros
    rfl
  · intros
    rfl

/-- Equality of literal fixed-coordinate metric four-jets therefore forces
equality of the actual Ricci one-jets.  Only the order-three truncation is
used by this theorem; the order-four slot is retained so it composes
directly with the detector's primitive input package. -/
theorem actualCoordinateRicciFirstJet_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hreg' : CoordinateMetricThreeJetDifferentiableAt4 g' z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0) :
    ∀ r n p,
      scalarFieldCoordinateFDeriv
          (fun y ↦ actualCoordinateRicciCovariantField4 g y n p) z r =
        scalarFieldCoordinateFDeriv
          (fun y ↦ actualCoordinateRicciCovariantField4 g' y n p) z r := by
  have hmetric := coordinateMetricMatrixField4_eq_of_sameFourJet h
  have hdet' : Matrix.det (coordinateMetricMatrixField4 g' z) ≠ 0 := by
    rw [← hmetric]
    exact hdet
  intro r n p
  rw [scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4
      g z hreg hdet r n p,
    scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4
      g' z hreg' hdet' r n p,
    hmetric,
    actualCoordinateMetricJet1Field4_eq_of_sameFourJet h,
    actualCoordinateMetricJet2Field4_eq_of_sameFourJet h,
    actualCoordinateMetricJet3Field4_eq_of_sameFourJet h]

end RainichKaluza
