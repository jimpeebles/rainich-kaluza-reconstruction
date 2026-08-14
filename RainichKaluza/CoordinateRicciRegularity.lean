import RainichKaluza.ActualCoordinateRicciFirstJet

/-!
# Compositional regularity for coordinate Ricci

This file proves differentiability of the literal fixed-coordinate Ricci
components without asking automation to unfold the entire contraction at
once.  The proof follows the formula's dependency graph through the inverse
metric jet, the Christoffel symbols, their coordinate jet, and finally the
four finite Ricci contractions.
-/

namespace RainichKaluza

private theorem differentiableAt_univ_sum_apply
    {I : Type*} [Fintype I]
    (f : I → CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    DifferentiableAt ℝ (fun y ↦ ∑ i, f i y) z := by
  rw [show (fun y ↦ ∑ i, f i y) = ∑ i, f i by
    funext y
    simp]
  apply DifferentiableAt.sum
  intro i _
  exact hf i

private theorem differentiableAt_coordinateChristoffelFirstKind4
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (z : CurvatureCoordinateSpace4)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (Q N P : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) z := by
  unfold coordinateChristoffelFirstKind
  simpa [div_eq_mul_inv] using
    (((hdg N Q P).add (hdg P Q N)).sub
      (hdg Q N P)).mul_const (1 / 2 : ℝ)

private theorem differentiableAt_coordinateChristoffelFirstKindJet4
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (z : CurvatureCoordinateSpace4)
    (hddg : ∀ R S A B, DifferentiableAt ℝ (fun y ↦ ddg y R S A B) z)
    (R Q N P : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKindJet (ddg y) R Q N P) z := by
  unfold coordinateChristoffelFirstKindJet
  simpa [div_eq_mul_inv] using
    (((hddg R N Q P).add (hddg R P Q N)).sub
      (hddg R Q N P)).mul_const (1 / 2 : ℝ)

private theorem differentiableAt_coordinateInverseMetricJet4
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (z : CurvatureCoordinateSpace4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (R M N : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) R M N) z := by
  unfold coordinateInverseMetricJet
  apply DifferentiableAt.neg
  apply differentiableAt_univ_sum_apply
  intro A
  apply differentiableAt_univ_sum_apply
  intro B
  exact ((hgi M A).mul (hdg R A B)).mul (hgi B N)

private theorem differentiableAt_coordinateChristoffel4
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (z : CurvatureCoordinateSpace4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (M N P : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffel (gInv y) (dg y) M N P) z := by
  unfold coordinateChristoffel
  apply differentiableAt_univ_sum_apply
  intro Q
  exact (hgi M Q).mul
    (differentiableAt_coordinateChristoffelFirstKind4 dg z hdg Q N P)

private theorem differentiableAt_coordinateChristoffelJet4
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (z : CurvatureCoordinateSpace4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (hddg : ∀ R S A B, DifferentiableAt ℝ (fun y ↦ ddg y R S A B) z)
    (R M N P : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelJet
        (gInv y) (dg y) (ddg y) R M N P) z := by
  unfold coordinateChristoffelJet
  apply differentiableAt_univ_sum_apply
  intro Q
  exact ((differentiableAt_coordinateInverseMetricJet4
      gInv dg z hgi hdg R M Q).mul
        (differentiableAt_coordinateChristoffelFirstKind4
          dg z hdg Q N P)).add
    ((hgi M Q).mul
      (differentiableAt_coordinateChristoffelFirstKindJet4
        ddg z hddg R Q N P))

/-- Coordinate Ricci is differentiable whenever its inverse-metric, metric
first-jet, and metric-second-jet component fields are differentiable. -/
theorem differentiableAt_coordinateRicci4_of_components
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (z : CurvatureCoordinateSpace4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (hddg : ∀ R S A B, DifferentiableAt ℝ (fun y ↦ ddg y R S A B) z)
    (N P : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateRicci (gInv y) (dg y) (ddg y) N P) z := by
  have hΓ (M A B : Fin 4) :=
    differentiableAt_coordinateChristoffel4 gInv dg z hgi hdg M A B
  have hdΓ (R M A B : Fin 4) :=
    differentiableAt_coordinateChristoffelJet4
      gInv dg ddg z hgi hdg hddg R M A B
  unfold coordinateRicci
  apply DifferentiableAt.sub
  · apply DifferentiableAt.add
    · apply DifferentiableAt.sub
      · apply differentiableAt_univ_sum_apply
        intro M
        exact hdΓ M M N P
      · apply differentiableAt_univ_sum_apply
        intro M
        exact hdΓ N M M P
    · apply differentiableAt_univ_sum_apply
      intro Q
      apply DifferentiableAt.mul
      · apply differentiableAt_univ_sum_apply
        intro M
        exact hΓ M M Q
      · exact hΓ Q N P
  · apply differentiableAt_univ_sum_apply
    intro M
    apply differentiableAt_univ_sum_apply
    intro Q
    exact (hΓ M N Q).mul (hΓ Q M P)

/-- The literal coordinate Ricci components are differentiable at every
nonsingular point carrying the repository's metric-three-jet regularity
package. -/
theorem differentiableAt_actualCoordinateRicciCovariantField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (i j : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ actualCoordinateRicciCovariantField4 g y i j) z := by
  unfold actualCoordinateRicciCovariantField4
  apply differentiableAt_coordinateRicci4_of_components
  · intro A B
    exact differentiableAt_matrixNonsingInv_apply4
      (coordinateMetricMatrixField4 g) z hreg.metric hdet A B
  · exact hreg.first
  · exact hreg.second

end RainichKaluza
