import RainichKaluza.FourthOrderMetricDetector

/-!
# Regularity of the selected actual-metric detector frame

This file closes the local analytic bookkeeping gap between smooth
principal-projector data and the `C^n` true coframe used by the
actual-metric fourth-order detector.  No curvature regularity is unfolded
here: the first theorem starts from smooth selected Maxwell projector
fields, and the second starts from a smooth residual and reconstructed
squared magnitude.

The strict frame-sign hypotheses needed by Gram--Schmidt are not repeated
as independent assumptions.  They are exactly the last four gates of the
pointwise upstream entrance predicate.  The orientation bit acts by a
constant matrix and therefore costs no differentiability.
-/

namespace RainichKaluza

/-- Smooth selected Maxwell projector fields, a smooth metric, and
pointwise upstream entrance make the detector's true dual coframe
entrywise `C^n`.

The proof follows the actual finite construction: project the fixed probes,
form the selected Lorentzian pivot, apply signed Gram--Schmidt, assemble the
column frame, invert it on the upstream nonsingular patch, and finally apply
the constant orientation reflection. -/
theorem matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_of_projectors
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hg : ContDiffOn ℝ n g U)
    (hminus : MatrixFieldContDiffOn n U
      (actualMetricMaxwellMinusProjectorCandidateField4 g choice))
    (hplus : MatrixFieldContDiffOn n U
      (actualMetricMaxwellPlusProjectorCandidateField4 g choice))
    (hupstream : ∀ z ∈ U,
      IsActualMetricUpstreamEntranceAt4 g z choice) :
    MatrixFieldContDiffOn n U
      (actualMetricPrincipalCoframeCandidateField4 g choice) := by
  have hminus0 : ContDiffOn ℝ n
      (actualMetricMaxwellMinusProbe0Field4 g choice) U := by
    exact contDiffOn_smoothMatrixProjectedVector hminus
      (curvatureCoordinateDirection choice.maxwellMinusProbe0)
  have hminus1 : ContDiffOn ℝ n
      (actualMetricMaxwellMinusProbe1Field4 g choice) U := by
    exact contDiffOn_smoothMatrixProjectedVector hminus
      (curvatureCoordinateDirection choice.maxwellMinusProbe1)
  have hpivot : ContDiffOn ℝ n
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) U := by
    exact contDiffOn_smoothLorentzianPivotCandidate
      choice.maxwellMinusPivotRecipe hg hminus0 hminus1
  have hcompanion : ContDiffOn ℝ n
      (actualMetricMaxwellLorentzCompanionCandidateField4 g choice) U := by
    exact contDiffOn_smoothLorentzianPivotCompanion
      choice.maxwellMinusPivotRecipe hminus0 hminus1
  have hplus0 : ContDiffOn ℝ n
      (actualMetricMaxwellPlusProbe0Field4 g choice) U := by
    exact contDiffOn_smoothMatrixProjectedVector hplus
      (curvatureCoordinateDirection choice.maxwellPlusProbe0)
  have hplus1 : ContDiffOn ℝ n
      (actualMetricMaxwellPlusProbe1Field4 g choice) U := by
    exact contDiffOn_smoothMatrixProjectedVector hplus
      (curvatureCoordinateDirection choice.maxwellPlusProbe1)
  have hsigns : ∀ z ∈ U,
      smoothMetricPairing g
          (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
          (actualMetricMaxwellLorentzPivotCandidateField4 g choice) z < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) z ∧
        0 < smoothMetricPairing g
          (actualMetricMaxwellPlusProbe0Field4 g choice)
          (actualMetricMaxwellPlusProbe0Field4 g choice) z ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe1Field4 g choice))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe1Field4 g choice)) z := by
    intro z hz
    have h := hupstream z hz
    unfold IsActualMetricUpstreamEntranceAt4 at h
    dsimp only at h
    rcases h with
      ⟨_, _, _, _, _, _, _, _, _, htime, hLorentzRemainder,
        hspace, hSpaceRemainder⟩
    exact ⟨htime, hLorentzRemainder, hspace, hSpaceRemainder⟩
  have hT : ContDiffOn ℝ n
      (actualMetricPrincipalTetradCandidateField4 g choice) U := by
    exact contDiffOn_smoothPrincipalTetradFromFields
      hg hpivot hcompanion hplus0 hplus1
      (fun z hz => (hsigns z hz).1)
      (fun z hz => (hsigns z hz).2.1)
      (fun z hz => (hsigns z hz).2.2.1)
      (fun z hz => (hsigns z hz).2.2.2)
  have hframe : MatrixFieldContDiffOn n U
      (actualMetricPrincipalFrameCandidateField4 g choice) := by
    exact contDiffOn_smoothPrincipalFrameMatrix hT
  have hframeDet : ∀ z ∈ U,
      Matrix.det (actualMetricPrincipalFrameCandidateField4 g choice z) ≠ 0 := by
    intro z hz hzero
    have hcoframeDet :=
      actualMetricPrincipalCoframeCandidate_det_ne_zero_of_upstream
        g z choice (hupstream z hz)
    apply hcoframeDet
    cases horientation : choice.orientationReverse
    · simp [actualMetricPrincipalCoframeCandidateField4,
        orientPrincipalCoframe4, horientation,
        Matrix.det_nonsing_inv, hzero]
    · simp [actualMetricPrincipalCoframeCandidateField4,
        orientPrincipalCoframe4, horientation, Matrix.det_mul,
        Matrix.det_nonsing_inv, hzero]
  have hinverse : MatrixFieldContDiffOn n U (fun z =>
      (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹) :=
    hframe.inv hframeDet
  cases horientation : choice.orientationReverse
  · rw [show actualMetricPrincipalCoframeCandidateField4 g choice =
        fun z => (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹ by
      funext z
      simp [actualMetricPrincipalCoframeCandidateField4,
        orientPrincipalCoframe4, horientation]]
    exact hinverse
  · have horiented :=
      (matrixFieldContDiffOn_const principalOrientationReflection4).mul
        hinverse
    rw [show actualMetricPrincipalCoframeCandidateField4 g choice = fun z =>
        principalOrientationReflection4 *
          (actualMetricPrincipalFrameCandidateField4 g choice z)⁻¹ by
      funext z
      simp [actualMetricPrincipalCoframeCandidateField4,
        orientPrincipalCoframe4, horientation]]
    exact horiented

/-- A smooth selected Maxwell residual and positive reconstructed square
automatically provide the smooth projector fields required by the preceding
coframe theorem.  Positivity is read from upstream entrance, so it is not an
extra premise. -/
theorem matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_of_residual
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hg : ContDiffOn ℝ n g U)
    (hresidual : MatrixFieldContDiffOn n U
      (actualMetricMaxwellResidualCandidateField4 g choice))
    (hqSq : ContDiffOn ℝ n
      (actualRicciReconstructedQSqField4 g) U)
    (hupstream : ∀ z ∈ U,
      IsActualMetricUpstreamEntranceAt4 g z choice) :
    MatrixFieldContDiffOn n U
      (actualMetricPrincipalCoframeCandidateField4 g choice) := by
  have hpos : ∀ z ∈ U, 0 < actualRicciReconstructedQSqField4 g z := by
    intro z hz
    have hq := IsActualMetricUpstreamEntranceAt4.qPos
      g z choice (hupstream z hz)
    exact Real.sqrt_pos.mp (by
      simpa [positiveMaxwellMagnitudeFromSquare] using hq)
  have hprojectors :=
    contDiffOn_curvatureMaxwellPrincipalProjectorFields
      hresidual hqSq hpos
  exact
    matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_of_projectors
      g choice hg hprojectors.1 hprojectors.2 hupstream

/-- On an upstream patch, `C^n` regularity of the reconstructed squared
magnitude gives the same regularity for the detector's protected positive
magnitude. -/
theorem contDiffOn_actualMetricPositiveMaxwellMagnitude_of_qSq
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hqSq : ContDiffOn ℝ n
      (actualRicciReconstructedQSqField4 g) U)
    (hupstream : ∀ z ∈ U,
      IsActualMetricUpstreamEntranceAt4 g z choice) :
    ContDiffOn ℝ n
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U := by
  apply contDiffOn_positiveMaxwellMagnitudeFromSquare hqSq
  intro z hz
  have hq := IsActualMetricUpstreamEntranceAt4.qPos
    g z choice (hupstream z hz)
  exact Real.sqrt_pos.mp (by
    simpa [positiveMaxwellMagnitudeFromSquare] using hq)

/-- Convenient joint regularity package at the order used by the
fourth-order detector composition. -/
theorem actualMetricDetectorRegularity_of_residual
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (hg : ContDiffOn ℝ n g U)
    (hresidual : MatrixFieldContDiffOn n U
      (actualMetricMaxwellResidualCandidateField4 g choice))
    (hqSq : ContDiffOn ℝ n
      (actualRicciReconstructedQSqField4 g) U)
    (hupstream : ∀ z ∈ U,
      IsActualMetricUpstreamEntranceAt4 g z choice) :
    MatrixFieldContDiffOn n U
        (actualMetricPrincipalCoframeCandidateField4 g choice) ∧
      ContDiffOn ℝ n
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) U := by
  exact
    ⟨matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_of_residual
      g choice hg hresidual hqSq hupstream,
    contDiffOn_actualMetricPositiveMaxwellMagnitude_of_qSq
      g choice hqSq hupstream⟩

end RainichKaluza
