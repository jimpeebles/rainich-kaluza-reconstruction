import RainichKaluza.CouplingPhasePatch
import RainichKaluza.InvariantActiveWedge

/-!
# Actual-metric fixed-choice phase propagation

`CouplingPhasePatch` isolates the patchwise calculus in one fixed
trivialization.  The literal metric detector, however, stores its channel
covectors in the moving principal coframe: its accepted `dA` is the pullback
of the genuine coordinate derivative by the inverse coframe.  This file
performs that frame conversion explicitly.

For one actual-metric choice accepted at every point of an open convex patch,
the existing fourth-order equation gives the pulled-back `dA` phase law.  If
the proposed fifth-order `dB` law is imposed in the same principal frame,
coframe invertibility converts both laws back to coordinate Frechet
derivatives.  The generic patch theorem then propagates `A²+B²=3` from one
base point.
-/

namespace RainichKaluza

open scoped Matrix Topology

/-- A covector identity in an invertible pulled-back frame can be returned to
the coordinate frame. -/
theorem covector_eq_smul_pull_of_pull_eq_smul
    (L K : Matrix4) (d omegaP : OneForm4) (r : ℝ)
    (hKL : K * L = 1)
    (h : pullCovectorToPrincipalFrame K d = r • omegaP) :
    d = r • pullCovectorToPrincipalFrame L omegaP := by
  have hpulled := congrArg (pullCovectorToPrincipalFrame L) h
  rw [pullCovectorToPrincipalFrame_comp, hKL,
    pullCovectorToPrincipalFrame_one,
    pullCovectorToPrincipalFrame_smul] at hpulled
  exact hpulled

/-- Package one literal actual-metric raw choice that is accepted throughout
the patch as the fixed channel datum used by the phase calculus.  All stored
covectors are in the detector's principal-frame trivialization. -/
noncomputable def actualMetricFixedFourthOrderChannelPatch
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    FixedFourthOrderChannelPatch U where
  seedAmplitude x := Real.sqrt
    (2 * positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g) x)
  scalarCovector x := pullCovectorToPrincipalFrame
    (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus x)
  cosineDerivative x := pullCovectorToPrincipalFrame
    (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
    (curvatureSeedCosineCoordinateDerivative
      (actualMetricPrincipalCoframeCandidateField4 g choice)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus)
      choice.channel.1 x)
  channels x := curvatureSeedCanonicalChannelField
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)) x
  choice := choice.channel
  accepted := by
    intro x hx
    have h := (haccepted x hx).toCurvatureSeed
    unfold IsCurvatureSeedFourthOrderCandidateAt
      IsTransportedSeedFourthOrderCandidate at h
    exact h

namespace ActualMetricFixedPhasePatch

variable {U : Set CurvatureCoordinateSpace4}

/-- The fixed accepted patch's reconstructed cosine is definitionally the
literal curvature-seed cosine scalar used by the metric detector. -/
theorem cosineComponent_eq_curvatureSeedCosineField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    (actualMetricFixedFourthOrderChannelPatch g choice haccepted).cosineComponent =
      curvatureSeedCosineField
        (actualMetricPrincipalCoframeCandidateField4 g choice)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g))
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        choice.channel.1 := by
  rfl

/-- The covector stored by the actual-metric patch is exactly the genuine
coordinate derivative of its cosine scalar, pulled to the principal frame. -/
theorem cosineDerivative_eq_pull_coordinateFDeriv
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (x : CurvatureCoordinateSpace4) :
    let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
    P.cosineDerivative x = pullCovectorToPrincipalFrame
      (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
      (scalarFieldCoordinateFDeriv P.cosineComponent x) := by
  rfl

/-- The ordinary actual-metric detector output is exactly the sum of squares
of the two scalar fields stored by the fixed patch package. -/
theorem couplingSqCandidate_eq_components
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (x : CurvatureCoordinateSpace4) :
    actualMetricFourthOrderCouplingSqCandidateAt g x choice =
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      P.cosineComponent x ^ 2 + P.sineComponent x ^ 2 := by
  rfl

/-- Coordinate-frame phase form obtained by pushing the detector's
principal-frame phase form through the selected coframe. -/
noncomputable def coordinatePhaseOneForm
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    CurvatureCoordinateSpace4 → OneForm4 :=
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  fun x ↦ pullCovectorToPrincipalFrame
    (actualMetricPrincipalCoframeCandidateField4 g choice x)
    (phaseOneFormFromEffectiveChannel
      (P.effectiveOneForm x) (P.reflectedScalarCovector x)
      (P.sineComponent x))

/-- The two detector phase equations, returned from the moving principal
frame to honest coordinate covectors.  This is the reusable pointwise seam
between the actual-metric detector and field-level phase calculus.

No differentiability hypothesis is needed here: both displayed terms are
the repository's literal coordinate `fderiv` covectors.  Differentiability
is only needed when these identities are promoted to `HasFDerivAt` facts. -/
theorem coordinateFDerivatives_eq_phaseLaws
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    {x : CurvatureCoordinateSpace4} (hx : x ∈ U)
    (hBeq :
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      sineCouplingPropagationEquation
        (pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x))
        (P.effectiveOneForm x) (P.reflectedScalarCovector x)
        (P.cosineComponent x) (P.sineComponent x) = 0) :
    let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
    scalarFieldCoordinateFDeriv P.cosineComponent x =
        (-2 * P.sineComponent x) •
          coordinatePhaseOneForm g choice haccepted x ∧
      scalarFieldCoordinateFDeriv P.sineComponent x =
        (2 * P.cosineComponent x) •
          coordinatePhaseOneForm g choice haccepted x := by
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  let L : CurvatureCoordinateSpace4 → Matrix4 :=
    actualMetricPrincipalCoframeCandidateField4 g choice
  let omegaP : CurvatureCoordinateSpace4 → OneForm4 := fun y ↦
    phaseOneFormFromEffectiveChannel
      (P.effectiveOneForm y) (P.reflectedScalarCovector y)
      (P.sineComponent y)
  have hframe : (L x)⁻¹ * L x = 1 :=
    actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
      g x choice (haccepted x hx).1
  constructor
  · have hphaseP : P.cosineDerivative x =
        (-2 * P.sineComponent x) • omegaP x := by
      apply sub_eq_zero.mp
      rw [← nextOrderSineCouplingEquation_eq_phaseLawResidual]
      exact P.cosinePhaseEquation x hx
    rw [cosineDerivative_eq_pull_coordinateFDeriv
      g choice haccepted x] at hphaseP
    have hcoordinate := covector_eq_smul_pull_of_pull_eq_smul
      (L x) (L x)⁻¹
      (scalarFieldCoordinateFDeriv P.cosineComponent x)
      (omegaP x) (-2 * P.sineComponent x) hframe hphaseP
    simpa only [coordinatePhaseOneForm, P, L, omegaP] using hcoordinate
  · have hphaseP : pullCovectorToPrincipalFrame (L x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x) =
        (2 * P.cosineComponent x) • omegaP x :=
      (sineCouplingPropagationEquation_eq_zero_iff
        (pullCovectorToPrincipalFrame (L x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x))
        (P.effectiveOneForm x) (P.reflectedScalarCovector x)
        (P.cosineComponent x) (P.sineComponent x)).mp hBeq
    have hcoordinate := covector_eq_smul_pull_of_pull_eq_smul
      (L x) (L x)⁻¹
      (scalarFieldCoordinateFDeriv P.sineComponent x)
      (omegaP x) (2 * P.cosineComponent x) hframe hphaseP
    simpa only [coordinatePhaseOneForm, P, L, omegaP] using hcoordinate

/-- **Literal actual-metric fixed-choice propagation.**  Persistent complete
acceptance supplies the principal-frame `dA` equation.  The only new phase
equation is the corresponding principal-frame `dB` equation.  Under honest
differentiability of the reconstructed scalars, a single Kaluza selector at
the base point propagates across the open convex patch. -/
theorem couplingSq_eq_three
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hAdiff : ∀ x ∈ U, DifferentiableAt ℝ
      (actualMetricFixedFourthOrderChannelPatch g choice haccepted).cosineComponent x)
    (hBdiff : ∀ x ∈ U, DifferentiableAt ℝ
      (actualMetricFixedFourthOrderChannelPatch g choice haccepted).sineComponent x)
    (hBeq : ∀ x ∈ U,
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      sineCouplingPropagationEquation
        (pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x))
        (P.effectiveOneForm x) (P.reflectedScalarCovector x)
        (P.cosineComponent x) (P.sineComponent x) = 0)
    {x0 : CurvatureCoordinateSpace4} (hx0 : x0 ∈ U)
    (hbase :
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      P.cosineComponent x0 ^ 2 + P.sineComponent x0 ^ 2 = 3) :
    ∀ x ∈ U,
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      P.cosineComponent x ^ 2 + P.sineComponent x ^ 2 = 3 := by
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  let L : CurvatureCoordinateSpace4 → Matrix4 :=
    actualMetricPrincipalCoframeCandidateField4 g choice
  let omegaP : CurvatureCoordinateSpace4 → OneForm4 := fun x ↦
    phaseOneFormFromEffectiveChannel
      (P.effectiveOneForm x) (P.reflectedScalarCovector x)
      (P.sineComponent x)
  let omega : CurvatureCoordinateSpace4 → OneForm4 := fun x ↦
    pullCovectorToPrincipalFrame (L x) (omegaP x)
  apply couplingSq_eq_three_of_phaseLaws_on_openConvex
    U hUopen hUconvex P.cosineComponent P.sineComponent
    (fun x ↦ oneForm4ContinuousLinearMap (omega x))
  · intro x hx
    have hphaseP : P.cosineDerivative x =
        (-2 * P.sineComponent x) • omegaP x := by
      apply sub_eq_zero.mp
      rw [← nextOrderSineCouplingEquation_eq_phaseLawResidual]
      exact P.cosinePhaseEquation x hx
    rw [cosineDerivative_eq_pull_coordinateFDeriv
      g choice haccepted x] at hphaseP
    have hderiv : scalarFieldCoordinateFDeriv P.cosineComponent x =
        (-2 * P.sineComponent x) • omega x := by
      apply covector_eq_smul_pull_of_pull_eq_smul
        (L x) (L x)⁻¹ _ (omegaP x) (-2 * P.sineComponent x)
      · exact actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
          g x choice (haccepted x hx).1
      · exact hphaseP
    have h := hasFDerivAt_of_coordinateFDeriv
      P.cosineComponent _ x (hAdiff x hx) hderiv
    simpa only [omega, oneForm4ContinuousLinearMap_smul] using h
  · intro x hx
    have hphaseP : pullCovectorToPrincipalFrame (L x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x) =
        (2 * P.cosineComponent x) • omegaP x :=
      (sineCouplingPropagationEquation_eq_zero_iff
        (pullCovectorToPrincipalFrame (L x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x))
        (P.effectiveOneForm x) (P.reflectedScalarCovector x)
        (P.cosineComponent x) (P.sineComponent x)).mp (hBeq x hx)
    have hderiv : scalarFieldCoordinateFDeriv P.sineComponent x =
        (2 * P.cosineComponent x) • omega x := by
      exact covector_eq_smul_pull_of_pull_eq_smul
        (L x) (L x)⁻¹ _ (omegaP x) (2 * P.cosineComponent x)
        (actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
          g x choice (haccepted x hx).1)
        hphaseP
    have h := hasFDerivAt_of_coordinateFDeriv
      P.sineComponent _ x (hBdiff x hx) hderiv
    simpa only [omega, oneForm4ContinuousLinearMap_smul] using h
  · exact hx0
  · exact hbase

/-- Detector-output formulation of `couplingSq_eq_three`: the single
base-point selector and the propagated conclusion are stated directly using
`actualMetricFourthOrderCouplingSqCandidateAt`. -/
theorem detectorCouplingSqCandidate_eq_three
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hAdiff : ∀ x ∈ U, DifferentiableAt ℝ
      (actualMetricFixedFourthOrderChannelPatch g choice haccepted).cosineComponent x)
    (hBdiff : ∀ x ∈ U, DifferentiableAt ℝ
      (actualMetricFixedFourthOrderChannelPatch g choice haccepted).sineComponent x)
    (hBeq : ∀ x ∈ U,
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      sineCouplingPropagationEquation
        (pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
          (scalarFieldCoordinateFDeriv P.sineComponent x))
        (P.effectiveOneForm x) (P.reflectedScalarCovector x)
        (P.cosineComponent x) (P.sineComponent x) = 0)
    {x0 : CurvatureCoordinateSpace4} (hx0 : x0 ∈ U)
    (hbase : actualMetricFourthOrderCouplingSqCandidateAt
      g x0 choice = 3) :
    ∀ x ∈ U,
      actualMetricFourthOrderCouplingSqCandidateAt g x choice = 3 := by
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  have hbase' : P.cosineComponent x0 ^ 2 +
      P.sineComponent x0 ^ 2 = 3 := by
    rw [← couplingSqCandidate_eq_components g choice haccepted x0]
    exact hbase
  have hprop := couplingSq_eq_three g choice haccepted hUopen hUconvex
    hAdiff hBdiff hBeq hx0 hbase'
  intro x hx
  rw [couplingSqCandidate_eq_components g choice haccepted x]
  exact hprop x hx

end ActualMetricFixedPhasePatch

end RainichKaluza
