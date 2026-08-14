import RainichKaluza.ActualMetricCouplingPhasePatch
import RainichKaluza.LocalHalfAngleLift

/-!
# Actual-metric half-angle splice

This file joins the literal actual-metric fixed-choice phase propagation to
the explicit local half-angle charts.  One accepted raw detector choice is
held fixed on an open convex patch.  The existing fourth-order equation and
the proposed principal-frame `dB` equation propagate the detector
normalization from one base point; the inverse-coframe bridge then supplies
the genuine coordinate phase derivatives used by `LocalHalfAngleLift`.

The result is deliberately local in the half-angle chart.  The strict
conditions `A ≠ -sqrt 3` and `A ≠ sqrt 3` are the two standard chart cuts;
they are also exactly what makes the relevant square root smoothly
differentiable.
-/

namespace RainichKaluza

open scoped Matrix Topology

namespace ActualMetricFixedPhasePatch

variable {U : Set CurvatureCoordinateSpace4}

/-! ## Explicit `sqrt 3` half-angle fields -/

/-- Positive-cosine half-angle cosine reconstructed from the literal
actual-metric detector component. -/
noncomputable def positiveCosineHalfAngleCField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    CurvatureCoordinateSpace4 → ℝ :=
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  fun x => positiveCosineHalfAngleC (Real.sqrt 3) (P.cosineComponent x)

/-- Signed positive-cosine-chart half-angle sine reconstructed from the two
literal detector components. -/
noncomputable def positiveCosineHalfAngleSField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    CurvatureCoordinateSpace4 → ℝ :=
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  fun x => positiveCosineHalfAngleS (Real.sqrt 3)
    (P.cosineComponent x) (P.sineComponent x)

/-- Signed positive-sine-chart half-angle cosine reconstructed from the two
literal detector components. -/
noncomputable def positiveSineHalfAngleCField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    CurvatureCoordinateSpace4 → ℝ :=
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  fun x => positiveSineHalfAngleC (Real.sqrt 3)
    (P.cosineComponent x) (P.sineComponent x)

/-- Positive-sine half-angle sine reconstructed from the literal
actual-metric detector component. -/
noncomputable def positiveSineHalfAngleSField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice) :
    CurvatureCoordinateSpace4 → ℝ :=
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  fun x => positiveSineHalfAngleS (Real.sqrt 3) (P.cosineComponent x)

/-! ## Normalized coupling circle -/

/-- A `C^1` actual-metric fixed choice satisfying the complementary
principal-frame phase equation lies on the radius-`sqrt 3` coupling circle
throughout the patch, once one literal detector output is normalized to
three. -/
theorem couplingCircle_eq_sqrtThree_of_C1
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hA : ContDiffOn ℝ 1
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).cosineComponent U)
    (hB : ContDiffOn ℝ 1
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).sineComponent U)
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
      let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
      P.cosineComponent x ^ 2 + P.sineComponent x ^ 2 =
        (Real.sqrt 3) ^ 2 := by
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  have hAdiff : ∀ x ∈ U, DifferentiableAt ℝ P.cosineComponent x :=
    fun x hx => (hA.differentiableOn_one x hx).differentiableAt
      (hUopen.mem_nhds hx)
  have hBdiff : ∀ x ∈ U, DifferentiableAt ℝ P.sineComponent x :=
    fun x hx => (hB.differentiableOn_one x hx).differentiableAt
      (hUopen.mem_nhds hx)
  have hbase' : P.cosineComponent x0 ^ 2 +
      P.sineComponent x0 ^ 2 = 3 := by
    rw [← couplingSqCandidate_eq_components g choice haccepted x0]
    exact hbase
  have hthree := couplingSq_eq_three g choice haccepted
    hUopen hUconvex hAdiff hBdiff hBeq hx0 hbase'
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  intro x hx
  exact (hthree x hx).trans hsqrt.symm

/-! ## Coordinate first-jet phase laws -/

/-- On the strict positive-cosine chart, the explicit `sqrt 3` half-angle
fields have the genuine coordinate phase derivatives. -/
theorem positiveCosineHalfAngleFields_coordinateFDerivatives_eq_phaseLaws
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hA : ContDiffOn ℝ 1
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).cosineComponent U)
    (hB : ContDiffOn ℝ 1
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).sineComponent U)
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
      g x0 choice = 3)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).cosineComponent x ≠ -Real.sqrt 3) :
    ∀ x ∈ U,
      scalarFieldCoordinateFDeriv
          (positiveCosineHalfAngleCField g choice haccepted) x =
        (-positiveCosineHalfAngleSField g choice haccepted x) •
          coordinatePhaseOneForm g choice haccepted x /\
      scalarFieldCoordinateFDeriv
          (positiveCosineHalfAngleSField g choice haccepted) x =
        positiveCosineHalfAngleCField g choice haccepted x •
          coordinatePhaseOneForm g choice haccepted x := by
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  have hcircle := couplingCircle_eq_sqrtThree_of_C1
    g choice haccepted hUopen hUconvex hA hB hBeq hx0 hbase
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  intro x hx
  have hphase := coordinateFDerivatives_eq_phaseLaws
    g choice haccepted hx (hBeq x hx)
  have hlift :=
    RainichKaluza.positiveCosineHalfAngleCoordinateFDerivatives_eq_phaseLaws
      hUopen x hx (Real.sqrt 3) P.cosineComponent P.sineComponent
      (coordinatePhaseOneForm g choice haccepted x) hsqrt hA hB
      hcircle hchart hphase.1 hphase.2
  simpa only [positiveCosineHalfAngleCField,
    positiveCosineHalfAngleSField, P] using hlift

/-- On the strict positive-sine chart, the complementary explicit `sqrt 3`
half-angle fields have the genuine coordinate phase derivatives. -/
theorem positiveSineHalfAngleFields_coordinateFDerivatives_eq_phaseLaws
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (haccepted : ∀ x ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g x choice)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hA : ContDiffOn ℝ 1
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).cosineComponent U)
    (hB : ContDiffOn ℝ 1
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).sineComponent U)
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
      g x0 choice = 3)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice haccepted).cosineComponent x ≠ Real.sqrt 3) :
    ∀ x ∈ U,
      scalarFieldCoordinateFDeriv
          (positiveSineHalfAngleCField g choice haccepted) x =
        (-positiveSineHalfAngleSField g choice haccepted x) •
          coordinatePhaseOneForm g choice haccepted x /\
      scalarFieldCoordinateFDeriv
          (positiveSineHalfAngleSField g choice haccepted) x =
        positiveSineHalfAngleCField g choice haccepted x •
          coordinatePhaseOneForm g choice haccepted x := by
  let P := actualMetricFixedFourthOrderChannelPatch g choice haccepted
  have hcircle := couplingCircle_eq_sqrtThree_of_C1
    g choice haccepted hUopen hUconvex hA hB hBeq hx0 hbase
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  intro x hx
  have hphase := coordinateFDerivatives_eq_phaseLaws
    g choice haccepted hx (hBeq x hx)
  have hlift :=
    RainichKaluza.positiveSineHalfAngleCoordinateFDerivatives_eq_phaseLaws
      hUopen x hx (Real.sqrt 3) P.cosineComponent P.sineComponent
      (coordinatePhaseOneForm g choice haccepted x) hsqrt hA hB
      hcircle hchart hphase.1 hphase.2
  simpa only [positiveSineHalfAngleCField,
    positiveSineHalfAngleSField, P] using hlift

end ActualMetricFixedPhasePatch

end RainichKaluza
