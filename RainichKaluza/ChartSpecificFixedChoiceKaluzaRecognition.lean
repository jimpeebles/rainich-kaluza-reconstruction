import RainichKaluza.GeometricFixedChoiceKaluzaRecognition
import RainichKaluza.PhaseIIIChannelAcceptanceBridge

/-!
# Chart-specific fixed-choice Kaluza recognition

This module closes both chart-specific Phase-III acceptance seams in the
staged fixed-choice converse.  The complete detector channel pair is promoted
to the two exterior EMD equations by the transported-channel bridge, so
Phase-III Maxwell acceptance is no longer an independent hypothesis on either
half-angle chart.

The final theorem then composes the staged boundary with the geometric
normal/radial-gauge recognition theorem.  The genuinely geometric inputs
which are not yet constructed by the detector remain visible: integration of
the selected scalar branch, its identification with the literal metric
scalar covector, vanishing of the metric scalar residual, and one compatible
`C²` Minkowski-normal/radial-gauge representative carrying the Einstein and
weighted-divergence equations.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

namespace ActualMetricFixedChoicePhasePatchData

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}

/-- **Detector channels imply Phase-III acceptance on the positive-cosine
chart.**  The only remaining scalar-side inputs are existence of a scalar
potential and identification of the chosen curvature branch with the
literal actual-metric scalar covector. -/
theorem positiveCosine_phaseIIIAcceptedBranch_of_detectorChannels
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z) :
    PhaseIIIAcceptedBranch C
      (D.positiveCosinePhaseIIIPatch hchart) branch := by
  let M := D.positiveCosinePhaseIIIPatch hchart
  refine ⟨hscalarPotential, ?_⟩
  apply (M.branchEMDExteriorClosureOn_iff_obstructionsVanishOn
    C branch).mp
  intro z hz
  have hKL : (M.L z)⁻¹ * M.L z = 1 := by
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using
        actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
          g z choice (D.accepted z hz).1
  have hLK : M.L z * (M.L z)⁻¹ = 1 := by
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using
        actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
          g z choice (D.accepted z hz).1
  have hunit : M.c z ^ 2 + M.s z ^ 2 = 1 := by
    let P := actualMetricFixedFourthOrderChannelPatch
      g choice D.accepted
    have hspec := positiveCosineHalfAngle_spec (Real.sqrt 3)
      (P.cosineComponent z) (P.sineComponent z)
      (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
      (hchart z hz)
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField, P]
      using hspec.1
  have hchannels := D.positiveCosine_transportedChannels_eq_physical
    hchart C branch hscalarMatchesMetric z hz
  exact emdExteriorClosure_of_transportedSeedChannels_eq_physical
    (M.L z) (M.L z)⁻¹ (M.dL z) (M.q z) (M.dq z)
      (C.branchScalarOneFormValue branch z) (M.omega z)
      M.coupling (M.c z) (M.s z) (M.dc z) (M.ds z)
      hKL hLK hunit (M.dc_eq z hz) (M.ds_eq z hz) hchannels

/-- **Detector channels imply Phase-III acceptance on the positive-sine
chart.**  This is the complementary-chart counterpart, obtained directly
from the common transported-channel bridge. -/
theorem positiveSine_phaseIIIAcceptedBranch_of_detectorChannels
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z) :
    PhaseIIIAcceptedBranch C
      (D.positiveSinePhaseIIIPatch hchart) branch :=
  D.positiveSine_phaseIIIAcceptedBranch hchart C branch
    hscalarMatchesMetric hscalarPotential

end ActualMetricFixedChoicePhasePatchData

namespace FixedChoiceStagedKaluzaConverseBoundary

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- Staged boundary for the positive-cosine chart, with full Phase-III
Maxwell acceptance derived from the persistent detector channels. -/
noncomputable def ofPositiveCosineChartDetectorChannels
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hmetricScalarEquation : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    FixedChoiceStagedKaluzaConverseBoundary D C
      (D.positiveCosinePhaseIIIPatch hchart) branch := by
  have haccepted :=
    D.positiveCosine_phaseIIIAcceptedBranch_of_detectorChannels
      hchart C branch hscalarPotential hscalarMatchesMetric
  apply ofPositiveCosineChart D hchart haccepted
  · intro z hz
    rw [C.branchScalarOneForm_eq_coordinateValue branch z,
      hscalarMatchesMetric z hz]
  · exact hmetricScalarEquation

/-- Staged boundary for the positive-sine chart, with full Phase-III Maxwell
acceptance derived from the persistent detector channels. -/
noncomputable def ofPositiveSineChartDetectorChannels
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hmetricScalarEquation : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    FixedChoiceStagedKaluzaConverseBoundary D C
      (D.positiveSinePhaseIIIPatch hchart) branch := by
  have haccepted :=
    D.positiveSine_phaseIIIAcceptedBranch_of_detectorChannels
      hchart C branch hscalarPotential hscalarMatchesMetric
  apply ofPositiveSineChart D hchart haccepted
  · intro z hz
    rw [C.branchScalarOneForm_eq_coordinateValue branch z,
      hscalarMatchesMetric z hz]
  · exact hmetricScalarEquation

end FixedChoiceStagedKaluzaConverseBoundary

/-! ## End-to-end chart-specific recognition -/

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 x : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Positive-cosine fixed-choice Kaluza recognition.**  A persistent
accepted detector choice, its complementary phase equation, and the complete
stored channel pair now feed all the way through Phase III and the staged
converse.  Supplying the four explicit geometric remainder inputs yields a
circle-invariant five-dimensional Kaluza germ whose base metric germ is the
given metric and which is intrinsically Ricci-flat in every nonlinear chart.

The four remainder inputs are:

1. integration of the selected scalar branch;
2. equality of that branch covector with the detector's actual-metric
   covector;
3. the metric scalar equation on the patch;
4. a compatible `C²` Minkowski-normal/radial-gauge representative carrying
   the normal Einstein equation and geometric weighted-Maxwell divergence.
-/
theorem exists_completeFixedChoiceKaluzaRecognition_positiveCosineChart
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ -Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hmetricScalarEquation : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0)
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation) x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation)
      N.toNormalGaugeRepresentative) :=
  FixedChoiceStagedKaluzaConverseBoundary.exists_completeFixedChoiceKaluzaRecognition_of_weightedDivergence
    (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveCosineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric hmetricScalarEquation) N

/-- **Exterior-Hodge form of positive-cosine recognition.**  This removes
the weighted-divergence statement from the hypotheses: the physical Maxwell
input is the detector-produced exterior equation
`d(*F) = -sqrt(3) dphi wedge (*F)` for the literal curvature jet of the
chosen `C²` gauge representative.  The component bridge derives the mixed
Kaluza Ricci equations internally. -/
theorem exists_completeFixedChoiceKaluzaRecognition_positiveCosineChart_of_hodgeExterior
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ -Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hmetricScalarEquation : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0)
    (N : FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation) x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation)
      N.toDivergenceRepresentative.toNormalGaugeRepresentative) :=
  FixedChoiceStagedKaluzaConverseBoundary.exists_completeFixedChoiceKaluzaRecognition_of_hodgeExterior
    (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveCosineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric hmetricScalarEquation) N

/-! ### Complementary positive-sine chart -/

/-- **Positive-sine fixed-choice Kaluza recognition.**  This is the
weighted-divergence endpoint on the complementary half-angle chart. -/
theorem exists_completeFixedChoiceKaluzaRecognition_positiveSineChart
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hmetricScalarEquation : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0)
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveSineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation) x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveSineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation)
      N.toNormalGaugeRepresentative) :=
  FixedChoiceStagedKaluzaConverseBoundary.exists_completeFixedChoiceKaluzaRecognition_of_weightedDivergence
    (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveSineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric hmetricScalarEquation) N

/-- **Exterior-Hodge form of positive-sine recognition.**  The detector's
exterior Hodge equation is converted internally to the weighted-divergence
input and then to the complete Kaluza recognition package. -/
theorem exists_completeFixedChoiceKaluzaRecognition_positiveSineChart_of_hodgeExterior
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hmetricScalarEquation : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0)
    (N : FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveSineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation) x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveSineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric
          hmetricScalarEquation)
      N.toDivergenceRepresentative.toNormalGaugeRepresentative) :=
  FixedChoiceStagedKaluzaConverseBoundary.exists_completeFixedChoiceKaluzaRecognition_of_hodgeExterior
    (FixedChoiceStagedKaluzaConverseBoundary.ofPositiveSineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric hmetricScalarEquation) N

end RainichKaluza
