import RainichKaluza.ChartSpecificFixedChoiceKaluzaRecognition
import RainichKaluza.NormalEMDScalarEquationBridge

/-!
# Scalar-residual-free staged Kaluza converse

The original staged boundary stores a rich field realization and algebraic
entrance package together with the scalar equation.  This file splits those
logical layers without changing that API.  `FixedChoiceStagedKaluzaConverseCore`
contains every field except `scalarResidual_zero`; `withScalarResidual`
inserts either an independently supplied or subsequently derived scalar
equation.

For the positive-cosine chart the core is constructed before any scalar wave
equation is assumed.  A second layer packages the exact normal-coordinate
regularity, source, and matter-jet assumptions consumed by
`NormalEMDScalarEquationBridge`, and uses them to fill the missing scalar
field of the original boundary.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

/-- The complete staged field/entrance output, before proving the scalar
equation.  This deliberately mirrors `FixedChoiceStagedKaluzaConverseBoundary`
except for its `scalarResidual_zero` field. -/
structure FixedChoiceStagedKaluzaConverseCore
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (M : PositiveQPhaseIIIPatch4 U)
    (branch : RelativeSignScalarBranch4) where
  physical : PhaseIIIPhysicalMaxwellC1PairRealization C M branch
  coupling_eq : M.coupling = Real.sqrt 3
  phaseCircle : ∀ z ∈ U, M.c z ^ 2 + M.s z ^ 2 = 1
  phaseFirstJets : ∀ z ∈ U,
    scalarFieldCoordinateFDeriv M.c z = (-M.s z) • M.omega z ∧
      scalarFieldCoordinateFDeriv M.s z = M.c z • M.omega z
  scalarPotential_matches_metric : ∀ z ∈ U,
    HasFDerivAt physical.maxwell.scalarRepresentative
      (oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)) z
  phaseIIIExteriorClosure : M.BranchEMDExteriorClosureOn C branch
  conventionMaxwell_closed :
    IsC1ClosedTwoFormOn
      physical.maxwell.conventionNormalizedPhysicalMaxwell
      physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative U
  conventionMaxwell_matches_seed : ∀ z ∈ U, ∀ i j,
    physical.maxwell.conventionNormalizedPhysicalMaxwell z
        (coordinateDirection i) (coordinateDirection j) =
      Real.sqrt 2 *
        negativeEMDWeight M.coupling
          physical.maxwell.scalarRepresentative z *
          (M.exteriorJet z).rotatedF i j
  conventionGaugePotential :
    ∃ A : CurvatureCoordinateSpace4 →
        CurvatureCoordinateSpace4 →L[ℝ] ℝ,
      IsGaugePotentialOn A physical.maxwell.physicalMaxwell U ∧
        IsGaugePotentialOn (Real.sqrt 2 • A)
          physical.maxwell.conventionNormalizedPhysicalMaxwell U
  weightedHodgeFlux_closed :
    IsC1ClosedTwoFormOn physical.weightedHodgeFlux
      physical.weightedHodgeFluxDerivative U
  coframe_reconstructs_metric : ∀ z ∈ U,
    (actualMetricPrincipalCoframeCandidateField4 g choice z)ᵀ *
        minkowskiMetric *
        actualMetricPrincipalCoframeCandidateField4 g choice z =
      coordinateMetricMatrixField4 g z
  ricci_entrance_split : ∀ z ∈ U,
    actualMetricMaxwellResidualCandidateField4 g choice z +
        actualMetricScalarContributionCandidateField4 g choice z =
      actualMixedRicciField4 g z
  residual_is_canonical_in_selected_frame : ∀ z ∈ U,
    transportMixed
        (actualMetricPrincipalCoframeCandidateField4 g choice z)
        (actualMetricMaxwellResidualCandidateField4 g choice z)
        (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹ =
      canonicalMaxwellResidual
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z)

namespace FixedChoiceStagedKaluzaConverseCore

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}

/-- Forget only the scalar equation from an existing staged boundary. -/
def ofBoundary
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch) :
    FixedChoiceStagedKaluzaConverseCore D C M branch where
  physical := B.physical
  coupling_eq := B.coupling_eq
  phaseCircle := B.phaseCircle
  phaseFirstJets := B.phaseFirstJets
  scalarPotential_matches_metric := B.scalarPotential_matches_metric
  phaseIIIExteriorClosure := B.phaseIIIExteriorClosure
  conventionMaxwell_closed := B.conventionMaxwell_closed
  conventionMaxwell_matches_seed := B.conventionMaxwell_matches_seed
  conventionGaugePotential := B.conventionGaugePotential
  weightedHodgeFlux_closed := B.weightedHodgeFlux_closed
  coframe_reconstructs_metric := B.coframe_reconstructs_metric
  ricci_entrance_split := B.ricci_entrance_split
  residual_is_canonical_in_selected_frame :=
    B.residual_is_canonical_in_selected_frame

/-- Insert a subsequently proved scalar equation and recover the original
staged-boundary API. -/
def withScalarResidual
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (hscalarResidual : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    FixedChoiceStagedKaluzaConverseBoundary D C M branch where
  physical := K.physical
  coupling_eq := K.coupling_eq
  phaseCircle := K.phaseCircle
  phaseFirstJets := K.phaseFirstJets
  scalarPotential_matches_metric := K.scalarPotential_matches_metric
  phaseIIIExteriorClosure := K.phaseIIIExteriorClosure
  conventionMaxwell_closed := K.conventionMaxwell_closed
  conventionMaxwell_matches_seed := K.conventionMaxwell_matches_seed
  conventionGaugePotential := K.conventionGaugePotential
  weightedHodgeFlux_closed := K.weightedHodgeFlux_closed
  scalarResidual_zero := hscalarResidual
  coframe_reconstructs_metric := K.coframe_reconstructs_metric
  ricci_entrance_split := K.ricci_entrance_split
  residual_is_canonical_in_selected_frame :=
    K.residual_is_canonical_in_selected_frame

/-- Coordinate matrix of the convention-normalized physical Maxwell field
stored before the scalar equation is proved. -/
noncomputable def conventionPhysicalMaxwellMatrix4
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  fun i j ↦ K.physical.maxwell.conventionNormalizedPhysicalMaxwell z
    (coordinateDirection i) (coordinateDirection j)

/-- Curvature-normalized field
`H = exp(a phi / 2) F / sqrt 2` stored by the pre-scalar boundary. -/
noncomputable def curvatureNormalizedPhysicalMaxwellMatrix4
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  (positiveEMDWeight M.coupling
      K.physical.maxwell.scalarRepresentative z / Real.sqrt 2) •
    K.conventionPhysicalMaxwellMatrix4 z

/-! ## Construction before the scalar equation -/

/-- Positive-cosine staged construction with no scalar-equation input. -/
noncomputable def ofPositiveCosineChart
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3)
    (A : PhaseIIIAcceptedBranch C
      (D.positiveCosinePhaseIIIPatch hchart) branch)
    (hscalarBridge : ∀ z ∈ U,
      C.branchScalarOneForm branch z =
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z)) :
    FixedChoiceStagedKaluzaConverseCore D C
      (D.positiveCosinePhaseIIIPatch hchart) branch := by
  let M := D.positiveCosinePhaseIIIPatch hchart
  have hlaws := D.positiveCosinePhaseLaws hchart
  have hsmooth := D.positiveCosineContDiffOne hchart
  let P : PhaseIIIPhysicalMaxwellC1PairRealization C M branch :=
    A.toPhysicalMaxwellC1PairRealization_ofActualSmoothFields
      (actualMetricPrincipalCoframeCandidateField4 g choice)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (ActualMetricFixedPhasePatch.coordinatePhaseOneForm
        g choice D.accepted)
      (ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField
        g choice D.accepted)
      (ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField
        g choice D.accepted)
      (Real.sqrt 3) (fun z hz ↦ (hlaws z hz).1)
        (fun z hz ↦ (hlaws z hz).2) D.isOpen D.starConvex
        D.frameContDiffTwo D.magnitudeContDiffTwo D.magnitude_pos
        hsmooth.1 hsmooth.2
  refine {
    physical := P
    coupling_eq := rfl
    phaseCircle := ?_
    phaseFirstJets := ?_
    scalarPotential_matches_metric := ?_
    phaseIIIExteriorClosure :=
      (M.branchEMDExteriorClosureOn_iff_obstructionsVanishOn C branch).2
        A.maxwell
    conventionMaxwell_closed :=
      P.maxwell.conventionNormalizedPhysicalMaxwell_closed
    conventionMaxwell_matches_seed := ?_
    conventionGaugePotential :=
      P.maxwell.exists_conventionNormalizedPhysicalMaxwell_gaugePotential
    weightedHodgeFlux_closed := P.weightedHodgeFlux_closed
    coframe_reconstructs_metric := ?_
    ricci_entrance_split := ?_
    residual_is_canonical_in_selected_frame := ?_ }
  · intro z hz
    let Q := actualMetricFixedFourthOrderChannelPatch
      g choice D.accepted
    have hspec := positiveCosineHalfAngle_spec (Real.sqrt 3)
      (Q.cosineComponent z) (Q.sineComponent z)
      (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
      (hchart z hz)
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField, Q]
      using hspec.1
  · intro z hz
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using hlaws z hz
  · intro z hz
    rw [← hscalarBridge z hz]
    exact P.maxwell.scalarRepresentative_is z hz
  · intro z hz i j
    exact P.maxwell.conventionNormalizedPhysicalMaxwell_matches_seed hz i j
  · intro z hz
    exact actualMetricPrincipalCoframeCandidate_metric_of_upstream
      g z choice (D.accepted z hz).1
  · intro z _
    exact maxwellResidual_add_scalar
      (actualMixedRicciField4 g z)
      (actualMetricScalarContributionCandidateField4 g choice z)
  · intro z hz
    exact actualMetricMaxwellResidual_transport_eq_canonical_of_upstream
      g z choice (D.accepted z hz).1

/-- Detector-channel version of the pre-scalar positive-cosine boundary.
The Phase-III Maxwell equations are derived rather than assumed. -/
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
          choice.relativeMinus z) :
    FixedChoiceStagedKaluzaConverseCore D C
      (D.positiveCosinePhaseIIIPatch hchart) branch := by
  have A := D.positiveCosine_phaseIIIAcceptedBranch_of_detectorChannels
    hchart C branch hscalarPotential hscalarMatchesMetric
  apply ofPositiveCosineChart D hchart A
  intro z hz
  rw [C.branchScalarOneForm_eq_coordinateValue branch z,
    hscalarMatchesMetric z hz]

end FixedChoiceStagedKaluzaConverseCore

/-! ## Exact normal-coordinate data deriving the missing scalar equation -/

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}

/-- All pointwise hypotheses used to derive the staged metric scalar
residual from the normal-coordinate Noether/Bianchi bridge.  No regularity,
source equality, field jet, skew-symmetry, or active-branch condition is
hidden in this package. -/
structure FixedChoiceNormalEMDScalarDerivationAt
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4) where
  metricC3 : CoordinateMetricComponentsContDiffThreeAt4 g z
  metricSymmetricNear : CoordinateMetricSymmetricNear4 g z
  metricDifferentiable :
    MatrixFieldDifferentiableAt4 (coordinateMetricMatrixField4 g) z
  metricValue : coordinateMetricMatrixField4 g z = minkowskiMetric
  metricFirstJet : actualCoordinateMetricJet1Field4 g z = 0
  scalarJet : Fin 4 → OneForm4
  maxwellJet : Fin 4 → Matrix4
  hodgeJet : Fin 4 → Matrix4
  hodgeValue : Matrix4
  scalarComponentsDifferentiable : ∀ k,
    DifferentiableAt ℝ
      (fun y ↦ actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y k) z
  scalarFirstJet : ∀ r k,
    scalarFieldCoordinateFDeriv
      (fun y ↦ actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y k) z r = scalarJet r k
  maxwellComponentsDifferentiable : ∀ p q,
    DifferentiableAt ℝ
      (fun y ↦ K.curvatureNormalizedPhysicalMaxwellMatrix4 y p q) z
  maxwellFirstJet : ∀ r p q,
    scalarFieldCoordinateFDeriv
      (fun y ↦ K.curvatureNormalizedPhysicalMaxwellMatrix4 y p q) z r =
        maxwellJet r p q
  scalarJet_symmetric : ∀ i j, scalarJet i j = scalarJet j i
  maxwellValue_skew :
    (K.curvatureNormalizedPhysicalMaxwellMatrix4 z)ᵀ =
      -K.curvatureNormalizedPhysicalMaxwellMatrix4 z
  maxwellJet_skew : ∀ k, (maxwellJet k)ᵀ = -maxwellJet k
  maxwellBianchi : NormalRescaledMaxwellBianchi
    (K.curvatureNormalizedPhysicalMaxwellMatrix4 z) maxwellJet
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z) M.coupling
  hodgeValue_eq : hodgeValue = coordinateMetricHodgeTwoForm4
    minkowskiMetric (K.curvatureNormalizedPhysicalMaxwellMatrix4 z)
  hodgeJet_eq : ∀ k, hodgeJet k = coordinateMetricHodgeTwoForm4
    minkowskiMetric (maxwellJet k)
  hodgeExterior : matrixExteriorDerivative hodgeJet =
    -(M.coupling / 2) • matrixOneWedgeTwoTensor
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus z) hodgeValue
  scalarCovector_active : actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus z ≠ 0
  einsteinSourceNear : actualCoordinateEinsteinField4 g =ᶠ[nhds z]
    actualCoordinateMatterEinsteinStressCovariantField4 g
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus)
      K.curvatureNormalizedPhysicalMaxwellMatrix4
  metricResidual_eq_normal :
    actualMetricScalarEquationResidualCandidateAt4 g choice z =
      normalScalarEquationResidual scalarJet
        (K.curvatureNormalizedPhysicalMaxwellMatrix4 z) M.coupling

namespace FixedChoiceNormalEMDScalarDerivationAt

/-- Contracted Bianchi and the two normal exterior Maxwell equations imply
the normal scalar residual for the packaged staged fields. -/
theorem normalResidual_zero
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4)
    (H : FixedChoiceNormalEMDScalarDerivationAt K z) :
    normalScalarEquationResidual H.scalarJet
      (K.curvatureNormalizedPhysicalMaxwellMatrix4 z) M.coupling = 0 := by
  exact normalScalarEquationResidual_eq_zero_of_eventuallyEqEinsteinSource
    g
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus)
    K.curvatureNormalizedPhysicalMaxwellMatrix4 z
    H.metricC3 H.metricSymmetricNear H.metricDifferentiable
    H.metricValue H.metricFirstJet H.scalarJet H.maxwellJet H.hodgeJet
    H.hodgeValue M.coupling H.scalarComponentsDifferentiable
    H.scalarFirstJet H.maxwellComponentsDifferentiable H.maxwellFirstJet
    H.scalarJet_symmetric H.maxwellValue_skew H.maxwellJet_skew
    H.maxwellBianchi H.hodgeValue_eq H.hodgeJet_eq H.hodgeExterior
    H.scalarCovector_active H.einsteinSourceNear

/-- The explicit identification between the staged metric residual and the
normal residual transfers the derived vanishing back to the detector field. -/
theorem metricResidual_zero
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4)
    (H : FixedChoiceNormalEMDScalarDerivationAt K z) :
    actualMetricScalarEquationResidualCandidateAt4 g choice z = 0 := by
  rw [H.metricResidual_eq_normal]
  exact H.normalResidual_zero K z

end FixedChoiceNormalEMDScalarDerivationAt

namespace FixedChoiceStagedKaluzaConverseCore

/-- Fill the old staged boundary's scalar field from pointwise normal EMD
derivations on the whole patch. -/
noncomputable def withNormalEMDDerivedScalarResidual
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (H : ∀ z ∈ U, FixedChoiceNormalEMDScalarDerivationAt K z) :
    FixedChoiceStagedKaluzaConverseBoundary D C M branch :=
  K.withScalarResidual (fun z hz ↦ (H z hz).metricResidual_zero K z)

/-- Once the derived scalar residual is inserted, the existing geometric
recognition backend applies unchanged. -/
theorem exists_completeRecognition_of_normalEMDDerivedScalarResidual
    {x : CurvatureCoordinateSpace4}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (H : ∀ z ∈ U, FixedChoiceNormalEMDScalarDerivationAt K z)
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt
      (K.withNormalEMDDerivedScalarResidual H) x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition
      (K.withNormalEMDDerivedScalarResidual H)
      N.toNormalGaugeRepresentative) :=
  FixedChoiceStagedKaluzaConverseBoundary.exists_completeFixedChoiceKaluzaRecognition_of_weightedDivergence
    (K.withNormalEMDDerivedScalarResidual H) N

end FixedChoiceStagedKaluzaConverseCore

/-! ## End-to-end positive-cosine composition -/

/-- **Detector channels to complete recognition with a derived scalar
equation.**  This is the scalar-residual-free analogue of the earlier
chart-specific recognition theorem: Phase-III Maxwell acceptance and the
entire staged field/entrance core are constructed first; pointwise normal EMD
data then derive and insert the scalar equation before the geometric Kaluza
backend is invoked. -/
theorem exists_completeFixedChoiceKaluzaRecognition_positiveCosineChart_of_normalEMD
    {x : CurvatureCoordinateSpace4}
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
    (H : ∀ z ∈ U,
      FixedChoiceNormalEMDScalarDerivationAt
        (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
          D hchart hscalarPotential hscalarMatchesMetric) z)
    (N : FixedChoiceMinkowskiNormalGaugeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseCore.withNormalEMDDerivedScalarResidual
        (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
          D hchart hscalarPotential hscalarMatchesMetric) H) x) :
    Nonempty (CompleteFixedChoiceKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseCore.withNormalEMDDerivedScalarResidual
        (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
          D hchart hscalarPotential hscalarMatchesMetric) H)
      N.toNormalGaugeRepresentative) :=
  FixedChoiceStagedKaluzaConverseCore.exists_completeRecognition_of_normalEMDDerivedScalarResidual
    (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric) H N

end RainichKaluza
