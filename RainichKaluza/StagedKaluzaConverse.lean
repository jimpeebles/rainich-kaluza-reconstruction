import RainichKaluza.ActualMetricHalfAngleSplice
import RainichKaluza.PhaseIIITransportedSeedCalculus

/-!
# Fixed-choice staged Kaluza converse boundary

This file assembles the strongest currently justified fixed-coordinate
converse package without treating a single detector quotient as if it implied
the two full Maxwell seed channels.

One literal actual-metric choice is assumed accepted on an open convex patch.
The complementary `dB` equation and one normalized base value propagate the
detector pair to the radius-`sqrt 3` circle.  Either explicit half-angle chart
then supplies the actual coordinate first jets used to build a
`PositiveQPhaseIIIPatch4` with coupling `sqrt 3`.

The complete Phase-III obstruction predicate remains an explicit input.  From
that input and ordinary smoothness of the selected frame and magnitude, the
existing seed-realization calculus constructs both the closed physical
Maxwell field and the closed weighted Hodge flux.  The convention-normalized
Maxwell field and its gauge potential are retained in the output.

The scalar equation is also deliberately retained as the explicit
metric-constructed residual `div_g(v) + 2 q A`.  This module does not claim
that the algebraic entrance, or the accepted quotient alone, proves either
the full seed-channel predicate or that scalar residual.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

/-! ## The retained metric scalar residual -/

/-- Coordinate divergence of the metric-constructed scalar covector.  The
formula is `g^{mu nu} (partial_mu v_nu - Gamma^rho_{mu nu} v_rho)` using the
actual metric value and first jet. -/
noncomputable def actualMetricScalarDivergenceCandidateAt4
    (g : CurvatureCoordinateSpace4 ->
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  let GInv := (coordinateMetricMatrixField4 g z)⁻¹
  let dg := actualCoordinateMetricJet1Field4 g z
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  ∑ mu, ∑ nu, GInv mu nu *
    (scalarFieldCoordinateFDeriv (fun y => v y nu) z mu -
      ∑ rho, coordinateChristoffel GInv dg rho mu nu * v z rho)

/-- The staged scalar-equation residual `div_g(v) + 2 q A`, entirely in
terms of the actual metric and the fixed detector choice.  Here `q` is the
positive reconstructed Maxwell magnitude and `A` is the detector's
double-angle cosine coupling. -/
noncomputable def actualMetricScalarEquationResidualCandidateAt4
    (g : CurvatureCoordinateSpace4 ->
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g)
  let v := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  actualMetricScalarDivergenceCandidateAt4 g choice z +
    2 * q z * curvatureSeedCosineField L q v choice.channel.1 z

/-! ## Persistent fixed-choice input -/

/-- Common hypotheses for either explicit half-angle chart.  Regularity of
the selected frame and magnitude is stored here because it is exactly what
the transported-seed field realization consumes. -/
structure ActualMetricFixedChoicePhasePatchData
    (U : Set CurvatureCoordinateSpace4)
    (g : CurvatureCoordinateSpace4 ->
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (x0 : CurvatureCoordinateSpace4) where
  isOpen : IsOpen U
  convex : Convex ℝ U
  starConvex : StarConvex ℝ 0 U
  base_mem : x0 ∈ U
  accepted : ∀ x ∈ U,
    IsActualMetricFourthOrderDetectorCandidateAt g x choice
  cosineContDiffOne : ContDiffOn ℝ 1
    (actualMetricFixedFourthOrderChannelPatch
      g choice accepted).cosineComponent U
  sineContDiffOne : ContDiffOn ℝ 1
    (actualMetricFixedFourthOrderChannelPatch
      g choice accepted).sineComponent U
  sinePhaseEquation : ∀ x ∈ U,
    let P := actualMetricFixedFourthOrderChannelPatch g choice accepted
    sineCouplingPropagationEquation
      (pullCovectorToPrincipalFrame
        (actualMetricPrincipalCoframeCandidateField4 g choice x)⁻¹
        (scalarFieldCoordinateFDeriv P.sineComponent x))
      (P.effectiveOneForm x) (P.reflectedScalarCovector x)
      (P.cosineComponent x) (P.sineComponent x) = 0
  baseNormalized : actualMetricFourthOrderCouplingSqCandidateAt
    g x0 choice = 3
  frameContDiffTwo : MatrixFieldContDiffOn 2 U
    (actualMetricPrincipalCoframeCandidateField4 g choice)
  magnitudeContDiffTwo : ContDiffOn ℝ 2
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)) U

namespace ActualMetricFixedChoicePhasePatchData

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 ->
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}

/-- The propagated detector circle in the form used by both half-angle
charts. -/
theorem couplingCircle
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0) :
    ∀ x ∈ U,
      let P := actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted
      P.cosineComponent x ^ 2 + P.sineComponent x ^ 2 =
        (Real.sqrt 3) ^ 2 :=
  ActualMetricFixedPhasePatch.couplingCircle_eq_sqrtThree_of_C1
    g choice D.accepted D.isOpen D.convex D.cosineContDiffOne
      D.sineContDiffOne D.sinePhaseEquation D.base_mem D.baseNormalized

/-- The selected positive magnitude is strictly positive everywhere on the
accepted patch. -/
theorem magnitude_pos
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0) :
    ∀ z ∈ U,
      0 < positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z := by
  intro z hz
  exact IsActualMetricUpstreamEntranceAt4.qPos g z choice
    (D.accepted z hz).1

/-- The accepted coframe identity upgrades the stored `C^2` coframe to
entrywise `C^2` regularity of the actual coordinate metric matrix.  This is
coordinate-metric regularity only; it does not assert that the present
coordinates are normal at any chosen point. -/
theorem coordinateMetricContDiffTwo
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0) :
    MatrixFieldContDiffOn 2 U (coordinateMetricMatrixField4 g) := by
  have hproduct : MatrixFieldContDiffOn 2 U (fun z =>
      (actualMetricPrincipalCoframeCandidateField4 g choice z)ᵀ *
        minkowskiMetric *
        actualMetricPrincipalCoframeCandidateField4 g choice z) :=
    ((D.frameContDiffTwo.transpose.mul
      (matrixFieldContDiffOn_const minkowskiMetric)).mul
        D.frameContDiffTwo)
  intro i j
  exact (hproduct i j).congr fun z hz => by
    exact congrArg (fun M : Matrix4 => M i j)
      (actualMetricPrincipalCoframeCandidate_metric_of_upstream
        g z choice (D.accepted z hz).1).symm

/-! ### Positive-cosine chart -/

/-- Coordinate phase laws for the positive-cosine half-angle chart. -/
theorem positiveCosinePhaseLaws
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3) :
    ∀ x ∈ U,
      scalarFieldCoordinateFDeriv
          (ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField
            g choice D.accepted) x =
        (-ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField
          g choice D.accepted x) •
          ActualMetricFixedPhasePatch.coordinatePhaseOneForm
            g choice D.accepted x ∧
      scalarFieldCoordinateFDeriv
          (ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField
            g choice D.accepted) x =
        ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField
          g choice D.accepted x •
          ActualMetricFixedPhasePatch.coordinatePhaseOneForm
            g choice D.accepted x :=
  ActualMetricFixedPhasePatch.positiveCosineHalfAngleFields_coordinateFDerivatives_eq_phaseLaws
      g choice D.accepted D.isOpen D.convex D.cosineContDiffOne
        D.sineContDiffOne D.sinePhaseEquation D.base_mem
        D.baseNormalized hchart

/-- The positive-cosine half-angle fields are `C^1` on their strict chart. -/
theorem positiveCosineContDiffOne
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3) :
    ContDiffOn ℝ 1
        (ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField
          g choice D.accepted) U ∧
      ContDiffOn ℝ 1
        (ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField
          g choice D.accepted) U := by
  let P := actualMetricFixedFourthOrderChannelPatch
    g choice D.accepted
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h := contDiffOn_positiveCosineHalfAngleLift
    (Real.sqrt 3) hsqrt D.cosineContDiffOne D.sineContDiffOne
      D.couplingCircle hchart
  simpa only [ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField,
    ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField, P] using h

/-- The actual-metric positive-cosine half-angle data as the concrete
Phase-III patch.  All derivative arrays are genuine coordinate Fréchet
derivatives by construction. -/
noncomputable def positiveCosinePhaseIIIPatch
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3) :
    PositiveQPhaseIIIPatch4 U :=
  let laws := D.positiveCosinePhaseLaws hchart
  PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g))
    (ActualMetricFixedPhasePatch.coordinatePhaseOneForm
      g choice D.accepted)
    (ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField
      g choice D.accepted)
    (ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField
      g choice D.accepted)
    (Real.sqrt 3) (fun z hz => (laws z hz).1)
      (fun z hz => (laws z hz).2)

/-! ### Positive-sine chart -/

/-- Coordinate phase laws for the complementary positive-sine chart. -/
theorem positiveSinePhaseLaws
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3) :
    ∀ x ∈ U,
      scalarFieldCoordinateFDeriv
          (ActualMetricFixedPhasePatch.positiveSineHalfAngleCField
            g choice D.accepted) x =
        (-ActualMetricFixedPhasePatch.positiveSineHalfAngleSField
          g choice D.accepted x) •
          ActualMetricFixedPhasePatch.coordinatePhaseOneForm
            g choice D.accepted x ∧
      scalarFieldCoordinateFDeriv
          (ActualMetricFixedPhasePatch.positiveSineHalfAngleSField
            g choice D.accepted) x =
        ActualMetricFixedPhasePatch.positiveSineHalfAngleCField
          g choice D.accepted x •
          ActualMetricFixedPhasePatch.coordinatePhaseOneForm
            g choice D.accepted x :=
  ActualMetricFixedPhasePatch.positiveSineHalfAngleFields_coordinateFDerivatives_eq_phaseLaws
      g choice D.accepted D.isOpen D.convex D.cosineContDiffOne
        D.sineContDiffOne D.sinePhaseEquation D.base_mem
        D.baseNormalized hchart

/-- The positive-sine half-angle fields are `C^1` on their strict chart. -/
theorem positiveSineContDiffOne
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3) :
    ContDiffOn ℝ 1
        (ActualMetricFixedPhasePatch.positiveSineHalfAngleCField
          g choice D.accepted) U ∧
      ContDiffOn ℝ 1
        (ActualMetricFixedPhasePatch.positiveSineHalfAngleSField
          g choice D.accepted) U := by
  let P := actualMetricFixedFourthOrderChannelPatch
    g choice D.accepted
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h := contDiffOn_positiveSineHalfAngleLift
    (Real.sqrt 3) hsqrt D.cosineContDiffOne D.sineContDiffOne
      D.couplingCircle hchart
  simpa only [ActualMetricFixedPhasePatch.positiveSineHalfAngleCField,
    ActualMetricFixedPhasePatch.positiveSineHalfAngleSField, P] using h

/-- The actual-metric positive-sine half-angle data as the concrete
Phase-III patch. -/
noncomputable def positiveSinePhaseIIIPatch
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3) :
    PositiveQPhaseIIIPatch4 U :=
  let laws := D.positiveSinePhaseLaws hchart
  PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g))
    (ActualMetricFixedPhasePatch.coordinatePhaseOneForm
      g choice D.accepted)
    (ActualMetricFixedPhasePatch.positiveSineHalfAngleCField
      g choice D.accepted)
    (ActualMetricFixedPhasePatch.positiveSineHalfAngleSField
      g choice D.accepted)
    (Real.sqrt 3) (fun z hz => (laws z hz).1)
      (fun z hz => (laws z hz).2)

end ActualMetricFixedChoicePhasePatchData

/-! ## Honest staged output -/

/-- The assembled fixed-choice boundary.  It reaches actual half-angle phase
fields, both exterior Maxwell equations at field level, the convention
`sqrt 2` normalization and gauge potential, and the exact algebraic metric
entrance identities.  The full Phase-III channels and scalar residual remain
visible proof fields rather than hidden consequences. -/
structure FixedChoiceStagedKaluzaConverseBoundary
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 ->
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
    ∃ A : CurvatureCoordinateSpace4 ->
        CurvatureCoordinateSpace4 →L[ℝ] ℝ,
      IsGaugePotentialOn A physical.maxwell.physicalMaxwell U ∧
        IsGaugePotentialOn (Real.sqrt 2 • A)
          physical.maxwell.conventionNormalizedPhysicalMaxwell U
  weightedHodgeFlux_closed :
    IsC1ClosedTwoFormOn physical.weightedHodgeFlux
      physical.weightedHodgeFluxDerivative U
  scalarResidual_zero : ∀ z ∈ U,
    actualMetricScalarEquationResidualCandidateAt4 g choice z = 0
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

namespace FixedChoiceStagedKaluzaConverseBoundary

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 ->
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Positive-cosine staged converse assembly.**  The full two-channel
Phase-III acceptance and the scalar residual are explicit hypotheses.  Every
other field and entrance component in the result is constructed or proved. -/
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
            choice.relativeMinus z))
    (hscalarResidual : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    FixedChoiceStagedKaluzaConverseBoundary D C
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
      (Real.sqrt 3) (fun z hz => (hlaws z hz).1)
        (fun z hz => (hlaws z hz).2) D.isOpen D.starConvex
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
    scalarResidual_zero := hscalarResidual
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

/-- **Positive-sine staged converse assembly.**  This is the complementary
chart version of `ofPositiveCosineChart`. -/
noncomputable def ofPositiveSineChart
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (A : PhaseIIIAcceptedBranch C
      (D.positiveSinePhaseIIIPatch hchart) branch)
    (hscalarBridge : ∀ z ∈ U,
      C.branchScalarOneForm branch z =
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z))
    (hscalarResidual : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    FixedChoiceStagedKaluzaConverseBoundary D C
      (D.positiveSinePhaseIIIPatch hchart) branch := by
  let M := D.positiveSinePhaseIIIPatch hchart
  have hlaws := D.positiveSinePhaseLaws hchart
  have hsmooth := D.positiveSineContDiffOne hchart
  let P : PhaseIIIPhysicalMaxwellC1PairRealization C M branch :=
    A.toPhysicalMaxwellC1PairRealization_ofActualSmoothFields
      (actualMetricPrincipalCoframeCandidateField4 g choice)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (ActualMetricFixedPhasePatch.coordinatePhaseOneForm
        g choice D.accepted)
      (ActualMetricFixedPhasePatch.positiveSineHalfAngleCField
        g choice D.accepted)
      (ActualMetricFixedPhasePatch.positiveSineHalfAngleSField
        g choice D.accepted)
      (Real.sqrt 3) (fun z hz => (hlaws z hz).1)
        (fun z hz => (hlaws z hz).2) D.isOpen D.starConvex
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
    scalarResidual_zero := hscalarResidual
    coframe_reconstructs_metric := ?_
    ricci_entrance_split := ?_
    residual_is_canonical_in_selected_frame := ?_ }
  · intro z hz
    let Q := actualMetricFixedFourthOrderChannelPatch
      g choice D.accepted
    have hspec := positiveSineHalfAngle_spec (Real.sqrt 3)
      (Q.cosineComponent z) (Q.sineComponent z)
      (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
      (hchart z hz)
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveSinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      ActualMetricFixedPhasePatch.positiveSineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveSineHalfAngleSField, Q]
      using hspec.1
  · intro z hz
    simpa only [M,
      ActualMetricFixedChoicePhasePatchData.positiveSinePhaseIIIPatch,
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

/-- Proposition-level positive-cosine staged converse theorem. -/
theorem nonempty_ofPositiveCosineChart
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
            choice.relativeMinus z))
    (hscalarResidual : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    Nonempty (FixedChoiceStagedKaluzaConverseBoundary D C
      (D.positiveCosinePhaseIIIPatch hchart) branch) :=
  ⟨ofPositiveCosineChart D hchart A hscalarBridge hscalarResidual⟩

/-- Proposition-level positive-sine staged converse theorem. -/
theorem nonempty_ofPositiveSineChart
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (A : PhaseIIIAcceptedBranch C
      (D.positiveSinePhaseIIIPatch hchart) branch)
    (hscalarBridge : ∀ z ∈ U,
      C.branchScalarOneForm branch z =
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z))
    (hscalarResidual : ∀ z ∈ U,
      actualMetricScalarEquationResidualCandidateAt4 g choice z = 0) :
    Nonempty (FixedChoiceStagedKaluzaConverseBoundary D C
      (D.positiveSinePhaseIIIPatch hchart) branch) :=
  ⟨ofPositiveSineChart D hchart A hscalarBridge hscalarResidual⟩

end FixedChoiceStagedKaluzaConverseBoundary

end RainichKaluza
