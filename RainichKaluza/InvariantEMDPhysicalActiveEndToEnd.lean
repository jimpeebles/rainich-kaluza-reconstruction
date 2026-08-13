import RainichKaluza.PhysicalComplexionInvariant
import RainichKaluza.InvariantEMDRegularityEndToEnd

/-!
# End-to-end invariant EMD necessity from a physical active locus

The regularity-closed theorem previously asked its selector callback for two
facts about the returned branch: selected-residual `C²` regularity and the
detector's active-wedge predicate.  The latter is not genuinely
choice-dependent.  This module removes it from the callback.

One genericity premise is stated at the base point entirely in terms of the
physical inverse metric, genuine Maxwell/Hodge pair, physical Maxwell stress,
reconstructed positive magnitude, and physical scalar covector.  After the
finite upstream selector fixes a branch and a scalar sign, the double-angle
complexion theorem proves that this physical premise is exactly the selected
detector active gate.  The callback therefore supplies only conventional
`C²` regularity of the selected residual.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- Selected open regular branch before physical genericity has been
transported to the detector active gate.  This is intentionally the existing
selected detector patch with its `activeWedge` field omitted. -/
structure SelectedActualMetricEMDPreActivePatch4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (U : Set CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (z : CurvatureCoordinateSpace4) where
  V : Set CurvatureCoordinateSpace4
  choice : ActualMetricDetectorChoice4
  isOpen : IsOpen V
  mem : z ∈ V
  subset : V ⊆ U
  scalarOrbit :
    (∀ y ∈ V,
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = W.scalarOneForm y) ∨
    (∀ y ∈ V,
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = -W.scalarOneForm y)
  upstream : ∀ y ∈ V,
    IsActualMetricUpstreamEntranceAt4 g y choice
  coframeC2 : MatrixFieldContDiffOn 2 V
    (actualMetricPrincipalCoframeCandidateField4 g choice)
  magnitudeC2 : ContDiffOn ℝ 2
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g)) V

/-- Forget the pre-active wrapper and attach a proved active gate. -/
def SelectedActualMetricEMDPreActivePatch4.withActive
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U}
    {z : CurvatureCoordinateSpace4}
    (S : SelectedActualMetricEMDPreActivePatch4 g U W z)
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z S.choice) :
    SelectedActualMetricEMDDetectorPatch4 g U W z where
  V := S.V
  choice := S.choice
  isOpen := S.isOpen
  mem := S.mem
  subset := S.subset
  scalarOrbit := S.scalarOrbit
  upstream := S.upstream
  coframeC2 := S.coframeC2
  magnitudeC2 := S.magnitudeC2
  activeWedge := hactive

/-- Intersect the selector's fixed scalar-sign and upstream germs, then
derive the selected coframe and magnitude regularity from conventional
metric, `q²`, and selected-residual `C²` data.  No active premise is used. -/
theorem exists_selectedActualMetricEMDPreActivePatch4_of_eventually_regularData
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hscalar :
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z] W.scalarOneForm) ∨
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z]
        fun y ↦ -W.scalarOneForm y))
    (hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice)
    (hgC2 : ContDiffOn ℝ 2 g U)
    (hqSqC2 : ContDiffOn ℝ 2
      (actualRicciReconstructedQSqField4 g) U)
    (hresidualC2 : MatrixFieldContDiffOn 2 U
      (actualMetricMaxwellResidualCandidateField4 g choice)) :
    Nonempty (SelectedActualMetricEMDPreActivePatch4 g U W z) := by
  rcases hscalar with hplus | hminus
  · have hcommon : ∀ᶠ y in nhds z,
        y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice ∧
          oneForm4ContinuousLinearMap
              (actualMetricScalarOneFormCandidateField4 g
                choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                choice.relativeMinus y) = W.scalarOneForm y := by
      filter_upwards [hupstream, hplus] with y hy hscalarY
      exact ⟨hy.1, hy.2, hscalarY⟩
    have hmem : {y | y ∈ U ∧
        IsActualMetricUpstreamEntranceAt4 g y choice ∧
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = W.scalarOneForm y} ∈ nhds z :=
      hcommon
    obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hmem
    have hVU : V ⊆ U := fun y hy ↦ (hVsub hy).1
    have hregular := actualMetricDetectorRegularity_of_residual
      g choice (hgC2.mono hVU)
      (fun r c ↦ (hresidualC2 r c).mono hVU)
      (hqSqC2.mono hVU) (fun y hy ↦ (hVsub hy).2.1)
    exact ⟨{
      V := V
      choice := choice
      isOpen := hVopen
      mem := hzV
      subset := hVU
      scalarOrbit := Or.inl (fun y hy ↦ (hVsub hy).2.2)
      upstream := fun y hy ↦ (hVsub hy).2.1
      coframeC2 := hregular.1
      magnitudeC2 := hregular.2 }⟩
  · have hcommon : ∀ᶠ y in nhds z,
        y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice ∧
          oneForm4ContinuousLinearMap
              (actualMetricScalarOneFormCandidateField4 g
                choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                choice.relativeMinus y) = -W.scalarOneForm y := by
      filter_upwards [hupstream, hminus] with y hy hscalarY
      exact ⟨hy.1, hy.2, hscalarY⟩
    have hmem : {y | y ∈ U ∧
        IsActualMetricUpstreamEntranceAt4 g y choice ∧
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = -W.scalarOneForm y} ∈ nhds z :=
      hcommon
    obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hmem
    have hVU : V ⊆ U := fun y hy ↦ (hVsub hy).1
    have hregular := actualMetricDetectorRegularity_of_residual
      g choice (hgC2.mono hVU)
      (fun r c ↦ (hresidualC2 r c).mono hVU)
      (hqSqC2.mono hVU) (fun y hy ↦ (hVsub hy).2.1)
    exact ⟨{
      V := V
      choice := choice
      isOpen := hVopen
      mem := hzV
      subset := hVU
      scalarOrbit := Or.inr (fun y hy ↦ (hVsub hy).2.2)
      upstream := fun y hy ↦ (hVsub hy).2.1
      coframeC2 := hregular.1
      magnitudeC2 := hregular.2 }⟩

/-- A choice-independent physical active premise transports to the active
gate of any selector-returned pre-active regular branch.  Scalar and coupling
signs are aligned internally on the whole selected open patch. -/
theorem SelectedActualMetricEMDPreActivePatch4.activeWedge_of_physical
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (z : CurvatureCoordinateSpace4)
    (S : SelectedActualMetricEMDPreActivePatch4 g U
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 z)
    (hphysicalActive : IsPhysicalMaxwellComplexionActiveWedgeAt
      (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
      P.physicalF.field P.physicalG.field
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (fun y ↦ matrixMaxwellStress
        (coordinateMetricMatrixField4 g y)⁻¹ (P.physicalF.field y))
      (fun y ↦ continuousCovectorCoordinates (P.scalarOneForm y)) z) :
    IsActualMetricActiveFourthOrderWedgeAt g z S.choice := by
  let physicalF := P.physicalF.restrict S.subset
  let physicalG := P.physicalG.restrict S.subset
  let physicalV := fun y ↦ continuousCovectorCoordinates (P.scalarOneForm y)
  have hstress : ∀ y ∈ S.V,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g S.choice y := by
    intro y hy
    have horbit : oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus y) = P.scalarOneForm y ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus y) = -P.scalarOneForm y := by
      rcases S.scalarOrbit with hplus | hminus
      · exact Or.inl (hplus y hy)
      · exact Or.inr (hminus y hy)
    simpa [physicalF] using
      physicalStress_eq_actualMetricMaxwellResidual_of_selectedOrbit
        g P S.choice y (S.subset hy) (S.upstream y hy).1 horbit
  have hphysicalHodge : ∀ y ∈ S.V,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y) := by
    intro y hy
    simpa [physicalF, physicalG] using P.physicalHodge y (S.subset hy)
  rcases S.scalarOrbit with hplus | hminus
  · have hclosure : ∀ y ∈ S.V,
        EMDExteriorClosure matrixOneWedgeTwo
          (actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus y) P.coupling
          (physicalF.field y) (physicalG.field y)
          (matrixExteriorDerivative (physicalF.firstJet y))
          (matrixExteriorDerivative (physicalG.firstJet y)) := by
      intro y hy
      have hscalar :=
        actualMetricScalarOneFormCandidate_eq_physical_of_selected_plus
          g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          S.choice y (hplus y hy)
      simpa [physicalF, physicalG, hscalar] using
        P.exteriorClosure y (S.subset hy)
    have hscalarZ :
        actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus z = physicalV z ∨
          actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus z = -physicalV z :=
      Or.inl (by simpa [physicalV] using
        (actualMetricScalarOneFormCandidate_eq_physical_of_selected_plus
          g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          S.choice z (hplus z S.mem)))
    apply (isActualMetricActiveFourthOrderWedgeAt_iff_choiceFreePhysicalScalarOrbit
      g S.choice physicalF physicalG physicalV P.coupling z
      S.isOpen S.mem S.coframeC2 S.magnitudeC2 S.upstream
      hstress hphysicalHodge hclosure hscalarZ).mpr
    simpa [physicalF, physicalG, physicalV] using hphysicalActive

  · have hclosure : ∀ y ∈ S.V,
        EMDExteriorClosure matrixOneWedgeTwo
          (actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus y) (-P.coupling)
          (physicalF.field y) (physicalG.field y)
          (matrixExteriorDerivative (physicalF.firstJet y))
          (matrixExteriorDerivative (physicalG.firstJet y)) := by
      intro y hy
      have hscalar :=
        actualMetricScalarOneFormCandidate_eq_neg_physical_of_selected_minus
          g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          S.choice y (hminus y hy)
      apply emdExteriorClosure_detectorScalar_neg_physical
        (actualMetricScalarOneFormCandidateField4 g
          S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
          S.choice.relativeMinus y)
        (continuousCovectorCoordinates (P.scalarOneForm y)) P.coupling
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)) hscalar
      simpa [physicalF, physicalG] using P.exteriorClosure y (S.subset hy)
    have hscalarZ :
        actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus z = physicalV z ∨
          actualMetricScalarOneFormCandidateField4 g
            S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
            S.choice.relativeMinus z = -physicalV z :=
      Or.inr (by simpa [physicalV] using
        (actualMetricScalarOneFormCandidate_eq_neg_physical_of_selected_minus
          g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          S.choice z (hminus z S.mem)))
    apply (isActualMetricActiveFourthOrderWedgeAt_iff_choiceFreePhysicalScalarOrbit
      g S.choice physicalF physicalG physicalV (-P.coupling) z
      S.isOpen S.mem S.coframeC2 S.magnitudeC2 S.upstream
      hstress hphysicalHodge hclosure hscalarZ).mpr
    simpa [physicalF, physicalG, physicalV] using hphysicalActive

/-- **Breakthrough-grade regular-data composition with one physical active
premise.**  The scalar/upstream selector, regularity promotion, sign-aligned
physical EMD splice, double-angle complexion invariant, and finite detector
are composed end to end.

The selector callback now returns only `C²` regularity of its selected
Maxwell residual.  Genericity is stated once, independently of every finite
detector choice, by `hphysicalActive`. -/
theorem
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_physicalActive
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (base : ActualMetricDetectorChoice4) (i j : Fin 4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g i j y)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qminus := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (Qminus ((Pi.basisFun ℝ (Fin 4)) i))
        (Qminus ((Pi.basisFun ℝ (Fin 4)) i)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qplus := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) j))
        (Qplus ((Pi.basisFun ℝ (Fin 4)) j)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hposA : 0 < 2 * (-1 : ℝ) * reconstructedDiagonalAField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hposB : 0 < 2 * (1 : ℝ) * reconstructedDiagonalBField
      (actualRicciComplementaryRootAField4 g)
      (actualRicciComplementaryRootBField4 g)
      (actualRicciReconstructedQSqField4 g) z)
    (hP : ∀ selected a b, ContinuousAt
      (fun w ↦ actualMetricMaxwellMinusProjectorCandidateField4
        g selected w a b) z)
    (hQ : ∀ selected a b, ContinuousAt
      (fun w ↦ actualMetricMaxwellPlusProjectorCandidateField4
        g selected w a b) z)
    (hindex : HasLorentzianIndexOne
      (continuousBilinFormToBilin (g z)))
    (hdiagA : ContinuousAt (fun y ↦
      2 * (-1 : ℝ) * reconstructedDiagonalAField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) y) z)
    (hdiagB : ContinuousAt (fun y ↦
      2 * (1 : ℝ) * reconstructedDiagonalBField
        (actualRicciComplementaryRootAField4 g)
        (actualRicciComplementaryRootBField4 g)
        (actualRicciReconstructedQSqField4 g) y) z)
    (hcoframeContinuous : ∀ selected r c, ContinuousAt (fun y ↦
      actualMetricPrincipalCoframeCandidateField4 g selected y r c) z)
    (hgC2 : ContDiffOn ℝ 2 g U)
    (hqSqC2 : ContDiffOn ℝ 2
      (actualRicciReconstructedQSqField4 g) U)
    (hphysicalActive : IsPhysicalMaxwellComplexionActiveWedgeAt
      (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹)
      P.physicalF.field P.physicalG.field
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g))
      (fun y ↦ matrixMaxwellStress
        (coordinateMetricMatrixField4 g y)⁻¹ (P.physicalF.field y))
      (fun y ↦ continuousCovectorCoordinates (P.scalarOneForm y)) z)
    (hselectedResidualC2 : ∀ selected : ActualMetricDetectorChoice4,
      IsInvariantEMDSelectorReturnedChoice4 g
          P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          z i j selected →
      MatrixFieldContDiffOn 2 U
        (actualMetricMaxwellResidualCandidateField4 g selected)) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice =
        P.coupling ^ 2 := by
  have hg : ContinuousAt g z :=
    hgC2.continuousOn.continuousAt (hopen.mem_nhds hz)
  obtain ⟨selected, hi, hj, hscalar, hselectedUpstream⟩ :=
    exists_eventually_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch
      g B hopen hz base i j hjet
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      halgebraic hprobeA hprobeB halpha hbeta hposA hposB hg hP hQ
      hindex hdiagA hdiagB hcoframeContinuous
  have hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y selected := by
    filter_upwards [hselectedUpstream] with y hy
    exact ⟨hy.1, hy.2.2⟩
  have hreturned : IsInvariantEMDSelectorReturnedChoice4 g
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      z i j selected := {
    scalarTimelikeProbe := hi
    scalarSpacelikeProbe := hj
    scalarGerm := hscalar
    upstreamGerm := hupstream }
  have hresidualC2 := hselectedResidualC2 selected hreturned
  obtain ⟨S⟩ :=
    exists_selectedActualMetricEMDPreActivePatch4_of_eventually_regularData
      g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 selected z
      hscalar hupstream hgC2 hqSqC2 hresidualC2
  let T := S.withActive (S.activeWedge_of_physical g P z hphysicalActive)
  exact exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD
    g P z T

/-- Kaluza normalization of the physical-active end-to-end conclusion.  It
is kept as a small reusable corollary so the long conventional entrance-data
signature need not be duplicated. -/
theorem
    exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_invariantEMD_physicalActiveResult
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (z : CurvatureCoordinateSpace4)
    (hresult : ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice =
        P.coupling ^ 2)
    (hKaluza : P.coupling ^ 2 = 3) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice = 3 := by
  obtain ⟨acceptedChoice, haccepted, hout⟩ := hresult
  exact ⟨acceptedChoice, haccepted, hout.trans hKaluza⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
