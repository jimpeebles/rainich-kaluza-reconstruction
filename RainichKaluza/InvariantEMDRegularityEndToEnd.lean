import RainichKaluza.ActualMetricDetectorRegularity
import RainichKaluza.InvariantEMDEndToEnd

/-!
# Invariant EMD end-to-end theorem from conventional regularity data

This module removes the selected-coframe and protected-magnitude `C²`
premises from the end-to-end invariant EMD theorem.  Instead it assumes
ordinary `C²` regularity of the metric, reconstructed squared magnitude,
and the selected Maxwell residual.  The true coframe and positive magnitude
regularity are then derived on the open neighborhood where the upstream
selector has actually certified its fixed branch.

The intrinsic active-wedge condition remains explicit.  It is the genuine
generic-locus hypothesis and is not a regularity consequence.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- Certificate that a finite detector choice is genuinely one of the fixed
branches returned by the invariant scalar/upstream selector at `z`.  This
lets downstream regular-locus callbacks be conditional on actual selector
output rather than quantifying genericity over every raw frame choice. -/
structure IsInvariantEMDSelectorReturnedChoice4
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (z : CurvatureCoordinateSpace4) (i j : Fin 4)
    (choice : ActualMetricDetectorChoice4) : Prop where
  scalarTimelikeProbe : choice.scalarTimelikeProbe = i
  scalarSpacelikeProbe : choice.scalarSpacelikeProbe = j
  scalarGerm :
    ((fun y ↦ oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y)) =ᶠ[nhds z] W.scalarOneForm) ∨
    ((fun y ↦ oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y)) =ᶠ[nhds z]
      fun y ↦ -W.scalarOneForm y)
  upstreamGerm : ∀ᶠ y in nhds z,
    y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice

/-- Intersect a fixed scalar-sign germ with an eventual upstream branch and
derive, rather than assume, the selected coframe and positive-magnitude
regularity on their common open neighborhood. -/
theorem
    exists_selectedActualMetricEMDDetectorPatch4_of_eventually_regularData
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
      (actualMetricMaxwellResidualCandidateField4 g choice))
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z choice) :
    Nonempty (SelectedActualMetricEMDDetectorPatch4 g U W z) := by
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
    refine ⟨{
      V := V
      choice := choice
      isOpen := hVopen
      mem := hzV
      subset := hVU
      scalarOrbit := Or.inl (fun y hy ↦ (hVsub hy).2.2)
      upstream := fun y hy ↦ (hVsub hy).2.1
      coframeC2 := hregular.1
      magnitudeC2 := hregular.2
      activeWedge := hactive }⟩
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
    refine ⟨{
      V := V
      choice := choice
      isOpen := hVopen
      mem := hzV
      subset := hVU
      scalarOrbit := Or.inr (fun y hy ↦ (hVsub hy).2.2)
      upstream := fun y hy ↦ (hVsub hy).2.1
      coframeC2 := hregular.1
      magnitudeC2 := hregular.2
      activeWedge := hactive }⟩

/-- **Regularity-closed end-to-end invariant EMD necessity.**  Conventional
`C²` regularity of `g`, reconstructed `q²`, and the residual of each
selector-eligible scalar branch replaces the earlier explicit coframe and
positive-magnitude regularity assumptions.  The callback retains only the
selected residual regularity and the intrinsic active-wedge condition. -/
theorem
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_regularData
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
    (hselectedResidualActive : ∀ selected : ActualMetricDetectorChoice4,
      IsInvariantEMDSelectorReturnedChoice4 g
          P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          z i j selected →
      MatrixFieldContDiffOn 2 U
          (actualMetricMaxwellResidualCandidateField4 g selected) ∧
        IsActualMetricActiveFourthOrderWedgeAt g z selected) :
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
      z i j selected := by
    exact {
      scalarTimelikeProbe := hi
      scalarSpacelikeProbe := hj
      scalarGerm := hscalar
      upstreamGerm := hupstream }
  obtain ⟨hresidualC2, hactive⟩ :=
    hselectedResidualActive selected hreturned
  obtain ⟨S⟩ :=
    exists_selectedActualMetricEMDDetectorPatch4_of_eventually_regularData
      g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 selected z
      hscalar hupstream hgC2 hqSqC2 hresidualC2 hactive
  exact
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD
      g P z S

/-- Kaluza normalization of the regularity-closed end-to-end theorem. -/
theorem
    exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_invariantEMD_endToEnd_regularData
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
    (hselectedResidualActive : ∀ selected : ActualMetricDetectorChoice4,
      IsInvariantEMDSelectorReturnedChoice4 g
          P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          z i j selected →
      MatrixFieldContDiffOn 2 U
          (actualMetricMaxwellResidualCandidateField4 g selected) ∧
        IsActualMetricActiveFourthOrderWedgeAt g z selected)
    (hKaluza : P.coupling ^ 2 = 3) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice = 3 := by
  obtain ⟨acceptedChoice, haccepted, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd_regularData
      g P B hopen hz base i j hjet halgebraic hprobeA hprobeB
      halpha hbeta hposA hposB hP hQ hindex hdiagA hdiagB
      hcoframeContinuous hgC2 hqSqC2 hselectedResidualActive
  exact ⟨acceptedChoice, haccepted, hout.trans hKaluza⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
