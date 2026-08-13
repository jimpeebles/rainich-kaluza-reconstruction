import RainichKaluza.NorthStarComposition
import RainichKaluza.ActualMetricScalarIdentifiability

/-!
# Invariant EMD entrance to the fourth-order detector

This module separates the physical input of the necessity theorem from the
finite detector choices.

`ChoiceIndependentActualMetricEMDPhysicalPatch4` is a choice-independent
Ricci--exterior EMD patch: it extends the Ricci witness by a pair of actual
`C¹` matrix two-form fields, their metric Hodge relation, the Maxwell stress
identity, and exterior closure with the physical scalar covector.  It does not
package the scalar wave equation, and it contains no detector probe, scalar
sign, Maxwell frame, orientation bit, or quotient component.

`SelectedActualMetricEMDDetectorPatch4` records the still-explicit regular
branch hypotheses after the finite upstream selector has returned one fixed
choice.  In particular, it does not conceal the active-wedge hypothesis or
the fact that a single scalar sign must persist on the selected open patch.

The main theorem composes these two packages.  The detector residual stress
is derived from the physical Ricci decomposition, and the signed coupling is
chosen as `a` or `-a` according to the selected scalar germ.  Hence the finite
metric-only accepted set is nonempty and its output is the invariant `a²`.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

namespace RescaledMaxwellMatrixC1On

variable {U V : Set BaseCoordinateSpace}

/-- Restrict a genuine `C¹` matrix two-form realization to a smaller set.
The field and stored first jet are unchanged; only their certified domain is
shrunk. -/
def restrict (S : RescaledMaxwellMatrixC1On U) (hVU : V ⊆ U) :
    RescaledMaxwellMatrixC1On V where
  field := S.field
  firstJet := S.firstJet
  differentiable := fun z hz ↦ S.differentiable z (hVU hz)
  firstJet_continuous := fun k i j ↦
    (S.firstJet_continuous k i j).mono hVU
  alternating := fun z hz ↦ S.alternating z (hVU hz)

@[simp] theorem restrict_field
    (S : RescaledMaxwellMatrixC1On U) (hVU : V ⊆ U) :
    (S.restrict hVU).field = S.field := rfl

@[simp] theorem restrict_firstJet
    (S : RescaledMaxwellMatrixC1On U) (hVU : V ⊆ U) :
    (S.restrict hVU).firstJet = S.firstJet := rfl

end RescaledMaxwellMatrixC1On

/-- **Detector-choice-free Ricci--exterior EMD physical patch.**  Besides the Ricci
witness used for scalar identifiability, this package supplies actual `C¹`
rescaled Maxwell and Hodge fields.  Their coordinate Maxwell stress is the
choice-independent Maxwell endomorphism in the Ricci decomposition, the
second field is the exact metric Hodge star of the first, and both obey EMD
exterior closure with the physical scalar covector and one constant signed
coupling.

The scalar wave equation is deliberately not a field of this structure.  No
member of `ActualMetricDetectorChoice4` occurs in it. -/
structure ChoiceIndependentActualMetricEMDPhysicalPatch4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (U : Set CurvatureCoordinateSpace4) extends
      ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U where
  physicalF : RescaledMaxwellMatrixC1On U
  physicalG : RescaledMaxwellMatrixC1On U
  coupling : ℝ
  physicalStress : ∀ z (hz : z ∈ U),
    Matrix.toLin'
        (matrixMaxwellStress (coordinateMetricMatrixField4 g z)⁻¹
          (physicalF.field z)) =
      (witnessAt z hz).maxwellRicci
  physicalHodge : ∀ z ∈ U,
    physicalG.field z = coordinateMetricHodgeTwoForm4
      (coordinateMetricMatrixField4 g z) (physicalF.field z)
  exteriorClosure : ∀ z ∈ U,
    EMDExteriorClosure matrixOneWedgeTwo
      (continuousCovectorCoordinates (scalarOneForm z)) coupling
      (physicalF.field z) (physicalG.field z)
      (matrixExteriorDerivative (physicalF.firstJet z))
      (matrixExteriorDerivative (physicalG.firstJet z))

/-- **The explicit selected-branch remainder.**  This package is deliberately
not choice-independent: it records the fixed finite branch returned by the
upstream selector and the open subpatch on which that same branch is regular.
The scalar sign is fixed on the whole subpatch, and the intrinsic active-wedge
gate is stated separately at the base point.

These hypotheses are exactly the current regular-locus boundary.  They are
not universal statements about all raw detector choices. -/
structure SelectedActualMetricEMDDetectorPatch4
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
  activeWedge : IsActualMetricActiveFourthOrderWedgeAt g z choice

/-- Intersect one fixed scalar-sign germ with one fixed upstream germ and
represent their common neighborhood by an honest open selected patch.

The `C²` coframe and magnitude assumptions are made on the original physical
domain `U` and restricted to the returned `V`.  The active-wedge condition is
intrinsic and pointwise at `z`; it is intentionally not promoted to a
universal raw-channel hypothesis. -/
theorem exists_selectedActualMetricEMDDetectorPatch4_of_eventually
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
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
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
    refine ⟨{
      V := V
      choice := choice
      isOpen := hVopen
      mem := hzV
      subset := hVU
      scalarOrbit := Or.inl (fun y hy ↦ (hVsub hy).2.2)
      upstream := fun y hy ↦ (hVsub hy).2.1
      coframeC2 := fun i j ↦ (hcoframeC2 i j).mono hVU
      magnitudeC2 := hmagnitudeC2.mono hVU
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
    refine ⟨{
      V := V
      choice := choice
      isOpen := hVopen
      mem := hzV
      subset := hVU
      scalarOrbit := Or.inr (fun y hy ↦ (hVsub hy).2.2)
      upstream := fun y hy ↦ (hVsub hy).2.1
      coframeC2 := fun i j ↦ (hcoframeC2 i j).mono hVU
      magnitudeC2 := hmagnitudeC2.mono hVU
      activeWedge := hactive }⟩

/-- A selected scalar branch in the positive physical orbit identifies the
detector scalar one-form with the coordinate form of the invariant physical
covector. -/
theorem actualMetricScalarOneFormCandidate_eq_physical_of_selected_plus
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (choice : ActualMetricDetectorChoice4) (y : CurvatureCoordinateSpace4)
    (hscalar : oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) = W.scalarOneForm y) :
    actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y =
      continuousCovectorCoordinates (W.scalarOneForm y) := by
  exact oneForm4_eq_continuousCovectorCoordinates_of_toContinuousLinearMap_eq
    _ _ hscalar

/-- The corresponding coordinate identity on the negative physical scalar
branch. -/
theorem actualMetricScalarOneFormCandidate_eq_neg_physical_of_selected_minus
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (choice : ActualMetricDetectorChoice4) (y : CurvatureCoordinateSpace4)
    (hscalar : oneForm4ContinuousLinearMap
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) = -W.scalarOneForm y) :
    actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y =
      -continuousCovectorCoordinates (W.scalarOneForm y) := by
  have hcoords :=
    oneForm4_eq_continuousCovectorCoordinates_of_toContinuousLinearMap_eq
      (actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y) (-W.scalarOneForm y) hscalar
  rw [hcoords]
  funext i
  simp [continuousCovectorCoordinates]

/-- The physical Maxwell stress equation and the choice-independent Ricci
decomposition force equality with the detector residual on every selected
scalar-orbit branch.  Thus residual stress is a conclusion, not a physical
entrance assumption. -/
theorem physicalStress_eq_actualMetricMaxwellResidual_of_selectedOrbit
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (choice : ActualMetricDetectorChoice4)
    (y : CurvatureCoordinateSpace4) (hy : y ∈ U)
    (halgebraic : IsActualMetricAlgebraicEntranceAt4 g y)
    (horbit : oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = P.scalarOneForm y ∨
      oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = -P.scalarOneForm y) :
    matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
        (P.physicalF.field y) =
      actualMetricMaxwellResidualCandidateField4 g choice y := by
  apply Matrix.toLin'.injective
  rw [P.physicalStress y hy]
  exact (actualMetricMaxwellResidual_toLin_eq_emdRicciWitness
    g y choice (P.witnessAt y hy) (P.scalarOneForm y)
      (P.scalarCovector_eq y hy) halgebraic horbit).symm

/-- Componentwise continuity of the selected detector scalar follows from
the invariant physical covector field once one fixed sign is known on the
selected patch. -/
theorem selectedScalarCandidate_continuousOn_of_orbit
    {U V : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (W : ChoiceIndependentActualMetricEMDRicciWitnessPatch4 g U)
    (choice : ActualMetricDetectorChoice4) (hVU : V ⊆ U)
    (horbit :
      (∀ y ∈ V,
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = W.scalarOneForm y) ∨
      (∀ y ∈ V,
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = -W.scalarOneForm y)) :
    ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y i) V := by
  intro i
  have hphysical : ContinuousOn (fun y ↦
      continuousCovectorCoordinates (W.scalarOneForm y) i) V := by
    change ContinuousOn (fun y ↦
      W.scalarOneForm y (curvatureCoordinateDirection i)) V
    exact continuousOn_clm_apply.mp (W.scalarContinuous.mono hVU)
      (curvatureCoordinateDirection i)
  rcases horbit with hplus | hminus
  · exact hphysical.congr (fun y hy ↦ congrFun
      (actualMetricScalarOneFormCandidate_eq_physical_of_selected_plus
        g W choice y (hplus y hy)) i)
  · exact hphysical.neg.congr (fun y hy ↦ congrFun
      (actualMetricScalarOneFormCandidate_eq_neg_physical_of_selected_minus
        g W choice y (hminus y hy)) i)

/-- **Invariant EMD necessity composed with the finite detector.**  A
choice-independent Ricci--exterior EMD physical patch and one explicitly regular selected
metric branch imply that the finite metric-only detector is nonempty at `z`
and returns the physical squared coupling.

The proof handles the unavoidable scalar ambiguity constructively.  On the
positive scalar branch it invokes the north-star theorem with `orientedA=a`;
on the negative branch it invokes it with `orientedA=-a`.  The physical stress
and exact Hodge field are restricted from `U` to the selected open patch `V`.
No premise quantifies genericity over every raw channel. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (z : CurvatureCoordinateSpace4)
    (S : SelectedActualMetricEMDDetectorPatch4 g U
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 z) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z choice =
        P.coupling ^ 2 := by
  let physicalF := P.physicalF.restrict S.subset
  let physicalG := P.physicalG.restrict S.subset
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
  have hvContinuous : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        S.choice.scalarTimelikeProbe S.choice.scalarSpacelikeProbe
        S.choice.relativeMinus y i) S.V :=
    selectedScalarCandidate_continuousOn_of_orbit g
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 S.choice
      S.subset S.scalarOrbit
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
    exact
      exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_patch_physicalHodgeFields
        g S.choice physicalF physicalG P.coupling P.coupling z
        S.isOpen S.mem S.coframeC2 S.magnitudeC2
        S.upstream hstress hphysicalHodge hvContinuous hclosure
        S.activeWedge rfl
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
    apply
      exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_patch_physicalHodgeFields
        g S.choice physicalF physicalG P.coupling (-P.coupling) z
        S.isOpen S.mem S.coframeC2 S.magnitudeC2
        S.upstream hstress hphysicalHodge hvContinuous hclosure S.activeWedge
    ring

/-- **Eventual fixed-branch form of invariant EMD necessity.**  A scalar
`\u00b1` germ and an eventual upstream entrance are intersected automatically.
The only regular-locus obligations left explicit are `C²` regularity of the
selected coframe and positive magnitude on `U`, together with the intrinsic
active wedge at `z`.  The conclusion is nonemptiness of the finite metric-only
accepted set with output equal to the physical invariant `a²`. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_eventually
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hscalar :
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z] P.scalarOneForm) ∨
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z]
        fun y ↦ -P.scalarOneForm y))
    (hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice)
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z choice) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice =
        P.coupling ^ 2 := by
  obtain ⟨S⟩ :=
    exists_selectedActualMetricEMDDetectorPatch4_of_eventually g
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 choice z
      hscalar hupstream hcoframeC2 hmagnitudeC2 hactive
  exact
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD
      g P z S

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
/-- Kaluza normalization of the invariant physical-patch composition. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_invariantEMD
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (z : CurvatureCoordinateSpace4)
    (S : SelectedActualMetricEMDDetectorPatch4 g U
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 z)
    (hKaluza : P.coupling ^ 2 = 3) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z choice = 3 := by
  obtain ⟨choice, hchoice, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD
      g P z S
  exact ⟨choice, hchoice, hout.trans hKaluza⟩

/-- Kaluza normalization of the eventual fixed-branch composition. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_invariantEMD_eventually
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hscalar :
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z] P.scalarOneForm) ∨
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y)) =ᶠ[nhds z]
        fun y ↦ -P.scalarOneForm y))
    (hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice)
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z choice)
    (hKaluza : P.coupling ^ 2 = 3) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice = 3 := by
  obtain ⟨acceptedChoice, hmem, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_eventually
      g P choice z hscalar hupstream hcoframeC2 hmagnitudeC2 hactive
  exact ⟨acceptedChoice, hmem, hout.trans hKaluza⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
