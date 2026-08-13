import RainichKaluza.InvariantEMDDetectorComposition

/-!
# Invariant EMD confluence on the uniquely integrable scalar branch

This module isolates the exact remaining seam between nonempty metric-only
fourth-order detection and full raw-choice identifiability.

Pointwise Ricci reconstruction cannot select a relative scalar sign: the
relative-sign reflection is a genuine centralizer symmetry of the
reconstruction equation.  Consequently, acceptance of an arbitrary raw
choice does not by itself identify that choice with the physical scalar
germ.  The first two theorems below state the strongest correctness and
confluence results once that germ is known.

The later theorems replace the apparently physical germ premise by a sharp
metric differential condition.  On a realized scalar-jet patch, if the two
literal relative-sign closure obstructions are not simultaneously zero, the
physical closed scalar branch is the unique closed branch.  Ordinary
continuity then promotes the strict signs of any choice accepted at the base
point to an upstream germ for that same choice.  Hence every pointwise
accepted regular survivor has the physical scalar germ up to the unavoidable
common sign and returns the invariant physical value `a^2`.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- **Accepted-branch correctness from an explicit physical scalar orbit.**
On an open regular patch, any already accepted raw choice whose scalar field
is one fixed sign of the invariant physical scalar field returns the physical
squared coupling.

Unlike the nonemptiness theorem, this result does not select a new component
channel: it proves correctness of the supplied accepted choice itself.  The
scalar-orbit premise is the exact information not implied by pointwise Ricci
reconstruction. -/
theorem
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_orbit
    {U V : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (choice : ActualMetricDetectorChoice4)
    (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen V) (hz : z ∈ V) (hVU : V ⊆ U)
    (horbit :
      (∀ y ∈ V,
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = P.scalarOneForm y) ∨
      (∀ y ∈ V,
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = -P.scalarOneForm y))
    (hcoframeC2 : MatrixFieldContDiffOn 2 V
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) V)
    (hupstream : ∀ y ∈ V,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (haccepted : IsActualMetricFourthOrderDetectorCandidateAt g z choice) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      P.coupling ^ 2 := by
  let physicalF := P.physicalF.restrict hVU
  let physicalG := P.physicalG.restrict hVU
  have hstress : ∀ y ∈ V,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y := by
    intro y hy
    have horbitY : oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = P.scalarOneForm y ∨
        oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) = -P.scalarOneForm y := by
      rcases horbit with hplus | hminus
      · exact Or.inl (hplus y hy)
      · exact Or.inr (hminus y hy)
    simpa [physicalF] using
      physicalStress_eq_actualMetricMaxwellResidual_of_selectedOrbit
        g P choice y (hVU hy) (hupstream y hy).1 horbitY
  have hphysicalHodge : ∀ y ∈ V,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y) := by
    intro y hy
    simpa [physicalF, physicalG] using P.physicalHodge y (hVU hy)
  have hvContinuous : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y i) V :=
    selectedScalarCandidate_continuousOn_of_orbit g
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4 choice
      hVU horbit
  have hsource :
      pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) choice.channel.1 ≠ 0 := by
    have hs := haccepted.toCurvatureSeed
    unfold IsCurvatureSeedFourthOrderCandidateAt
      IsTransportedSeedFourthOrderCandidate IsFourthOrderChannelCandidate
      at hs
    exact hs.2.1.1
  rcases horbit with hplus | hminus
  · have hclosure : ∀ y ∈ V,
        EMDExteriorClosure matrixOneWedgeTwo
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) P.coupling
          (physicalF.field y) (physicalG.field y)
          (matrixExteriorDerivative (physicalF.firstJet y))
          (matrixExteriorDerivative (physicalG.firstJet y)) := by
      intro y hy
      have hscalar :=
        actualMetricScalarOneFormCandidate_eq_physical_of_selected_plus
          g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          choice y (hplus y hy)
      simpa [physicalF, physicalG, hscalar] using
        P.exteriorClosure y (hVU hy)
    have hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
        g z choice P.coupling :=
      isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalHodgeFields
        g choice physicalF physicalG P.coupling z hopen hz hcoframeC2
        hmagnitudeC2 hupstream hstress hphysicalHodge hvContinuous
        hsource hclosure
    exact actualMetricFourthOrderCouplingSqCandidate_eq_physical
      g z choice P.coupling haccepted hphysical
  · have hclosure : ∀ y ∈ V,
        EMDExteriorClosure matrixOneWedgeTwo
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus y) (-P.coupling)
          (physicalF.field y) (physicalG.field y)
          (matrixExteriorDerivative (physicalF.firstJet y))
          (matrixExteriorDerivative (physicalG.firstJet y)) := by
      intro y hy
      have hscalar :=
        actualMetricScalarOneFormCandidate_eq_neg_physical_of_selected_minus
          g P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
          choice y (hminus y hy)
      apply emdExteriorClosure_detectorScalar_neg_physical
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y)
        (continuousCovectorCoordinates (P.scalarOneForm y)) P.coupling
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)) hscalar
      simpa [physicalF, physicalG] using P.exteriorClosure y (hVU hy)
    have hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
        g z choice (-P.coupling) :=
      isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalHodgeFields
        g choice physicalF physicalG (-P.coupling) z hopen hz hcoframeC2
        hmagnitudeC2 hupstream hstress hphysicalHodge hvContinuous
        hsource hclosure
    rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical
      g z choice (-P.coupling) haccepted hphysical]
    ring

/-- Eventual-germ form of accepted-branch correctness.  The scalar germ and
upstream germ are intersected automatically; regularity is restricted from
the physical patch to the resulting open neighborhood. -/
theorem
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_germ
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
    (haccepted : IsActualMetricFourthOrderDetectorCandidateAt g z choice) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      P.coupling ^ 2 := by
  rcases hscalar with hplus | hminus
  · have hcommon : ∀ᶠ y in nhds z,
        y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice ∧
          oneForm4ContinuousLinearMap
              (actualMetricScalarOneFormCandidateField4 g
                choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                choice.relativeMinus y) = P.scalarOneForm y := by
      filter_upwards [hupstream, hplus] with y hy hscalarY
      exact ⟨hy.1, hy.2, hscalarY⟩
    have hmem : {y | y ∈ U ∧
        IsActualMetricUpstreamEntranceAt4 g y choice ∧
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = P.scalarOneForm y} ∈ nhds z :=
      hcommon
    obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hmem
    have hVU : V ⊆ U := fun y hy ↦ (hVsub hy).1
    exact
      actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_orbit
        g P choice z hVopen hzV hVU
        (Or.inl (fun y hy ↦ (hVsub hy).2.2))
        (fun i j ↦ (hcoframeC2 i j).mono hVU)
        (hmagnitudeC2.mono hVU)
        (fun y hy ↦ (hVsub hy).2.1) haccepted
  · have hcommon : ∀ᶠ y in nhds z,
        y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice ∧
          oneForm4ContinuousLinearMap
              (actualMetricScalarOneFormCandidateField4 g
                choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
                choice.relativeMinus y) = -P.scalarOneForm y := by
      filter_upwards [hupstream, hminus] with y hy hscalarY
      exact ⟨hy.1, hy.2, hscalarY⟩
    have hmem : {y | y ∈ U ∧
        IsActualMetricUpstreamEntranceAt4 g y choice ∧
        oneForm4ContinuousLinearMap
            (actualMetricScalarOneFormCandidateField4 g
              choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
              choice.relativeMinus y) = -P.scalarOneForm y} ∈ nhds z :=
      hcommon
    obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp hmem
    have hVU : V ⊆ U := fun y hy ↦ (hVsub hy).1
    exact
      actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_orbit
        g P choice z hVopen hzV hVU
        (Or.inr (fun y hy ↦ (hVsub hy).2.2))
        (fun i j ↦ (hcoframeC2 i j).mono hVU)
        (hmagnitudeC2.mono hVU)
        (fun y hy ↦ (hVsub hy).2.1) haccepted

/-- Two accepted regular choices with physical scalar germs have identical
metric-only outputs, even when their probes, relative signs, Maxwell frames,
orientations, sources, and wedge components are different. -/
theorem
    actualMetricFourthOrderCouplingSqCandidates_eq_of_invariantEMD_germs
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (choice choice' : ActualMetricDetectorChoice4)
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
    (hscalar' :
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice'.scalarTimelikeProbe choice'.scalarSpacelikeProbe
            choice'.relativeMinus y)) =ᶠ[nhds z] P.scalarOneForm) ∨
      ((fun y ↦ oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice'.scalarTimelikeProbe choice'.scalarSpacelikeProbe
            choice'.relativeMinus y)) =ᶠ[nhds z]
        fun y ↦ -P.scalarOneForm y))
    (hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice)
    (hupstream' : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice')
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hcoframeC2' : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice'))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (haccepted : IsActualMetricFourthOrderDetectorCandidateAt g z choice)
    (haccepted' : IsActualMetricFourthOrderDetectorCandidateAt g z choice') :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      actualMetricFourthOrderCouplingSqCandidateAt g z choice' := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_germ
      g P choice z hscalar hupstream hcoframeC2 hmagnitudeC2 haccepted,
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_germ
      g P choice' z hscalar' hupstream' hcoframeC2' hmagnitudeC2 haccepted']

/-- The sharp pointwise differential condition that eliminates the intrinsic
relative-sign ambiguity: the two literal metric scalar branches are not both
closed at the displayed curvature jet.  On the Ricci--exterior EMD patch used
here at least one branch is locally the closed physical scalar; this condition makes that
branch unique. -/
def IsActualMetricUniqueScalarClosureBranchAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) (i j : Fin 4) : Prop :=
  ¬ (actualMetricScalarClosureObstruction4 g i j false z = 0 ∧
      actualMetricScalarClosureObstruction4 g i j true z = 0)

/-- Ordinary pointwise continuity of the four strict Gram functions used by
one selected Maxwell frame.  Together with the strict signs already present
in pointwise upstream acceptance, this promotes that same finite frame choice
to a neighborhood; it does not select or assume a new frame. -/
def AreActualMetricSelectedFramePairingsContinuousAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) : Prop :=
  ContinuousAt (fun y ↦ smoothMetricPairing g
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
      (actualMetricMaxwellLorentzPivotCandidateField4 g choice) y) z ∧
  ContinuousAt (fun y ↦ smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
        (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) y) z ∧
  ContinuousAt (fun y ↦ smoothMetricPairing g
      (actualMetricMaxwellPlusProbe0Field4 g choice)
      (actualMetricMaxwellPlusProbe0Field4 g choice) y) z ∧
  ContinuousAt (fun y ↦ smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice))
      (smoothMetricOrthogonalizeSecond g
        (actualMetricMaxwellPlusProbe0Field4 g choice)
        (actualMetricMaxwellPlusProbe1Field4 g choice)) y) z

/-- **Arbitrary accepted-choice correctness on the unique-closure locus.**
A realized scalar-jet patch and the choice-independent EMD Ricci witness
prove that one of the two relative-sign branches has a physical `±` germ.
If the two closure obstructions are not simultaneously zero, acceptance of
the supplied choice forces its stored relative-sign bit to be exactly that
physical branch.  Thus the explicit scalar-germ premise of the preceding
theorem is derived rather than assumed.

This is the strongest raw-choice correctness statement available without
excluding the known two-closed-branch locus. -/
theorem
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_uniqueClosure
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (choice : ActualMetricDetectorChoice4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qminus := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe))
        (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qplus := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe))
        (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hunique : IsActualMetricUniqueScalarClosureBranchAt4 g z
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe)
    (hacceptedOn : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y choice)
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      P.coupling ^ 2 := by
  have halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y := by
    intro y hy
    exact (hacceptedOn y hy).1.1
  obtain ⟨relativeMinus, hscalar, hrelativeClosure⟩ :=
    exists_actualMetricScalarGermAndClosureChoice_of_emdRicciWitnessPatch
      g B hopen hz choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      hjet P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      halgebraic hprobeA hprobeB halpha hbeta
  have hchoiceClosure : actualMetricScalarClosureObstruction4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z = 0 := by
    have hupstream := (hacceptedOn z hz).1
    unfold IsActualMetricUpstreamEntranceAt4 at hupstream
    dsimp only at hupstream
    exact hupstream.2.2.2.2.2.1
  have hrelative : relativeMinus = choice.relativeMinus := by
    unfold IsActualMetricUniqueScalarClosureBranchAt4 at hunique
    cases hr : relativeMinus <;> cases hc : choice.relativeMinus
    · rfl
    · exfalso
      exact hunique ⟨by simpa [hr] using hrelativeClosure,
        by simpa [hc] using hchoiceClosure⟩
    · exfalso
      exact hunique ⟨by simpa [hc] using hchoiceClosure,
        by simpa [hr] using hrelativeClosure⟩
    · rfl
  subst relativeMinus
  have hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact ⟨hy, (hacceptedOn y hy).1⟩
  exact
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_germ
      g P choice z hscalar hupstream hcoframeC2 hmagnitudeC2
      (hacceptedOn z hz)

/-- **Germ-local arbitrary-choice correctness on the unique-closure locus.**
The supplied detector choice need not be accepted on the whole physical
patch.  It is enough that acceptance persist on some (unspecified)
neighborhood of `z` inside `U`.  The choice-independent algebraic entrance
and admissible scalar-probe signs remain patchwise hypotheses because they
are exactly what constructs the physical scalar germ before it is compared
with the accepted branch.

The accepted germ automatically gives accepted-set membership at `z` and
the upstream germ needed for genuine first-jet transfer. -/
theorem
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_uniqueClosure_eventually
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (choice : ActualMetricDetectorChoice4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe y)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qminus := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe))
        (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qplus := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe))
        (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hunique : IsActualMetricUniqueScalarClosureBranchAt4 g z
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe)
    (haccepted : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricFourthOrderDetectorCandidateAt g y choice)
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      P.coupling ^ 2 := by
  obtain ⟨relativeMinus, hscalar, hrelativeClosure⟩ :=
    exists_actualMetricScalarGermAndClosureChoice_of_emdRicciWitnessPatch
      g B hopen hz choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      hjet P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      halgebraic hprobeA hprobeB halpha hbeta
  have hacceptedZ : IsActualMetricFourthOrderDetectorCandidateAt g z choice :=
    haccepted.self_of_nhds.2
  have hchoiceClosure : actualMetricScalarClosureObstruction4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z = 0 := by
    have hupstream := hacceptedZ.1
    unfold IsActualMetricUpstreamEntranceAt4 at hupstream
    dsimp only at hupstream
    exact hupstream.2.2.2.2.2.1
  have hrelative : relativeMinus = choice.relativeMinus := by
    unfold IsActualMetricUniqueScalarClosureBranchAt4 at hunique
    cases hr : relativeMinus <;> cases hc : choice.relativeMinus
    · rfl
    · exfalso
      exact hunique ⟨by simpa [hr] using hrelativeClosure,
        by simpa [hc] using hchoiceClosure⟩
    · exfalso
      exact hunique ⟨by simpa [hc] using hchoiceClosure,
        by simpa [hr] using hrelativeClosure⟩
    · rfl
  subst relativeMinus
  have hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice := by
    filter_upwards [haccepted] with y hy
    exact ⟨hy.1, hy.2.1⟩
  exact
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_germ
      g P choice z hscalar hupstream hcoframeC2 hmagnitudeC2 hacceptedZ

/-- **Pointwise accepted-set correctness on the unique-closure locus.**
This removes the patchwise or eventual acceptance premise entirely.  A raw
choice need only belong to the finite accepted set at `z`.  Its upstream
strict frame signs persist by ordinary continuity; the unique scalar-closure
condition identifies its stored relative-sign bit with the physical scalar
germ; and the existing scalar/frame promotion theorem then reconstructs an
upstream neighborhood for that same raw choice.

Thus, subject only to the displayed metric regularity and the sharp exclusion
of the two-closed-branch locus, every pointwise accepted survivor is
physically correct. -/
theorem
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (choice : ActualMetricDetectorChoice4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe y)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qminus := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe))
        (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qplus := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe))
        (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (hunique : IsActualMetricUniqueScalarClosureBranchAt4 g z
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe)
    (haccepted : choice ∈
      acceptedActualMetricFourthOrderDetectorChoicesAt g z)
    (hframesContinuous :
      AreActualMetricSelectedFramePairingsContinuousAt4 g z choice)
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
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      P.coupling ^ 2 := by
  have hacceptedAt : IsActualMetricFourthOrderDetectorCandidateAt g z choice :=
    (mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff
      g z choice).mp haccepted
  obtain ⟨relativeMinus, hscalar, hrelativeClosure⟩ :=
    exists_actualMetricScalarGermAndClosureChoice_of_emdRicciWitnessPatch
      g B hopen hz choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      hjet P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      halgebraic hprobeA hprobeB halpha hbeta
  have hchoiceClosure : actualMetricScalarClosureObstruction4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus z = 0 := by
    have hupstream := hacceptedAt.1
    unfold IsActualMetricUpstreamEntranceAt4 at hupstream
    dsimp only at hupstream
    exact hupstream.2.2.2.2.2.1
  have hrelative : relativeMinus = choice.relativeMinus := by
    unfold IsActualMetricUniqueScalarClosureBranchAt4 at hunique
    cases hr : relativeMinus <;> cases hc : choice.relativeMinus
    · rfl
    · exfalso
      exact hunique ⟨by simpa [hr] using hrelativeClosure,
        by simpa [hc] using hchoiceClosure⟩
    · exfalso
      exact hunique ⟨by simpa [hc] using hchoiceClosure,
        by simpa [hr] using hrelativeClosure⟩
    · rfl
  subst relativeMinus
  have hupstreamAt := hacceptedAt.1
  have hupstreamData := hupstreamAt
  unfold IsActualMetricUpstreamEntranceAt4 at hupstreamData
  dsimp only at hupstreamData
  rcases hupstreamData with
    ⟨_, _, _, _, _, _, _, _, _, hframe0, hframe1, hframe2, hframe3⟩
  unfold AreActualMetricSelectedFramePairingsContinuousAt4 at hframesContinuous
  have hframesGerm : ∀ᶠ y in nhds z,
      smoothMetricPairing g
          (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
          (actualMetricMaxwellLorentzPivotCandidateField4 g choice) y < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g choice))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellLorentzPivotCandidateField4 g choice)
            (actualMetricMaxwellLorentzCompanionCandidateField4 g choice)) y ∧
        0 < smoothMetricPairing g
          (actualMetricMaxwellPlusProbe0Field4 g choice)
          (actualMetricMaxwellPlusProbe0Field4 g choice) y ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe1Field4 g choice))
          (smoothMetricOrthogonalizeSecond g
            (actualMetricMaxwellPlusProbe0Field4 g choice)
            (actualMetricMaxwellPlusProbe1Field4 g choice)) y := by
    exact principalGramSigns_eventually z _ _ _ _
      hframesContinuous.1 hframesContinuous.2.1
      hframesContinuous.2.2.1 hframesContinuous.2.2.2
      hframe0 hframe1 hframe2 hframe3
  have hcoframeContinuous : ∀ r c, ContinuousAt (fun y ↦
      actualMetricPrincipalCoframeCandidateField4 g choice y r c) z := by
    intro r c
    exact ((hcoframeC2 r c).continuousOn z hz).continuousAt
      (hopen.mem_nhds hz)
  have hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y choice :=
    eventually_isActualMetricUpstreamEntranceAt4_of_scalarFrameGerms
      g B hopen hz choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      hjet P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      halgebraic hprobeA hprobeB choice rfl rfl hupstreamAt hscalar
      hframesGerm hdiagA hdiagB hcoframeContinuous
  exact
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_germ
      g P choice z hscalar hupstream hcoframeC2 hmagnitudeC2 hacceptedAt

/-- **Open-patch raw-choice confluence on the unique-closure locus.** Any
two accepted regular metric choices, possibly using completely different
finite probes and channels, return the same value once each scalar probe pair
lies off its sharp two-closed-branch locus.  Both outputs are independently
identified with the invariant physical value `P.coupling^2`. -/
theorem
    actualMetricFourthOrderCouplingSqCandidates_eq_of_invariantEMD_uniqueClosure
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (B B' : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (choice choice' : ActualMetricDetectorChoice4)
    (hjet : ∀ y, B.jet y = actualMetricScalarBranchJetField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe y)
    (hjet' : ∀ y, B'.jet y = actualMetricScalarBranchJetField4 g
      choice'.scalarTimelikeProbe choice'.scalarSpacelikeProbe y)
    (hprobeA : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qminus := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe))
        (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe)) < 0)
    (hprobeB : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qplus := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe))
        (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe)))
    (hprobeA' : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qminus := Matrix.toLin'
        (actualRicciComplementaryProjectorAField4 g y)
      gb (Qminus ((Pi.basisFun ℝ (Fin 4)) choice'.scalarTimelikeProbe))
        (Qminus ((Pi.basisFun ℝ (Fin 4)) choice'.scalarTimelikeProbe)) < 0)
    (hprobeB' : ∀ y ∈ U,
      let gb := continuousBilinFormToBilin (g y)
      let Qplus := Matrix.toLin'
        (actualRicciComplementaryProjectorBField4 g y)
      0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) choice'.scalarSpacelikeProbe))
        (Qplus ((Pi.basisFun ℝ (Fin 4)) choice'.scalarSpacelikeProbe)))
    (halpha : B.alphaField z ≠ 0) (hbeta : B.betaField z ≠ 0)
    (halpha' : B'.alphaField z ≠ 0) (hbeta' : B'.betaField z ≠ 0)
    (hunique : IsActualMetricUniqueScalarClosureBranchAt4 g z
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe)
    (hunique' : IsActualMetricUniqueScalarClosureBranchAt4 g z
      choice'.scalarTimelikeProbe choice'.scalarSpacelikeProbe)
    (hacceptedOn : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y choice)
    (hacceptedOn' : ∀ y ∈ U,
      IsActualMetricFourthOrderDetectorCandidateAt g y choice')
    (hcoframeC2 : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hcoframeC2' : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice'))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      actualMetricFourthOrderCouplingSqCandidateAt g z choice' := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_uniqueClosure
      g P B hopen hz choice hjet hprobeA hprobeB halpha hbeta hunique
      hacceptedOn hcoframeC2 hmagnitudeC2,
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_uniqueClosure
      g P B' hopen hz choice' hjet' hprobeA' hprobeB' halpha' hbeta'
      hunique' hacceptedOn' hcoframeC2' hmagnitudeC2]

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
