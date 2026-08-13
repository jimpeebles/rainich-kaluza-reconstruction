import RainichKaluza.InvariantEMDConfluence

/-!
# Publication-facing invariant EMD confluence corollaries

The pointwise accepted-choice theorem identifies one finite detector survivor
with the physical value `a²`.  This file packages the two immediate statements
used in the manuscript:

* two independently accepted pointwise survivors agree when each satisfies
  its own unique scalar-closure and regularity hypotheses;
* if every member of the finite accepted set carries those hypotheses, then
  the finite image of detector outputs is the singleton `{a²}` as soon as the
  accepted set is nonempty.

Neither statement strengthens the geometric hypotheses of the underlying
correctness theorem.  Their purpose is to make its all-survivor quantifiers
explicit and publication-safe.
-/

namespace RainichKaluza

open scoped Matrix Topology

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- **Pointwise pairwise confluence on the unique-closure locus.**  The two
choices need only belong to the finite accepted set at the base point.  Each
choice has its own realized scalar branch, admissible probes, unique-closure
gate, frame continuity, and coframe regularity.  The algebraic entrance,
diagonal continuity, and protected-magnitude regularity are shared geometric
data. -/
theorem
    actualMetricFourthOrderCouplingSqCandidates_eq_of_invariantEMD_pointwiseAccepted
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
    (haccepted : choice ∈
      acceptedActualMetricFourthOrderDetectorChoicesAt g z)
    (haccepted' : choice' ∈
      acceptedActualMetricFourthOrderDetectorChoicesAt g z)
    (hframesContinuous :
      AreActualMetricSelectedFramePairingsContinuousAt4 g z choice)
    (hframesContinuous' :
      AreActualMetricSelectedFramePairingsContinuousAt4 g z choice')
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
    (hcoframeC2' : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice'))
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      actualMetricFourthOrderCouplingSqCandidateAt g z choice' := by
  rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted
      g P B hopen hz choice hjet halgebraic hprobeA hprobeB
      halpha hbeta hunique haccepted hframesContinuous hdiagA hdiagB
      hcoframeC2 hmagnitudeC2,
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted
      g P B' hopen hz choice' hjet' halgebraic hprobeA' hprobeB'
      halpha' hbeta' hunique' haccepted' hframesContinuous' hdiagA hdiagB
      hcoframeC2' hmagnitudeC2]

/-- Per-choice local data needed to apply pointwise accepted-branch
correctness.  Acceptance itself and the geometric hypotheses common to every
choice are intentionally kept outside this certificate. -/
structure InvariantEMDPointwiseSurvivorData4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (U : Set CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) where
  branch : RealizedCurvatureScalarBranchPatch4 U
  jet : ∀ y, branch.jet y = actualMetricScalarBranchJetField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe y
  probeA : ∀ y ∈ U,
    let gb := continuousBilinFormToBilin (g y)
    let Qminus := Matrix.toLin'
      (actualRicciComplementaryProjectorAField4 g y)
    gb (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe))
      (Qminus ((Pi.basisFun ℝ (Fin 4)) choice.scalarTimelikeProbe)) < 0
  probeB : ∀ y ∈ U,
    let gb := continuousBilinFormToBilin (g y)
    let Qplus := Matrix.toLin'
      (actualRicciComplementaryProjectorBField4 g y)
    0 < gb (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe))
      (Qplus ((Pi.basisFun ℝ (Fin 4)) choice.scalarSpacelikeProbe))
  alpha_ne : branch.alphaField z ≠ 0
  beta_ne : branch.betaField z ≠ 0
  uniqueClosure : IsActualMetricUniqueScalarClosureBranchAt4 g z
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
  framesContinuous :
    AreActualMetricSelectedFramePairingsContinuousAt4 g z choice
  coframeC2 : MatrixFieldContDiffOn 2 U
    (actualMetricPrincipalCoframeCandidateField4 g choice)

/-- A per-survivor certificate turns pointwise accepted-set membership into
the physical squared coupling. -/
theorem InvariantEMDPointwiseSurvivorData4.output_eq_physical
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    (D : InvariantEMDPointwiseSurvivorData4 g U z choice)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (hopen : IsOpen U) (hz : z ∈ U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
    (haccepted : choice ∈
      acceptedActualMetricFourthOrderDetectorChoicesAt g z)
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
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      P.coupling ^ 2 := by
  exact
    actualMetricFourthOrderCouplingSqCandidate_eq_physical_of_invariantEMD_pointwiseAccepted
      g P D.branch hopen hz choice D.jet halgebraic D.probeA D.probeB
      D.alpha_ne D.beta_ne D.uniqueClosure haccepted D.framesContinuous
      hdiagA hdiagB D.coframeC2 hmagnitudeC2

/-- The finite set of squared-coupling values carried by pointwise accepted
actual-metric detector choices. -/
noncomputable def acceptedActualMetricFourthOrderCouplingSqValuesAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Finset ℝ :=
  (acceptedActualMetricFourthOrderDetectorChoicesAt g z).image
    (actualMetricFourthOrderCouplingSqCandidateAt g z)

/-- **Singleton-image publication corollary.**  If the finite accepted set is
nonempty and every accepted choice carries its own pointwise survivor data,
then the complete finite image of detector outputs is exactly `{a²}`. -/
theorem acceptedActualMetricFourthOrderCouplingSqValuesAt_eq_singleton_physical
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : ChoiceIndependentActualMetricEMDPhysicalPatch4 g U)
    (hopen : IsOpen U) {z : CurvatureCoordinateSpace4} (hz : z ∈ U)
    (halgebraic : ∀ y ∈ U, IsActualMetricAlgebraicEntranceAt4 g y)
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
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hnonempty :
      (acceptedActualMetricFourthOrderDetectorChoicesAt g z).Nonempty)
    (hdata : ∀ choice,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z →
        Nonempty (InvariantEMDPointwiseSurvivorData4 g U z choice)) :
    acceptedActualMetricFourthOrderCouplingSqValuesAt g z =
      {P.coupling ^ 2} := by
  classical
  apply Finset.ext
  intro value
  constructor
  · intro hvalue
    obtain ⟨choice, hchoice, rfl⟩ :=
      (Finset.mem_image.mp hvalue)
    obtain ⟨D⟩ := hdata choice hchoice
    have hout := D.output_eq_physical P hopen hz halgebraic hchoice
      hdiagA hdiagB hmagnitudeC2
    simp [hout]
  · intro hvalue
    have hvalueEq : value = P.coupling ^ 2 := by simpa using hvalue
    obtain ⟨choice, hchoice⟩ := hnonempty
    obtain ⟨D⟩ := hdata choice hchoice
    have hout := D.output_eq_physical P hopen hz halgebraic hchoice
      hdiagA hdiagB hmagnitudeC2
    apply Finset.mem_image.mpr
    exact ⟨choice, hchoice, hout.trans hvalueEq.symm⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
