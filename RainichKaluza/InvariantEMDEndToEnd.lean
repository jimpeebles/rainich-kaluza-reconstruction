import RainichKaluza.InvariantEMDDetectorComposition

/-!
# End-to-end invariant EMD necessity

This module closes the remaining composition seam between the finite upstream
selector and the invariant physical EMD detector theorem.

The input is a detector-choice-free genuine EMD physical patch, a realized
scalar branch, and the explicit geometric hypotheses used by the upstream
selector.  That selector existentially returns one fixed finite branch,
together with its scalar `±` germ and an eventual upstream certificate.  A
regular-locus callback supplies `C²` coframe regularity and the intrinsic
active-wedge condition for precisely such a selected scalar-probe branch.
Positive-magnitude `C²` regularity is stated separately because it is
choice-independent.

No hypothesis demands fourth-order genericity, acceptance, or an active wedge
for every raw detector channel.  The active condition is imposed only on the
fixed branch produced by the finite upstream selection.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- **End-to-end generic fourth-order necessity for a genuine invariant EMD
patch.**  The finite upstream selector chooses a single scalar sign, Maxwell
frame, and orientation.  On that selected branch, the explicit regular-locus
callback provides the two remaining choice-dependent analytic hypotheses:
`C²` regularity of its principal coframe on `U` and a nonzero intrinsic
active wedge at `z`.

The conclusion contains no matter field or coupling in its detector side:
the finite metric-only accepted set is nonempty and one accepted survivor
returns the physical invariant `a²`.

The callback is deliberately indexed by the scalar probes `i,j` fixed by the
realized branch.  It is applied only after the upstream theorem has produced
its existential selected choice; it is not a universal genericity or
acceptance premise over fourth-order component channels. -/
theorem
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd
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
    (hg : ContinuousAt g z)
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
    (hselectedRegular : ∀ selected : ActualMetricDetectorChoice4,
      selected.scalarTimelikeProbe = i →
      selected.scalarSpacelikeProbe = j →
      MatrixFieldContDiffOn 2 U
          (actualMetricPrincipalCoframeCandidateField4 g selected) ∧
        IsActualMetricActiveFourthOrderWedgeAt g z selected)
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice =
        P.coupling ^ 2 := by
  obtain ⟨selected, hi, hj, hscalar, hselectedUpstream⟩ :=
    exists_eventually_actualMetricUpstreamEntranceAt4_of_emdRicciWitnessPatch
      g B hopen hz base i j hjet
      P.toChoiceIndependentActualMetricEMDRicciWitnessPatch4
      halgebraic hprobeA hprobeB halpha hbeta hposA hposB hg hP hQ
      hindex hdiagA hdiagB hcoframeContinuous
  obtain ⟨hcoframeC2, hactive⟩ := hselectedRegular selected hi hj
  have hupstream : ∀ᶠ y in nhds z,
      y ∈ U ∧ IsActualMetricUpstreamEntranceAt4 g y selected := by
    filter_upwards [hselectedUpstream] with y hy
    exact ⟨hy.1, hy.2.2⟩
  exact
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_eventually
      g P selected z hscalar hupstream hcoframeC2 hmagnitudeC2 hactive

/-- Kaluza normalization of the end-to-end invariant EMD necessity theorem.
Under `a² = 3`, one finite metric-only accepted survivor returns exactly
`3`. -/
theorem
    exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_invariantEMD_endToEnd
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
    (hg : ContinuousAt g z)
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
    (hselectedRegular : ∀ selected : ActualMetricDetectorChoice4,
      selected.scalarTimelikeProbe = i →
      selected.scalarSpacelikeProbe = j →
      MatrixFieldContDiffOn 2 U
          (actualMetricPrincipalCoframeCandidateField4 g selected) ∧
        IsActualMetricActiveFourthOrderWedgeAt g z selected)
    (hmagnitudeC2 : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hKaluza : P.coupling ^ 2 = 3) :
    ∃ acceptedChoice : ActualMetricDetectorChoice4,
      acceptedChoice ∈
          acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z acceptedChoice = 3 := by
  obtain ⟨acceptedChoice, haccepted, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_invariantEMD_endToEnd
      g P B hopen hz base i j hjet halgebraic hprobeA hprobeB
      halpha hbeta hposA hposB hg hP hQ hindex hdiagA hdiagB
      hcoframeContinuous hselectedRegular hmagnitudeC2
  exact ⟨acceptedChoice, haccepted, hout.trans hKaluza⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
