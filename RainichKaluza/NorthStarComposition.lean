import RainichKaluza.FourthOrderMetricDetector

/-!
# Actual-metric north-star composition

This module closes the geometric germ splice used by the patchwise physical
channel theorem.  Reconstructed Maxwell stress fixes a physical two-form to
the local duality circle.  On the positive-orientation coframe branch, the
coordinate metric Hodge star then fixes its Hodge partner with the same
complexion.  Consequently the physical field germs required by the
fourth-order quotient theorem are consequences of stress and Hodge geometry,
not additional matter-field matching assumptions.
-/

namespace RainichKaluza

open scoped Matrix Topology
open Matrix Filter

/-- Raw quotient-channel indices do not enter the reconstructed Maxwell
residual. -/
@[simp] theorem actualMetricMaxwellResidualCandidateField4_withChannel
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (channel : FourthOrderComponentChoice) :
    actualMetricMaxwellResidualCandidateField4 g
        (choice.withChannel channel) =
      actualMetricMaxwellResidualCandidateField4 g choice := by
  rfl

/-- Exact Hodge action on a transported canonical duality rotation in a
positive-orientation coframe. -/
theorem coordinateMetricHodgeTwoForm4_dualityRotation_of_det_pos
    (G L K : Matrix4) (E c s : ℝ)
    (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hdet : 0 < Matrix.det L) :
    coordinateMetricHodgeTwoForm4 G
        (transportTwoForm L
          (c • canonicalMaxwellTwoForm E 0 +
            s • canonicalHodgeStar E 0)) =
      transportTwoForm L
        ((-s) • canonicalMaxwellTwoForm E 0 +
          c • canonicalHodgeStar E 0) := by
  have hrotF :
      c • canonicalMaxwellTwoForm E 0 +
          s • canonicalHodgeStar E 0 =
        canonicalMaxwellTwoForm (c * E) (s * E) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalHodgeStar, canonicalMaxwellTwoForm]
  have hrotG :
      (-s) • canonicalMaxwellTwoForm E 0 +
          c • canonicalHodgeStar E 0 =
        canonicalHodgeStar (c * E) (s * E) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalHodgeStar, canonicalMaxwellTwoForm]
  rw [hrotF, hrotG]
  exact coordinateMetricHodgeTwoForm4_canonical_of_det_pos
    G L K (c * E) (s * E) hG hKL hLK hdet

/-- Pulling a two-form to an invertible principal frame and identifying its
canonical duality coordinates identifies the original coordinate two-form
after transport back. -/
theorem eq_transportTwoForm_dualityRotation_of_pullback_eq
    (L K F F0 G0 : Matrix4) (c s : ℝ)
    (hKL : K * L = 1) (_hLK : L * K = 1)
    (hpull : transportTwoForm K F = c • F0 + s • G0) :
    F = c • transportTwoForm L F0 +
      s • transportTwoForm L G0 := by
  have hback : transportTwoForm L (transportTwoForm K F) = F := by
    rw [← transportTwoForm_mul L K F, hKL]
    simp [transportTwoForm]
  rw [← hback, hpull, transportTwoForm_add_detector,
    transportTwoForm_smul, transportTwoForm_smul]

/-- Pointwise physical-field realization of one positive-`q` duality jet.
The Maxwell field follows from its pulled stress-fibre coordinates.  If the
second physical field is the actual metric Hodge star and the coframe is
positively oriented, it follows with the same complexion automatically. -/
theorem physicalFields_eq_localPositiveQExteriorDualityJet_of_pullback_hodge
    (G L K F H : Matrix4) (q c s : ℝ)
    (dL : Fin 4 → Matrix4) (dq dc ds : OneForm4)
    (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hdet : 0 < Matrix.det L)
    (hpull : transportTwoForm K F =
      c • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
        s • canonicalHodgeStar (Real.sqrt (2 * q)) 0)
    (hH : H = coordinateMetricHodgeTwoForm4 G F) :
    let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
    F = J.rotatedF ∧ H = J.rotatedG := by
  let E := Real.sqrt (2 * q)
  let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
  change transportTwoForm K F =
    c • canonicalMaxwellTwoForm E 0 +
      s • canonicalHodgeStar E 0 at hpull
  have hFsum : F =
      c • transportTwoForm L (canonicalMaxwellTwoForm E 0) +
        s • transportTwoForm L (canonicalHodgeStar E 0) :=
    eq_transportTwoForm_dualityRotation_of_pullback_eq
      L K F (canonicalMaxwellTwoForm E 0) (canonicalHodgeStar E 0)
        c s hKL hLK hpull
  have hF : F = transportTwoForm L
      (c • canonicalMaxwellTwoForm E 0 +
        s • canonicalHodgeStar E 0) := by
    simpa only [transportTwoForm_add_detector, transportTwoForm_smul] using hFsum
  have hHodge :=
    coordinateMetricHodgeTwoForm4_dualityRotation_of_det_pos
      G L K E c s hG hKL hLK hdet
  constructor
  · change F =
      c • transportTwoForm L (canonicalMaxwellTwoForm E 0) +
        s • transportTwoForm L (canonicalHodgeStar E 0)
    exact hFsum
  · rw [hH, hF, hHodge]
    change transportTwoForm L
        ((-s) • canonicalMaxwellTwoForm E 0 +
          c • canonicalHodgeStar E 0) =
      (-s) • transportTwoForm L (canonicalMaxwellTwoForm E 0) +
        c • transportTwoForm L (canonicalHodgeStar E 0)
    rw [transportTwoForm_add_detector, transportTwoForm_smul,
      transportTwoForm_smul]

/-- **Geometric physical-channel splice without germ assumptions.**  The
stress equation fixes the physical Maxwell field on the reconstructed
duality circle.  Positive-orientation Hodge naturality then fixes its physical
Hodge partner.  These pointwise geometric identities imply the field germs
consumed by the genuine `C¹` first-jet transfer theorem. -/
theorem isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalHodgeFields
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (a : ℝ) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice))
    (hqSmooth : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hvContinuous : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y i) U)
    (hsource :
      pullCovectorToPrincipalFrame
          (actualMetricPrincipalCoframeCandidateField4 g choice z)⁻¹
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus z) choice.channel.1 ≠ 0)
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) a
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y))) :
    IsActualMetricPhysicalConstantCouplingChannelAt g z choice a := by
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g)
  let K := fun y ↦ (L y)⁻¹
  let pulledF := fun y ↦ transportTwoForm (K y) (physicalF.field y)
  let c := smoothCanonicalStressFiberCosine q pulledF
  let s := smoothCanonicalStressFiberSine q pulledF
  have hLSmoothOne : MatrixFieldContDiffOn 1 U L := by
    intro i j
    exact (hLSmooth i j).of_le (by norm_num)
  have hKSmooth : MatrixFieldContDiffOn 1 U K := by
    simpa [L, K] using
      matrixFieldContDiffOn_actualMetricPrincipalCoframeCandidate_inv_of_upstream
        g choice hLSmoothOne hupstream
  have hstressFiber :
      ContDiffOn ℝ 1 c U ∧ ContDiffOn ℝ 1 s U ∧
        (∀ y ∈ U, c y ^ 2 + s y ^ 2 = 1) ∧
        ∀ y ∈ U,
          pulledF y = c y •
                canonicalMaxwellTwoForm (Real.sqrt (2 * q y)) 0 +
              s y • canonicalHodgeStar (Real.sqrt (2 * q y)) 0 := by
    simpa [L, q, K, pulledF, c, s] using
      smoothActualMetricAdaptedMaxwellStressFiber_coordinates_of_c1
        g choice physicalF hopen (hqSmooth.of_le (by norm_num))
          hKSmooth hupstream hstress
  have hgerms :
      ∀ y ∈ U,
        physicalF.field =ᶠ[nhds y] (fun x ↦
            (localPositiveQExteriorDualityJet
              (L x) (fun k i j ↦
                scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
              (q x) (scalarFieldCoordinateFDeriv q x)
              (c x) (s x) (scalarFieldCoordinateFDeriv c x)
              (scalarFieldCoordinateFDeriv s x)).rotatedF) ∧
          physicalG.field =ᶠ[nhds y] (fun x ↦
            (localPositiveQExteriorDualityJet
              (L x) (fun k i j ↦
                scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
              (q x) (scalarFieldCoordinateFDeriv q x)
              (c x) (s x) (scalarFieldCoordinateFDeriv c x)
              (scalarFieldCoordinateFDeriv s x)).rotatedG) := by
    intro y hy
    constructor <;> filter_upwards [hopen.mem_nhds hy] with x hx
    · exact (physicalFields_eq_localPositiveQExteriorDualityJet_of_pullback_hodge
        (coordinateMetricMatrixField4 g x) (L x) (K x)
        (physicalF.field x) (physicalG.field x) (q x) (c x) (s x)
        (fun k i j ↦ scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
        (scalarFieldCoordinateFDeriv q x)
        (scalarFieldCoordinateFDeriv c x)
        (scalarFieldCoordinateFDeriv s x)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_metric_of_upstream
            g x choice (hupstream x hx)).symm)
        (by simpa [K, L] using
          (actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
            g x choice (hupstream x hx)))
        (by simpa [K, L] using
          (actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
            g x choice (hupstream x hx)))
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
            g x choice (hupstream x hx)))
        (hstressFiber.2.2.2 x hx)
        (by simpa [L] using hphysicalHodge x hx)).1
    · exact (physicalFields_eq_localPositiveQExteriorDualityJet_of_pullback_hodge
        (coordinateMetricMatrixField4 g x) (L x) (K x)
        (physicalF.field x) (physicalG.field x) (q x) (c x) (s x)
        (fun k i j ↦ scalarFieldCoordinateFDeriv (fun w ↦ L w i j) x k)
        (scalarFieldCoordinateFDeriv q x)
        (scalarFieldCoordinateFDeriv c x)
        (scalarFieldCoordinateFDeriv s x)
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_metric_of_upstream
            g x choice (hupstream x hx)).symm)
        (by simpa [K, L] using
          (actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
            g x choice (hupstream x hx)))
        (by simpa [K, L] using
          (actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
            g x choice (hupstream x hx)))
        (by simpa [L] using
          (actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
            g x choice (hupstream x hx)))
        (hstressFiber.2.2.2 x hx)
        (by simpa [L] using hphysicalHodge x hx)).2
  unfold IsActualMetricPhysicalConstantCouplingChannelAt
  dsimp only
  exact isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalFields
    g choice physicalF physicalG a z hopen hz hLSmooth hqSmooth hKSmooth
    (physicalF.contDiffOn_field hopen) hupstream hstress hvContinuous hsource
    (by simpa [L, q, K, pulledF, c, s] using hgerms) hclosure

/-- **Conditional publishable fourth-order necessity theorem.**  On a fixed
actual-metric upstream branch, a genuine `C¹` Maxwell/Hodge pair with the
reconstructed stress, the exact physical Hodge relation, and EMD exterior
closure makes the finite detector nonempty on the intrinsic active-wedge
locus.  The selected raw choice returns the physical invariant `a²`.

`orientedA` records the unavoidable simultaneous scalar/coupling sign.  The
detector output is insensitive to that sign through `orientedA² = a²`. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_patch_physicalHodgeFields
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (a orientedA : ℝ) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g base))
    (hqSmooth : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y base)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g base y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hvContinuous : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        base.scalarTimelikeProbe base.scalarSpacelikeProbe
        base.relativeMinus y i) U)
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          base.scalarTimelikeProbe base.scalarSpacelikeProbe
          base.relativeMinus y) orientedA
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)))
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z base)
    (horiented : orientedA ^ 2 = a ^ 2) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z choice = a ^ 2 := by
  obtain ⟨channel, hgeneric⟩ :=
    exists_actualMetricGenericFourthOrderComponentAt_withChannel
      g z base hactive
  let choice := base.withChannel channel
  have hLSmooth' : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g choice) := by
    simpa [choice] using hLSmooth
  have hupstream' : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y choice := by
    intro y hy
    exact (isActualMetricUpstreamEntranceAt4_withChannel
      g y base channel).mpr (hupstream y hy)
  have hstress' : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g choice y := by
    intro y hy
    simpa [choice] using hstress y hy
  have hvContinuous' : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus y i) U := by
    intro i
    simpa [choice, ActualMetricDetectorChoice4.withChannel] using hvContinuous i
  have hclosure' : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus y) orientedA
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)) := by
    intro y hy
    simpa [choice, ActualMetricDetectorChoice4.withChannel] using hclosure y hy
  have hphysical : IsActualMetricPhysicalConstantCouplingChannelAt
      g z choice orientedA :=
    isActualMetricPhysicalConstantCouplingChannelAt_of_patch_physicalHodgeFields
      g choice physicalF physicalG orientedA z hopen hz hLSmooth' hqSmooth
      hupstream' hstress' hphysicalHodge hvContinuous'
      hgeneric.1 hclosure'
  have hupstreamZ : IsActualMetricUpstreamEntranceAt4 g z choice :=
    hupstream' z hz
  have haccepted : IsActualMetricFourthOrderDetectorCandidateAt g z choice :=
    isActualMetricFourthOrderDetectorCandidateAt_of_upstream_physical
      g z choice orientedA hupstreamZ hphysical hgeneric
  refine ⟨choice, ?_, ?_⟩
  · rw [mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff]
    exact haccepted
  · rw [actualMetricFourthOrderCouplingSqCandidate_eq_physical
      g z choice orientedA haccepted hphysical, horiented]

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
/-- Kaluza normalization of the patchwise nonemptiness theorem. -/
theorem exists_acceptedActualMetricFourthOrderChoice_and_eq_three_of_patch_physicalHodgeFields
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (base : ActualMetricDetectorChoice4)
    (physicalF physicalG : RescaledMaxwellMatrixC1On U)
    (a orientedA : ℝ) (z : CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hz : z ∈ U)
    (hLSmooth : MatrixFieldContDiffOn 2 U
      (actualMetricPrincipalCoframeCandidateField4 g base))
    (hqSmooth : ContDiffOn ℝ 2
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g)) U)
    (hupstream : ∀ y ∈ U,
      IsActualMetricUpstreamEntranceAt4 g y base)
    (hstress : ∀ y ∈ U,
      matrixMaxwellStress (coordinateMetricMatrixField4 g y)⁻¹
          (physicalF.field y) =
        actualMetricMaxwellResidualCandidateField4 g base y)
    (hphysicalHodge : ∀ y ∈ U,
      physicalG.field y = coordinateMetricHodgeTwoForm4
        (coordinateMetricMatrixField4 g y) (physicalF.field y))
    (hvContinuous : ∀ i, ContinuousOn (fun y ↦
      actualMetricScalarOneFormCandidateField4 g
        base.scalarTimelikeProbe base.scalarSpacelikeProbe
        base.relativeMinus y i) U)
    (hclosure : ∀ y ∈ U,
      EMDExteriorClosure matrixOneWedgeTwo
        (actualMetricScalarOneFormCandidateField4 g
          base.scalarTimelikeProbe base.scalarSpacelikeProbe
          base.relativeMinus y) orientedA
        (physicalF.field y) (physicalG.field y)
        (matrixExteriorDerivative (physicalF.firstJet y))
        (matrixExteriorDerivative (physicalG.firstJet y)))
    (hactive : IsActualMetricActiveFourthOrderWedgeAt g z base)
    (horiented : orientedA ^ 2 = a ^ 2) (hKaluza : a ^ 2 = 3) :
    ∃ choice : ActualMetricDetectorChoice4,
      choice ∈ acceptedActualMetricFourthOrderDetectorChoicesAt g z ∧
      actualMetricFourthOrderCouplingSqCandidateAt g z choice = 3 := by
  obtain ⟨choice, hmem, hout⟩ :=
    exists_acceptedActualMetricFourthOrderChoice_and_eq_physical_of_patch_physicalHodgeFields
      g base physicalF physicalG a orientedA z hopen hz hLSmooth hqSmooth
      hupstream hstress hphysicalHodge hvContinuous hclosure
      hactive horiented
  exact ⟨choice, hmem, hout.trans hKaluza⟩

set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable true

end RainichKaluza
