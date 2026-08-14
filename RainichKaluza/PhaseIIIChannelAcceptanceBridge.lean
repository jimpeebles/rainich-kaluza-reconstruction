import RainichKaluza.StagedKaluzaConverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Persistent detector channels to Phase-III acceptance

This file audits the seam between a literal actual-metric fourth-order
choice accepted throughout a patch and the two Phase-III exterior
obstructions.  The detector already retains the *complete* pulled-back seed
channel pair.  Once the propagated sine component is lifted to genuine
half-angle fields, that pair is the physical channel pair for the recovered
phase one-form.  Invertibility of the selected coframe then returns the two
channel equations to the coordinate frame.

The scalar-potential member of `PhaseIIIAcceptedBranch` is logically
separate.  The final packaging theorems therefore take precisely that scalar
fact, plus the exact identification of the chosen curvature branch covector
with the literal actual-metric scalar covector.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

private theorem fin4_sum_rotate4
    {R : Type*} [AddCommMonoid R]
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
      rw [Finset.sum_comm]

/-- Pulling a covariant three-tensor successively by `B` and then `A` is
pullback by `B * A`. -/
theorem pullThreeTensorToPrincipalFrame_comp
    (A B : Matrix4) (H : ThreeTensor4) :
    pullThreeTensorToPrincipalFrame A
        (pullThreeTensorToPrincipalFrame B H) =
      pullThreeTensorToPrincipalFrame (B * A) H := by
  ext a b c
  simp only [pullThreeTensorToPrincipalFrame, Matrix.mul_apply]
  calc
    (∑ x, ∑ y, ∑ z,
        A x a * A y b * A z c *
          (∑ i, ∑ j, ∑ k, B i x * B j y * B k z * H i j k)) =
        ∑ x, ∑ y, ∑ z, ∑ i, ∑ j, ∑ k,
          A x a * A y b * A z c *
            (B i x * B j y * B k z * H i j k) := by
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ x, ∑ y, ∑ z, ∑ j, ∑ k,
          A x a * A y b * A z c *
            (B i x * B j y * B k z * H i j k) := by
      exact fin4_sum_rotate4 (fun x y z i ↦ ∑ j, ∑ k,
        A x a * A y b * A z c *
          (B i x * B j y * B k z * H i j k))
    _ = ∑ i, ∑ j, ∑ x, ∑ y, ∑ z, ∑ k,
          A x a * A y b * A z c *
            (B i x * B j y * B k z * H i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact fin4_sum_rotate4 (fun x y z j ↦ ∑ k,
        A x a * A y b * A z c *
          (B i x * B j y * B k z * H i j k))
    _ = ∑ i, ∑ j, ∑ k, ∑ x, ∑ y, ∑ z,
          A x a * A y b * A z c *
            (B i x * B j y * B k z * H i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact fin4_sum_rotate4 (fun x y z k ↦
        A x a * A y b * A z c *
          (B i x * B j y * B k z * H i j k))
    _ = ∑ i, ∑ j, ∑ k, ∑ z, ∑ y, ∑ x,
          A x a * A y b * A z c *
            (B i x * B j y * B k z * H i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      calc
        (∑ x, ∑ y, ∑ z,
            A x a * A y b * A z c *
              (B i x * B j y * B k z * H i j k)) =
            ∑ x, ∑ z, ∑ y,
              A x a * A y b * A z c *
                (B i x * B j y * B k z * H i j k) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
        _ = ∑ z, ∑ x, ∑ y,
              A x a * A y b * A z c *
                (B i x * B j y * B k z * H i j k) := by
          rw [Finset.sum_comm]
        _ = ∑ z, ∑ y, ∑ x,
              A x a * A y b * A z c *
                (B i x * B j y * B k z * H i j k) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ k,
          (∑ x, B i x * A x a) *
            (∑ y, B j y * A y b) *
              (∑ z, B k z * A z c) * H i j k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- The identity matrix acts trivially on covariant three-tensors. -/
@[simp] theorem pullThreeTensorToPrincipalFrame_one
    (H : ThreeTensor4) :
    pullThreeTensorToPrincipalFrame (1 : Matrix4) H = H := by
  ext a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [pullThreeTensorToPrincipalFrame, Matrix.one_apply]

/-- Pullback by an invertible coframe map is injective. -/
theorem pullThreeTensorToPrincipalFrame_injective_of_mul_eq_one
    (L K : Matrix4) (hKL : K * L = 1) :
    Function.Injective (pullThreeTensorToPrincipalFrame K) := by
  intro H J h
  have hpushed := congrArg (pullThreeTensorToPrincipalFrame L) h
  rw [pullThreeTensorToPrincipalFrame_comp,
    pullThreeTensorToPrincipalFrame_comp, hKL] at hpushed
  simpa only [pullThreeTensorToPrincipalFrame_one] using hpushed

/-- Adding back the shear removed by `phaseOneFormFromEffectiveChannel`
recovers the supplied effective connection. -/
theorem effectiveComplexionOneForm_phaseOneFormFromEffectiveChannel
    (eta Jv : OneForm4) (B : ℝ) :
    effectiveComplexionOneForm
        (phaseOneFormFromEffectiveChannel eta Jv B) Jv B = eta := by
  funext i
  simp [effectiveComplexionOneForm, phaseOneFormFromEffectiveChannel]

/-- **Converse transported-channel bridge.**  For an invertible coframe, the
complete pulled-back physical seed-channel identity is not merely necessary
for EMD exterior closure: together with a unit complexion lift and its actual
phase first jets, it is sufficient for both exterior equations. -/
theorem emdExteriorClosure_of_transportedSeedChannels_eq_physical
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega : OneForm4) (a c s : ℝ)
    (dc ds : OneForm4)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hchannels :
      transportedPositiveQCanonicalSeedChannels L K dL q dq =
        canonicalPhysicalSeedChannels (Real.sqrt (2 * q))
          (pullCovectorToPrincipalFrame K v)
          (pullCovectorToPrincipalFrame K omega)
          (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s))) :
    let J := localPositiveQExteriorDualityJet
      L dL q dq c s dc ds
    EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
      (J.rotatedDF matrixOneWedgeTwo)
      (J.rotatedDG matrixOneWedgeTwo) := by
  let F0 := transportTwoForm L
    (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)
  let G0 := transportedPositiveQHodgeSeed L q
  let A := a * (c ^ 2 - s ^ 2)
  let B := a * (2 * c * s)
  have hinjective :=
    pullThreeTensorToPrincipalFrame_injective_of_mul_eq_one L K hKL
  have hchannelF := congrArg Prod.fst hchannels
  have hchannelG := congrArg Prod.snd hchannels
  dsimp only [transportedPositiveQCanonicalSeedChannels] at hchannelF hchannelG
  have hF0 : localPositiveQSeedExteriorDerivative L dL q dq =
      (A / 2) • matrixOneWedgeTwoTensor v F0 -
        matrixOneWedgeTwoTensor omega G0 +
          (B / 2) • matrixOneWedgeTwoTensor v G0 := by
    apply hinjective
    rw [hchannelF]
    dsimp only [F0, G0, transportedPositiveQHodgeSeed]
    simp only [pullThreeTensorToPrincipalFrame_add,
      pullThreeTensorToPrincipalFrame_sub,
      pullThreeTensorToPrincipalFrame_smul]
    simp only [pullThreeTensor_matrixOneWedgeTwoTensor_transport
      L K _ _ hLK]
    simp only [canonicalPhysicalSeedChannels, A, B]
  have hG0 : localPositiveQHodgeSeedExteriorDerivative L dL q dq =
      matrixOneWedgeTwoTensor omega F0 +
          (B / 2) • matrixOneWedgeTwoTensor v F0 -
        (A / 2) • matrixOneWedgeTwoTensor v G0 := by
    apply hinjective
    rw [hchannelG]
    dsimp only [F0, G0, transportedPositiveQHodgeSeed]
    simp only [pullThreeTensorToPrincipalFrame_add,
      pullThreeTensorToPrincipalFrame_sub,
      pullThreeTensorToPrincipalFrame_smul]
    simp only [pullThreeTensor_matrixOneWedgeTwoTensor_transport
      L K _ _ hLK]
    simp only [canonicalPhysicalSeedChannels, A, B]
  apply (localPositiveQ_emdClosure_iff_seedChannels
    L dL q dq omega v c s a dc ds hdc hds).2
  dsimp only [localPositiveQExteriorDualityJet,
    ExteriorDualityJet.rotatedSeedDF,
    ExteriorDualityJet.rotatedSeedDG,
    ExteriorDualityJet.rotatedF,
    ExteriorDualityJet.rotatedG]
  constructor
  · change c • localPositiveQSeedExteriorDerivative L dL q dq +
        s • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
      (a / 2) • matrixOneWedgeTwoTensor v (c • F0 + s • G0) -
        matrixOneWedgeTwoTensor omega ((-s) • F0 + c • G0)
    rw [hF0, hG0]
    ext i j k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.smul_apply, matrixOneWedgeTwoTensor]
    have hsquare : s ^ 2 = 1 - c ^ 2 := by linarith [hunit]
    simp only [A, B]
    ring_nf
    have hcube : s ^ 3 = s * (1 - c ^ 2) := by
      rw [show s ^ 3 = s * s ^ 2 by ring, hsquare]
    rw [hcube, hsquare]
    ring
  · change (-s) • localPositiveQSeedExteriorDerivative L dL q dq +
        c • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
      matrixOneWedgeTwoTensor omega (c • F0 + s • G0) -
        (a / 2) • matrixOneWedgeTwoTensor v ((-s) • F0 + c • G0)
    rw [hF0, hG0]
    ext i j k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.smul_apply, matrixOneWedgeTwoTensor]
    have hsquare : s ^ 2 = 1 - c ^ 2 := by linarith [hunit]
    simp only [A, B]
    ring_nf
    have hcube : s ^ 3 = s * (1 - c ^ 2) := by
      rw [show s ^ 3 = s * s ^ 2 by ring, hsquare]
    rw [hcube, hsquare]
    ring

namespace ActualMetricFixedChoicePhasePatchData

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}

/-- The complete detector channel pair is the physical channel pair of the
positive-cosine half-angle lift, provided the selected scalar branch really
is the literal actual-metric scalar covector. -/
theorem positiveCosine_transportedChannels_eq_physical
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalar : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    let M := D.positiveCosinePhaseIIIPatch hchart
    transportedPositiveQCanonicalSeedChannels
        (M.L z) (M.L z)⁻¹ (M.dL z) (M.q z) (M.dq z) =
      canonicalPhysicalSeedChannels (Real.sqrt (2 * M.q z))
        (pullCovectorToPrincipalFrame (M.L z)⁻¹
          (C.branchScalarOneFormValue branch z))
        (pullCovectorToPrincipalFrame (M.L z)⁻¹ (M.omega z))
        (M.coupling * (M.c z ^ 2 - M.s z ^ 2))
        (M.coupling * (2 * M.c z * M.s z)) := by
  let P := actualMetricFixedFourthOrderChannelPatch
    g choice D.accepted
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let K := fun y ↦ (L y)⁻¹
  let omegaP := fun y ↦ phaseOneFormFromEffectiveChannel
    (P.effectiveOneForm y) (P.reflectedScalarCovector y)
      (P.sineComponent y)
  let omega := ActualMetricFixedPhasePatch.coordinatePhaseOneForm
    g choice D.accepted
  let c := ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField
    g choice D.accepted
  let s := ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField
    g choice D.accepted
  have hLK : L z * K z = 1 := by
    simpa [L, K] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice (D.accepted z hz).1
  have hvpull : pullCovectorToPrincipalFrame (K z)
        (C.branchScalarOneFormValue branch z) = P.scalarCovector z := by
    rw [hscalar z hz]
    rfl
  have homegaPull : pullCovectorToPrincipalFrame (K z) (omega z) =
      omegaP z := by
    unfold omega ActualMetricFixedPhasePatch.coordinatePhaseOneForm
    rw [pullCovectorToPrincipalFrame_comp, hLK,
      pullCovectorToPrincipalFrame_one]
  have hspec := positiveCosineHalfAngle_spec (Real.sqrt 3)
    (P.cosineComponent z) (P.sineComponent z)
    (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
    (hchart z hz)
  have hA : P.cosineComponent z =
      Real.sqrt 3 * (c z ^ 2 - s z ^ 2) := by
    simpa [c, s,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField, P]
      using hspec.2.1
  have hB : P.sineComponent z =
      Real.sqrt 3 * (2 * c z * s z) := by
    calc
      P.sineComponent z =
          2 * Real.sqrt 3 * c z * s z := by
        simpa [c, s,
          ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField,
          ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField, P]
          using hspec.2.2
      _ = Real.sqrt 3 * (2 * c z * s z) := by ring
  have heta : effectiveComplexionOneForm (pullCovectorToPrincipalFrame
        (K z) (omega z))
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame (K z)
            (C.branchScalarOneFormValue branch z)))
        (Real.sqrt 3 * (2 * c z * s z)) = P.effectiveOneForm z := by
    rw [hvpull, homegaPull, ← hB]
    exact effectiveComplexionOneForm_phaseOneFormFromEffectiveChannel
      (P.effectiveOneForm z) (P.reflectedScalarCovector z)
        (P.sineComponent z)
  have heta' : effectiveComplexionOneForm
        (pullCovectorToPrincipalFrame (K z) (omega z))
        (canonicalPrincipalReflectionCovector (P.scalarCovector z))
        (Real.sqrt 3 * (2 * c z * s z)) = P.effectiveOneForm z := by
    simpa only [hvpull] using heta
  have hcomplete := P.completeChannels z hz
  let M := D.positiveCosinePhaseIIIPatch hchart
  change transportedPositiveQCanonicalSeedChannels
      (L z) (K z) (matrixFieldCoordinateFDeriv4 L z)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z)
      (scalarFieldCoordinateFDeriv
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z) = _
  calc
    transportedPositiveQCanonicalSeedChannels
        (L z) (K z) (matrixFieldCoordinateFDeriv4 L z)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z)
        (scalarFieldCoordinateFDeriv
          (positiveMaxwellMagnitudeFromSquare
            (actualRicciReconstructedQSqField4 g)) z) = P.channels z := by
      rfl
    _ = canonicalComplexionCouplingChannels
        (P.seedAmplitude z) (P.scalarCovector z)
        (P.effectiveOneForm z) (P.cosineComponent z) := hcomplete
    _ = canonicalPhysicalSeedChannels
        (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z))
        (pullCovectorToPrincipalFrame (K z)
          (C.branchScalarOneFormValue branch z))
        (pullCovectorToPrincipalFrame (K z) (omega z))
        (Real.sqrt 3 * (c z ^ 2 - s z ^ 2))
        (Real.sqrt 3 * (2 * c z * s z)) := by
      rw [canonicalPhysicalSeedChannels_eq_full]
      unfold canonicalFullComplexionCouplingChannels
      rw [hvpull, heta', ← hA]
      rfl

/-- Persistent literal detector acceptance supplies both Phase-III Maxwell
obstruction channels on the positive-cosine chart.  The only branch-specific
input is the exact identification of its scalar covector with the scalar
covector used by the detector. -/
theorem positiveCosine_branchObstructionsVanishOn
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalar : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z) :
    (D.positiveCosinePhaseIIIPatch hchart).BranchObstructionsVanishOn
      C branch := by
  let M := D.positiveCosinePhaseIIIPatch hchart
  apply (M.branchEMDExteriorClosureOn_iff_obstructionsVanishOn
    C branch).1
  intro z hz
  have hKL : (M.L z)⁻¹ * M.L z = 1 := by
    simpa only [M, positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice (D.accepted z hz).1
  have hLK : M.L z * (M.L z)⁻¹ = 1 := by
    simpa only [M, positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice (D.accepted z hz).1
  let P := actualMetricFixedFourthOrderChannelPatch
    g choice D.accepted
  have hspec := positiveCosineHalfAngle_spec (Real.sqrt 3)
    (P.cosineComponent z) (P.sineComponent z)
    (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
    (hchart z hz)
  have hunit : M.c z ^ 2 + M.s z ^ 2 = 1 := by
    simpa only [M, positiveCosinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveCosineHalfAngleSField, P]
      using hspec.1
  exact emdExteriorClosure_of_transportedSeedChannels_eq_physical
    (M.L z) (M.L z)⁻¹ (M.dL z) (M.q z) (M.dq z)
    (C.branchScalarOneFormValue branch z) (M.omega z)
    M.coupling (M.c z) (M.s z) (M.dc z) (M.ds z)
    hKL hLK hunit (M.dc_eq z hz) (M.ds_eq z hz)
    (D.positiveCosine_transportedChannels_eq_physical
      hchart C branch hscalar z hz)

/-- Full Phase-III acceptance on the positive-cosine chart.  Detector
acceptance proves the Maxwell member; scalar integrability remains exactly
the independent `BranchScalarPotentialExists` member of the structure. -/
theorem positiveCosine_phaseIIIAcceptedBranch
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalar : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hpotential : C.BranchScalarPotentialExists branch) :
    PhaseIIIAcceptedBranch C (D.positiveCosinePhaseIIIPatch hchart)
      branch :=
  ⟨hpotential,
    D.positiveCosine_branchObstructionsVanishOn
      hchart C branch hscalar⟩

/-! ### Positive-sine chart -/

/-- The complete detector channel pair is also the physical channel pair of
the complementary positive-sine half-angle lift. -/
theorem positiveSine_transportedChannels_eq_physical
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalar : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    let M := D.positiveSinePhaseIIIPatch hchart
    transportedPositiveQCanonicalSeedChannels
        (M.L z) (M.L z)⁻¹ (M.dL z) (M.q z) (M.dq z) =
      canonicalPhysicalSeedChannels (Real.sqrt (2 * M.q z))
        (pullCovectorToPrincipalFrame (M.L z)⁻¹
          (C.branchScalarOneFormValue branch z))
        (pullCovectorToPrincipalFrame (M.L z)⁻¹ (M.omega z))
        (M.coupling * (M.c z ^ 2 - M.s z ^ 2))
        (M.coupling * (2 * M.c z * M.s z)) := by
  let P := actualMetricFixedFourthOrderChannelPatch
    g choice D.accepted
  let L := actualMetricPrincipalCoframeCandidateField4 g choice
  let K := fun y ↦ (L y)⁻¹
  let omegaP := fun y ↦ phaseOneFormFromEffectiveChannel
    (P.effectiveOneForm y) (P.reflectedScalarCovector y)
      (P.sineComponent y)
  let omega := ActualMetricFixedPhasePatch.coordinatePhaseOneForm
    g choice D.accepted
  let c := ActualMetricFixedPhasePatch.positiveSineHalfAngleCField
    g choice D.accepted
  let s := ActualMetricFixedPhasePatch.positiveSineHalfAngleSField
    g choice D.accepted
  have hLK : L z * K z = 1 := by
    simpa [L, K] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice (D.accepted z hz).1
  have hvpull : pullCovectorToPrincipalFrame (K z)
        (C.branchScalarOneFormValue branch z) = P.scalarCovector z := by
    rw [hscalar z hz]
    rfl
  have homegaPull : pullCovectorToPrincipalFrame (K z) (omega z) =
      omegaP z := by
    unfold omega ActualMetricFixedPhasePatch.coordinatePhaseOneForm
    rw [pullCovectorToPrincipalFrame_comp, hLK,
      pullCovectorToPrincipalFrame_one]
  have hspec := positiveSineHalfAngle_spec (Real.sqrt 3)
    (P.cosineComponent z) (P.sineComponent z)
    (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
    (hchart z hz)
  have hA : P.cosineComponent z =
      Real.sqrt 3 * (c z ^ 2 - s z ^ 2) := by
    simpa [c, s,
      ActualMetricFixedPhasePatch.positiveSineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveSineHalfAngleSField, P]
      using hspec.2.1
  have hB : P.sineComponent z =
      Real.sqrt 3 * (2 * c z * s z) := by
    calc
      P.sineComponent z =
          2 * Real.sqrt 3 * c z * s z := by
        simpa [c, s,
          ActualMetricFixedPhasePatch.positiveSineHalfAngleCField,
          ActualMetricFixedPhasePatch.positiveSineHalfAngleSField, P]
          using hspec.2.2
      _ = Real.sqrt 3 * (2 * c z * s z) := by ring
  have heta : effectiveComplexionOneForm (pullCovectorToPrincipalFrame
        (K z) (omega z))
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame (K z)
            (C.branchScalarOneFormValue branch z)))
        (Real.sqrt 3 * (2 * c z * s z)) = P.effectiveOneForm z := by
    rw [hvpull, homegaPull, ← hB]
    exact effectiveComplexionOneForm_phaseOneFormFromEffectiveChannel
      (P.effectiveOneForm z) (P.reflectedScalarCovector z)
        (P.sineComponent z)
  have heta' : effectiveComplexionOneForm
        (pullCovectorToPrincipalFrame (K z) (omega z))
        (canonicalPrincipalReflectionCovector (P.scalarCovector z))
        (Real.sqrt 3 * (2 * c z * s z)) = P.effectiveOneForm z := by
    simpa only [hvpull] using heta
  have hcomplete := P.completeChannels z hz
  let M := D.positiveSinePhaseIIIPatch hchart
  change transportedPositiveQCanonicalSeedChannels
      (L z) (K z) (matrixFieldCoordinateFDeriv4 L z)
      (positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z)
      (scalarFieldCoordinateFDeriv
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g)) z) = _
  calc
    transportedPositiveQCanonicalSeedChannels
        (L z) (K z) (matrixFieldCoordinateFDeriv4 L z)
        (positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z)
        (scalarFieldCoordinateFDeriv
          (positiveMaxwellMagnitudeFromSquare
            (actualRicciReconstructedQSqField4 g)) z) = P.channels z := by
      rfl
    _ = canonicalComplexionCouplingChannels
        (P.seedAmplitude z) (P.scalarCovector z)
        (P.effectiveOneForm z) (P.cosineComponent z) := hcomplete
    _ = canonicalPhysicalSeedChannels
        (Real.sqrt (2 * positiveMaxwellMagnitudeFromSquare
          (actualRicciReconstructedQSqField4 g) z))
        (pullCovectorToPrincipalFrame (K z)
          (C.branchScalarOneFormValue branch z))
        (pullCovectorToPrincipalFrame (K z) (omega z))
        (Real.sqrt 3 * (c z ^ 2 - s z ^ 2))
        (Real.sqrt 3 * (2 * c z * s z)) := by
      rw [canonicalPhysicalSeedChannels_eq_full]
      unfold canonicalFullComplexionCouplingChannels
      rw [hvpull, heta', ← hA]
      rfl

/-- Persistent literal detector acceptance supplies both Phase-III Maxwell
obstruction channels on the positive-sine chart. -/
theorem positiveSine_branchObstructionsVanishOn
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalar : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z) :
    (D.positiveSinePhaseIIIPatch hchart).BranchObstructionsVanishOn
      C branch := by
  let M := D.positiveSinePhaseIIIPatch hchart
  apply (M.branchEMDExteriorClosureOn_iff_obstructionsVanishOn
    C branch).1
  intro z hz
  have hKL : (M.L z)⁻¹ * M.L z = 1 := by
    simpa only [M, positiveSinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice (D.accepted z hz).1
  have hLK : M.L z * (M.L z)⁻¹ = 1 := by
    simpa only [M, positiveSinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice (D.accepted z hz).1
  let P := actualMetricFixedFourthOrderChannelPatch
    g choice D.accepted
  have hspec := positiveSineHalfAngle_spec (Real.sqrt 3)
    (P.cosineComponent z) (P.sineComponent z)
    (Real.sqrt_pos.2 (by norm_num)) (D.couplingCircle z hz)
    (hchart z hz)
  have hunit : M.c z ^ 2 + M.s z ^ 2 = 1 := by
    simpa only [M, positiveSinePhaseIIIPatch,
      PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs,
      ActualMetricFixedPhasePatch.positiveSineHalfAngleCField,
      ActualMetricFixedPhasePatch.positiveSineHalfAngleSField, P]
      using hspec.1
  exact emdExteriorClosure_of_transportedSeedChannels_eq_physical
    (M.L z) (M.L z)⁻¹ (M.dL z) (M.q z) (M.dq z)
    (C.branchScalarOneFormValue branch z) (M.omega z)
    M.coupling (M.c z) (M.s z) (M.dc z) (M.ds z)
    hKL hLK hunit (M.dc_eq z hz) (M.ds_eq z hz)
    (D.positiveSine_transportedChannels_eq_physical
      hchart C branch hscalar z hz)

/-- Full Phase-III acceptance on the positive-sine chart. -/
theorem positiveSine_phaseIIIAcceptedBranch
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3)
    (C : CurvatureScalarBranchComponentPatch4 U)
    (branch : RelativeSignScalarBranch4)
    (hscalar : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (hpotential : C.BranchScalarPotentialExists branch) :
    PhaseIIIAcceptedBranch C (D.positiveSinePhaseIIIPatch hchart)
      branch :=
  ⟨hpotential,
    D.positiveSine_branchObstructionsVanishOn
      hchart C branch hscalar⟩

end ActualMetricFixedChoicePhasePatchData

end RainichKaluza
