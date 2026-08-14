import RainichKaluza.StagedKaluzaConverse
import RainichKaluza.EinsteinSourceFirstJetBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Staged converse to the actual Einstein source

This file closes the algebraic normalization step between the staged
fixed-choice converse and the honest metric-dependent matter source.

The Phase-III seed is the curvature-normalized field
`H = exp(a phi / 2) F / sqrt 2`.  Its Maxwell stress is shown to equal the
actual metric Maxwell residual by transporting the unit duality circle
through the selected coframe.  Combining that equality with the scalar
rank-one entrance split gives the literal covariant Einstein/source identity.

For a boundary with an abstract `PositiveQPhaseIIIPatch4` parameter, the
necessary identification of its `L` and `q` fields with the actual selected
coframe and reconstructed magnitude is exposed as
`StagedSeedEntranceAlignmentOn`.  Both concrete half-angle patches satisfy
this alignment definitionally.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

/-! ## Physical normalization -/

/-- Coordinate matrix of the convention-normalized physical Maxwell field
stored in a staged boundary. -/
noncomputable def stagedConventionPhysicalMaxwellMatrix4
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  fun i j ↦ B.physical.maxwell.conventionNormalizedPhysicalMaxwell z
    (coordinateDirection i) (coordinateDirection j)

/-- The curvature-normalized Maxwell matrix
`H = exp(a phi / 2) F / sqrt 2` reconstructed from the convention field. -/
noncomputable def stagedCurvatureNormalizedPhysicalMaxwellMatrix4
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  (positiveEMDWeight M.coupling
      B.physical.maxwell.scalarRepresentative z / Real.sqrt 2) •
    stagedConventionPhysicalMaxwellMatrix4 B z

namespace FixedChoiceStagedKaluzaConverseBoundary

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}

/-- Undoing the convention normalization recovers exactly the Phase-III
curvature seed, including the `sqrt 2` and exponential factors. -/
theorem stagedCurvatureNormalizedPhysicalMaxwellMatrix4_eq_rotatedF
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B z =
      (M.exteriorJet z).rotatedF := by
  have hweight :
      positiveEMDWeight M.coupling
          B.physical.maxwell.scalarRepresentative z *
        negativeEMDWeight M.coupling
          B.physical.maxwell.scalarRepresentative z = 1 := by
    unfold positiveEMDWeight negativeEMDWeight
    rw [← Real.exp_add]
    rw [show M.coupling / 2 * B.physical.maxwell.scalarRepresentative z +
        -(M.coupling / 2) * B.physical.maxwell.scalarRepresentative z = 0 by
      ring]
    exact Real.exp_zero
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  unfold stagedCurvatureNormalizedPhysicalMaxwellMatrix4
    stagedConventionPhysicalMaxwellMatrix4
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [B.conventionMaxwell_matches_seed z hz i j]
  calc
    (positiveEMDWeight M.coupling
          B.physical.maxwell.scalarRepresentative z / Real.sqrt 2) *
        (Real.sqrt 2 *
          negativeEMDWeight M.coupling
            B.physical.maxwell.scalarRepresentative z *
          (M.exteriorJet z).rotatedF i j) =
      (positiveEMDWeight M.coupling
          B.physical.maxwell.scalarRepresentative z *
        negativeEMDWeight M.coupling
          B.physical.maxwell.scalarRepresentative z) *
        (M.exteriorJet z).rotatedF i j := by
      field_simp [hsqrt]
    _ = (M.exteriorJet z).rotatedF i j := by rw [hweight]; simp

/-! ## The exact abstract seed-alignment seam -/

/-- The Phase-III patch uses the actual selected principal coframe and the
positive magnitude reconstructed from the actual Ricci tensor.  This is
definitionally true for both concrete half-angle patches, but is not a field
of the abstract staged-boundary structure. -/
def StagedSeedEntranceAlignmentOn
    (_D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (M : PositiveQPhaseIIIPatch4 U) : Prop :=
  ∀ z ∈ U,
    M.L z = actualMetricPrincipalCoframeCandidateField4 g choice z ∧
      M.q z = positiveMaxwellMagnitudeFromSquare
        (actualRicciReconstructedQSqField4 g) z

/-- The concrete positive-cosine Phase-III patch has the required entrance
alignment by construction. -/
theorem ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch_seedAlignment
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ -Real.sqrt 3) :
    StagedSeedEntranceAlignmentOn D (D.positiveCosinePhaseIIIPatch hchart) := by
  intro z hz
  exact ⟨rfl, rfl⟩

/-- The concrete positive-sine Phase-III patch has the required entrance
alignment by construction. -/
theorem ActualMetricFixedChoicePhasePatchData.positiveSinePhaseIIIPatch_seedAlignment
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ x ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent x ≠ Real.sqrt 3) :
    StagedSeedEntranceAlignmentOn D (D.positiveSinePhaseIIIPatch hchart) := by
  intro z hz
  exact ⟨rfl, rfl⟩

end FixedChoiceStagedKaluzaConverseBoundary

/-! ## Maxwell-stress transport for a unit duality rotation -/

/-- A unit rotation of the positive canonical seed has the same canonical
Maxwell residual. -/
theorem matrixMaxwellStress_canonical_unitRotation
    (q c s : ℝ) (hq : 0 < q) (hcircle : c ^ 2 + s ^ 2 = 1) :
    matrixMaxwellStress minkowskiMetric
        (c • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          s • canonicalHodgeStar (Real.sqrt (2 * q)) 0) =
      canonicalMaxwellResidual q := by
  let E := Real.sqrt (2 * q)
  have hform :
      c • canonicalMaxwellTwoForm E 0 + s • canonicalHodgeStar E 0 =
        canonicalMaxwellTwoForm (c * E) (s * E) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalHodgeStar, canonicalMaxwellTwoForm]
  have hskew :
      (c • canonicalMaxwellTwoForm E 0 +
          s • canonicalHodgeStar E 0)ᵀ =
        -(c • canonicalMaxwellTwoForm E 0 +
          s • canonicalHodgeStar E 0) := by
    rw [hform]
    exact canonicalMaxwellTwoForm_transpose _ _
  apply (matrixMaxwellStress_eq_canonicalResidual_iff_amplitudeCircle
    _ q hskew).2
  refine ⟨c * E, s * E, ?_, hform⟩
  have hE : E ^ 2 = 2 * q := by
    dsimp [E]
    rw [Real.sq_sqrt]
    positivity
  nlinarith

/-- General-basis form of the same unit-circle stress identity. -/
theorem matrixMaxwellStress_transport_unitRotation
    (G L K : Matrix4) (q c s : ℝ)
    (hG : G = Lᵀ * minkowskiMetric * L)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hq : 0 < q) (hcircle : c ^ 2 + s ^ 2 = 1) :
    matrixMaxwellStress G⁻¹
        (transportTwoForm L
          (c • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
            s • canonicalHodgeStar (Real.sqrt (2 * q)) 0)) =
      transportMixed K (canonicalMaxwellResidual q) L := by
  rw [inverse_metric_congruence G L K hG hKL hLK]
  rw [matrixMaxwellStress_changeBasis minkowskiMetric K L
    (c • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
      s • canonicalHodgeStar (Real.sqrt (2 * q)) 0) hLK hKL]
  rw [matrixMaxwellStress_canonical_unitRotation q c s hq hcircle]

/-! ## Algebraic identification with the source conventions -/

/-- In four dimensions the ordinary mixed Maxwell stress is tracefree. -/
theorem matrixMaxwellStress_trace_zero (G F : Matrix4) :
    Matrix.trace (matrixMaxwellStress G F) = 0 := by
  unfold matrixMaxwellStress
  simp [Matrix.trace, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
/-- For a symmetric inverse metric and an alternating covariant two-form,
the coordinate-index source formula is exactly `matrixMaxwellStress`. -/
theorem coordinateMaxwellEinsteinStressMixed4_eq_matrixMaxwellStress
    (GInv F : Matrix4) (hGInv : GInvᵀ = GInv) (hF : Fᵀ = -F) :
    coordinateMaxwellEinsteinStressMixed4 GInv F =
      matrixMaxwellStress GInv F := by
  have hGentry (i j : Fin 4) : GInv j i = GInv i j := by
    have h := congrArg (fun A : Matrix4 ↦ A i j) hGInv
    simpa only [Matrix.transpose_apply] using h
  rw [eq_lorentzSkewTwoForm4_of_transpose_eq_neg F hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMaxwellEinsteinStressMixed4,
      coordinateRaisedTwoForm4, matrixMaxwellStress,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ,
      lorentzSkewTwoForm4, hGentry] <;>
    ring

/-- The staged rank-one scalar contribution becomes the trace-adjusted
scalar Einstein source after subtracting one half of its mixed trace. -/
theorem coordinateScalarEinsteinStressMixed4_eq_scalarContribution_sub_trace
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    coordinateScalarEinsteinStressMixed4 (gInv z) (v z) =
      scalarContributionMatrixField gInv v z -
        ((1 / 2 : ℝ) * scalarContributionTraceField gInv v z) •
          (1 : Matrix4) := by
  have hcontribution (i j : Fin 4) :
      scalarContributionMatrixField gInv v z i j =
        (1 / 2 : ℝ) * coordinateRaisedOneForm4 (gInv z) (v z) i * v z j := by
    unfold scalarContributionMatrixField scalarRaisedVector
      coordinateRaisedOneForm4
    simp only [Matrix.mulVec, dotProduct]
    ring
  have htrace : scalarContributionTraceField gInv v z =
      (1 / 2 : ℝ) * ∑ k,
        coordinateRaisedOneForm4 (gInv z) (v z) k * v z k := by
    unfold scalarContributionTraceField oneForm4Evaluate
      scalarRaisedVector coordinateRaisedOneForm4
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [hcontribution, htrace]
  unfold coordinateScalarEinsteinStressMixed4
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]

/-- The named scalar trace field is literally the matrix trace of the
rank-one mixed scalar contribution. -/
theorem scalarContributionMatrixField_trace
    {X : Type*} (gInv : X → Matrix4) (v : X → OneForm4) (z : X) :
    Matrix.trace (scalarContributionMatrixField gInv v z) =
      scalarContributionTraceField gInv v z := by
  unfold Matrix.trace scalarContributionMatrixField
    scalarContributionTraceField oneForm4Evaluate
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The value part of every local positive-`q` exterior jet is a transported
canonical duality rotation. -/
theorem PositiveQPhaseIIIPatch4.exteriorJet_rotatedF_eq_transport
    {U : Set CurvatureCoordinateSpace4}
    (M : PositiveQPhaseIIIPatch4 U) (z : CurvatureCoordinateSpace4) :
    (M.exteriorJet z).rotatedF =
      transportTwoForm (M.L z)
        (M.c z • canonicalMaxwellTwoForm (Real.sqrt (2 * M.q z)) 0 +
          M.s z • canonicalHodgeStar (Real.sqrt (2 * M.q z)) 0) := by
  unfold PositiveQPhaseIIIPatch4.exteriorJet
    localPositiveQExteriorDualityJet ExteriorDualityJet.rotatedF
    transportedPositiveQHodgeSeed
  rw [← transportTwoForm_smul, ← transportTwoForm_smul,
    ← transportTwoForm_add_detector]

/-- Consequently the curvature-normalized seed is an honest alternating
two-form, independently of the differential Phase-III channels. -/
theorem PositiveQPhaseIIIPatch4.exteriorJet_rotatedF_transpose
    {U : Set CurvatureCoordinateSpace4}
    (M : PositiveQPhaseIIIPatch4 U) (z : CurvatureCoordinateSpace4) :
    ((M.exteriorJet z).rotatedF)ᵀ = -(M.exteriorJet z).rotatedF := by
  rw [M.exteriorJet_rotatedF_eq_transport]
  apply transportTwoForm_transpose
  have hcanonical :
      M.c z • canonicalMaxwellTwoForm (Real.sqrt (2 * M.q z)) 0 +
          M.s z • canonicalHodgeStar (Real.sqrt (2 * M.q z)) 0 =
        canonicalMaxwellTwoForm
          (M.c z * Real.sqrt (2 * M.q z))
          (M.s z * Real.sqrt (2 * M.q z)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonicalHodgeStar, canonicalMaxwellTwoForm]
  rw [hcanonical]
  exact canonicalMaxwellTwoForm_transpose _ _

/-- Contracting a symmetric covariant tensor with an inverse metric is the
trace of the corresponding mixed matrix. -/
theorem coordinateContraction_eq_trace_mul_of_symmetric
    (GInv Ric : Matrix4) (hRic : Ricᵀ = Ric) :
    (∑ i, ∑ j, GInv i j * Ric i j) = Matrix.trace (GInv * Ric) := by
  have hRicEntry (i j : Fin 4) : Ric j i = Ric i j := by
    have h := congrArg (fun A : Matrix4 ↦ A i j) hRic
    simpa only [Matrix.transpose_apply] using h
  simp [Matrix.trace, Matrix.mul_apply, hRicEntry]

namespace FixedChoiceStagedKaluzaConverseBoundary

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}

/-- **Normalized physical Maxwell stress equals the actual residual.**
The convention field is first rescaled to
`H = exp(a phi / 2) F / sqrt 2`; its ordinary Maxwell stress is then exactly
the metric-reconstructed residual. -/
theorem curvatureNormalizedPhysicalMaxwellStress_eq_actualMetricResidual
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (halign : StagedSeedEntranceAlignmentOn D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    matrixMaxwellStress (coordinateMetricMatrixField4 g z)⁻¹
        (stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B z) =
      actualMetricMaxwellResidualCandidateField4 g choice z := by
  rw [B.stagedCurvatureNormalizedPhysicalMaxwellMatrix4_eq_rotatedF z hz]
  rcases halign z hz with ⟨hLalign, hqalign⟩
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let K := L⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  have hupstream : IsActualMetricUpstreamEntranceAt4 g z choice :=
    (D.accepted z hz).1
  have hKL : K * L = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  have hLK : L * K = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  have hmetric : coordinateMetricMatrixField4 g z =
      Lᵀ * minkowskiMetric * L := by
    simpa [L] using (B.coframe_reconstructs_metric z hz).symm
  have hqpos : 0 < q := by
    simpa [q] using D.magnitude_pos z hz
  have hrotated : (M.exteriorJet z).rotatedF =
      transportTwoForm L
        (M.c z • canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          M.s z • canonicalHodgeStar (Real.sqrt (2 * q)) 0) := by
    unfold PositiveQPhaseIIIPatch4.exteriorJet
      localPositiveQExteriorDualityJet ExteriorDualityJet.rotatedF
      transportedPositiveQHodgeSeed
    rw [hLalign, hqalign]
    change M.c z • transportTwoForm L
          (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
        M.s z • transportTwoForm L
          (canonicalHodgeStar (Real.sqrt (2 * q)) 0) = _
    rw [← transportTwoForm_smul, ← transportTwoForm_smul,
      ← transportTwoForm_add_detector]
  rw [hrotated]
  rw [matrixMaxwellStress_transport_unitRotation
    (coordinateMetricMatrixField4 g z) L K q (M.c z) (M.s z)
    hmetric hKL hLK hqpos (B.phaseCircle z hz)]
  rw [← B.residual_is_canonical_in_selected_frame z hz]
  change K * (L * actualMetricMaxwellResidualCandidateField4 g choice z * K) *
      L = actualMetricMaxwellResidualCandidateField4 g choice z
  calc
    K * (L * actualMetricMaxwellResidualCandidateField4 g choice z * K) * L =
        (K * L) * actualMetricMaxwellResidualCandidateField4 g choice z *
          (K * L) := by noncomm_ring
    _ = actualMetricMaxwellResidualCandidateField4 g choice z := by
      rw [hKL]
      simp

/-- **Pointwise Einstein/source identity from the staged entrance.**  Once
the abstract Phase-III seed is aligned with the detector's actual coframe and
magnitude, the staged Ricci split and normalized Maxwell stress give the
literal covariant Einstein equation used by the first-jet bridge. -/
theorem actualCoordinateEinsteinField4_eq_actualMatterSource
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (halign : StagedSeedEntranceAlignmentOn D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    actualCoordinateEinsteinField4 g z =
      actualCoordinateMatterEinsteinStressCovariantField4 g
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        (stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B) z := by
  let G : Matrix4 := coordinateMetricMatrixField4 g z
  let Ric : Matrix4 := actualCoordinateRicciCovariantField4 g z
  let R : Matrix4 := actualMixedRicciField4 g z
  let vField := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  let V : Matrix4 := actualMetricScalarContributionCandidateField4 g choice z
  let S : Matrix4 := actualMetricMaxwellResidualCandidateField4 g choice z
  let H : Matrix4 := stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B z
  let traceV : ℝ := scalarContributionTraceField
    (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹) vField z
  have hupstream : IsActualMetricUpstreamEntranceAt4 g z choice :=
    (D.accepted z hz).1
  have halgebraic := hupstream.1
  unfold IsActualMetricAlgebraicEntranceAt4 at halgebraic
  dsimp only at halgebraic
  have hGsym : Gᵀ = G := by simpa [G] using halgebraic.1
  have hright : G * G⁻¹ = 1 := by
    simpa [G] using halgebraic.2.2.1
  have hGRsym : (G * R)ᵀ = G * R := by
    simpa [G, R] using halgebraic.2.2.2.1
  have hGInvSym : G⁻¹ᵀ = G⁻¹ :=
    inverseMatrix_transpose_eq_self_of_symmetric G G⁻¹ hGsym hright
  have hRicEq : G * R = Ric := by
    dsimp [G, R, Ric]
    unfold actualMixedRicciField4
    rw [← Matrix.mul_assoc, hright, Matrix.one_mul]
  have hRicSym : Ricᵀ = Ric := by
    rw [← hRicEq]
    exact hGRsym
  have hScalar : actualCoordinateScalarCurvatureField4 g z =
      Matrix.trace R := by
    unfold actualCoordinateScalarCurvatureField4
    rw [coordinateContraction_eq_trace_mul_of_symmetric
      (coordinateMetricMatrixField4 g z)⁻¹
      (actualCoordinateRicciCovariantField4 g z)]
    · rfl
    · simpa [Ric] using hRicSym
  have hsplit : S + V = R := by
    simpa [S, V, R] using B.ricci_entrance_split z hz
  have hstress : matrixMaxwellStress G⁻¹ H = S := by
    simpa [G, H, S] using
      B.curvatureNormalizedPhysicalMaxwellStress_eq_actualMetricResidual
        halign z hz
  have hHskew : Hᵀ = -H := by
    dsimp [H]
    rw [B.stagedCurvatureNormalizedPhysicalMaxwellMatrix4_eq_rotatedF z hz]
    exact M.exteriorJet_rotatedF_transpose z
  have htraceS : Matrix.trace S = 0 := by
    rw [← hstress]
    exact matrixMaxwellStress_trace_zero G⁻¹ H
  have htraceR : Matrix.trace R = traceV := by
    calc
      Matrix.trace R = Matrix.trace (S + V) :=
        congrArg Matrix.trace hsplit.symm
      _ = Matrix.trace S + Matrix.trace V := by
        simp [Matrix.trace, Finset.sum_add_distrib]
      _ = Matrix.trace V := by rw [htraceS]; simp
      _ = traceV := by
        simpa [V, actualMetricScalarContributionCandidateField4,
          traceV, vField] using
          scalarContributionMatrixField_trace
            (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹) vField z
  have hscalarSource : coordinateScalarEinsteinStressMixed4 G⁻¹ (vField z) =
      V - ((1 / 2 : ℝ) * traceV) • (1 : Matrix4) := by
    change coordinateScalarEinsteinStressMixed4
        (coordinateMetricMatrixField4 g z)⁻¹ (vField z) =
      scalarContributionMatrixField
          (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹) vField z -
        ((1 / 2 : ℝ) * traceV) • (1 : Matrix4)
    simpa [traceV] using
      coordinateScalarEinsteinStressMixed4_eq_scalarContribution_sub_trace
        (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹) vField z
  have hmaxwellSource : coordinateMaxwellEinsteinStressMixed4 G⁻¹ H = S := by
    rw [coordinateMaxwellEinsteinStressMixed4_eq_matrixMaxwellStress
      G⁻¹ H hGInvSym hHskew]
    exact hstress
  have hmatter : coordinateMatterEinsteinStressMixed4 G⁻¹ (vField z) H =
      R - ((1 / 2 : ℝ) * Matrix.trace R) • (1 : Matrix4) := by
    unfold coordinateMatterEinsteinStressMixed4
    rw [hscalarSource, hmaxwellSource, htraceR, ← hsplit]
    module
  calc
    actualCoordinateEinsteinField4 g z =
        Ric - (actualCoordinateScalarCurvatureField4 g z / 2) • G := by
      ext i j
      unfold actualCoordinateEinsteinField4
      simp [G, Ric]
      ring
    _ = G * R - (Matrix.trace R / 2) • G := by
      rw [hScalar, hRicEq]
    _ = G * (R - ((1 / 2 : ℝ) * Matrix.trace R) • (1 : Matrix4)) := by
      rw [mul_sub, mul_smul_comm, Matrix.mul_one]
      congr 1
      ring_nf
    _ = G * coordinateMatterEinsteinStressMixed4 G⁻¹ (vField z) H := by
      rw [hmatter]
    _ = actualCoordinateMatterEinsteinStressCovariantField4 g vField
        (stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B) z := by
      ext i j
      unfold actualCoordinateMatterEinsteinStressCovariantField4
        coordinateMatterEinsteinStressCovariant4
      rw [Matrix.mul_apply]

/-- Patchwise pointwise entrance immediately gives the neighborhood equality
required by the source first-jet theorem at every interior point. -/
theorem actualCoordinateEinsteinField4_eventuallyEq_actualMatterSource
    (B : FixedChoiceStagedKaluzaConverseBoundary D C M branch)
    (halign : StagedSeedEntranceAlignmentOn D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    actualCoordinateEinsteinField4 g =ᶠ[nhds z]
      actualCoordinateMatterEinsteinStressCovariantField4 g
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        (stagedCurvatureNormalizedPhysicalMaxwellMatrix4 B) := by
  filter_upwards [D.isOpen.mem_nhds hz] with y hy
  exact B.actualCoordinateEinsteinField4_eq_actualMatterSource
    halign y hy

end FixedChoiceStagedKaluzaConverseBoundary

end RainichKaluza
