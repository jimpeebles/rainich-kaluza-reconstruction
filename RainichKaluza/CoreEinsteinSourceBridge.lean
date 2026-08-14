import RainichKaluza.ScalarResidualFreeStagedKaluzaConverse
import RainichKaluza.StagedEinsteinSourceBridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Scalar-residual-free staged Einstein/source bridge

The algebraic Einstein/source identity in `StagedEinsteinSourceBridge` does
not use the scalar wave equation, but its statements are parameterized by the
older boundary which stores that equation.  This module adapts the compiled
normalization and entrance argument to
`FixedChoiceStagedKaluzaConverseCore`.

Consequently a core supplies the honest pointwise covariant Einstein/source
identity, and its patchwise entrance supplies the neighborhood equality
needed by the first-jet normal Noether bridge, before any scalar residual has
been assumed or derived.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

namespace FixedChoiceStagedKaluzaConverseCore

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}

/-- Undoing convention normalization in the pre-scalar core recovers exactly
the Phase-III curvature-normalized seed. -/
theorem curvatureNormalizedPhysicalMaxwellMatrix4_eq_rotatedF
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    K.curvatureNormalizedPhysicalMaxwellMatrix4 z =
      (M.exteriorJet z).rotatedF := by
  have hweight :
      positiveEMDWeight M.coupling
          K.physical.maxwell.scalarRepresentative z *
        negativeEMDWeight M.coupling
          K.physical.maxwell.scalarRepresentative z = 1 := by
    unfold positiveEMDWeight negativeEMDWeight
    rw [← Real.exp_add]
    rw [show M.coupling / 2 * K.physical.maxwell.scalarRepresentative z +
        -(M.coupling / 2) * K.physical.maxwell.scalarRepresentative z = 0 by
      ring]
    exact Real.exp_zero
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  unfold curvatureNormalizedPhysicalMaxwellMatrix4
    conventionPhysicalMaxwellMatrix4
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [K.conventionMaxwell_matches_seed z hz i j]
  calc
    (positiveEMDWeight M.coupling
          K.physical.maxwell.scalarRepresentative z / Real.sqrt 2) *
        (Real.sqrt 2 *
          negativeEMDWeight M.coupling
            K.physical.maxwell.scalarRepresentative z *
          (M.exteriorJet z).rotatedF i j) =
      (positiveEMDWeight M.coupling
          K.physical.maxwell.scalarRepresentative z *
        negativeEMDWeight M.coupling
          K.physical.maxwell.scalarRepresentative z) *
        (M.exteriorJet z).rotatedF i j := by
      field_simp [hsqrt]
    _ = (M.exteriorJet z).rotatedF i j := by rw [hweight]; simp

/-- The core's curvature-normalized Maxwell stress is the actual metric
residual.  The proof uses only seed alignment, the unit phase circle, and the
algebraic entrance fields retained by the core. -/
theorem curvatureNormalizedPhysicalMaxwellStress_eq_actualMetricResidual
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    matrixMaxwellStress (coordinateMetricMatrixField4 g z)⁻¹
        (K.curvatureNormalizedPhysicalMaxwellMatrix4 z) =
      actualMetricMaxwellResidualCandidateField4 g choice z := by
  rw [K.curvatureNormalizedPhysicalMaxwellMatrix4_eq_rotatedF z hz]
  rcases halign z hz with ⟨hLalign, hqalign⟩
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let Linv := L⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  have hupstream : IsActualMetricUpstreamEntranceAt4 g z choice :=
    (D.accepted z hz).1
  have hKL : Linv * L = 1 := by
    simpa [Linv, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  have hLK : L * Linv = 1 := by
    simpa [Linv, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  have hmetric : coordinateMetricMatrixField4 g z =
      Lᵀ * minkowskiMetric * L := by
    simpa [L] using (K.coframe_reconstructs_metric z hz).symm
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
    (coordinateMetricMatrixField4 g z) L Linv q (M.c z) (M.s z)
    hmetric hKL hLK hqpos (K.phaseCircle z hz)]
  rw [← K.residual_is_canonical_in_selected_frame z hz]
  change Linv *
      (L * actualMetricMaxwellResidualCandidateField4 g choice z * Linv) *
      L = actualMetricMaxwellResidualCandidateField4 g choice z
  calc
    Linv *
        (L * actualMetricMaxwellResidualCandidateField4 g choice z * Linv) *
        L =
      (Linv * L) * actualMetricMaxwellResidualCandidateField4 g choice z *
        (Linv * L) := by noncomm_ring
    _ = actualMetricMaxwellResidualCandidateField4 g choice z := by
      rw [hKL]
      simp

/-- **Pointwise Einstein/source identity from the pre-scalar core.**  No
scalar wave equation occurs in the assumptions or proof. -/
theorem actualCoordinateEinsteinField4_eq_actualMatterSource
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    actualCoordinateEinsteinField4 g z =
      actualCoordinateMatterEinsteinStressCovariantField4 g
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        K.curvatureNormalizedPhysicalMaxwellMatrix4 z := by
  let G : Matrix4 := coordinateMetricMatrixField4 g z
  let Ric : Matrix4 := actualCoordinateRicciCovariantField4 g z
  let R : Matrix4 := actualMixedRicciField4 g z
  let vField := actualMetricScalarOneFormCandidateField4 g
    choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
    choice.relativeMinus
  let V : Matrix4 := actualMetricScalarContributionCandidateField4 g choice z
  let S : Matrix4 := actualMetricMaxwellResidualCandidateField4 g choice z
  let H : Matrix4 := K.curvatureNormalizedPhysicalMaxwellMatrix4 z
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
    simpa [S, V, R] using K.ricci_entrance_split z hz
  have hstress : matrixMaxwellStress G⁻¹ H = S := by
    simpa [G, H, S] using
      K.curvatureNormalizedPhysicalMaxwellStress_eq_actualMetricResidual
        halign z hz
  have hHskew : Hᵀ = -H := by
    dsimp [H]
    rw [K.curvatureNormalizedPhysicalMaxwellMatrix4_eq_rotatedF z hz]
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
        K.curvatureNormalizedPhysicalMaxwellMatrix4 z := by
      ext i j
      unfold actualCoordinateMatterEinsteinStressCovariantField4
        coordinateMatterEinsteinStressCovariant4
      rw [Matrix.mul_apply]

/-- Patchwise entrance gives the neighborhood Einstein/source equality at
every interior point, still without a scalar-residual assumption. -/
theorem actualCoordinateEinsteinField4_eventuallyEq_actualMatterSource
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    actualCoordinateEinsteinField4 g =ᶠ[nhds z]
      actualCoordinateMatterEinsteinStressCovariantField4 g
        (actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus)
        K.curvatureNormalizedPhysicalMaxwellMatrix4 := by
  filter_upwards [D.isOpen.mem_nhds hz] with y hy
  exact K.actualCoordinateEinsteinField4_eq_actualMatterSource
    halign y hy

end FixedChoiceStagedKaluzaConverseCore

end RainichKaluza
