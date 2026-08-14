import RainichKaluza.SourceDerivedPointwiseKaluzaRecognition
import RainichKaluza.NormalCoordinateHodgeFirstJet
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Core source-derived recognition with the Hodge equation derived

This module removes `hodgeExterior` from the input representative used by the
source-derived core endpoint.  The staged core's closed weighted Hodge flux,
the detector-selected coframe, and Minkowski normal-coordinate calculus derive
that equation instead.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

private theorem scalarFieldCoordinateFDeriv_mul_core_hodge
    (f h : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y * h y) z r =
      scalarFieldCoordinateFDeriv f z r * h z +
        f z * scalarFieldCoordinateFDeriv h z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f * h) z) _ = _
  rw [fderiv_mul hf hh]
  simp
  ring

/-- Source-derived core representative before imposing any EMD equation or
the exterior-Hodge law. -/
structure FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    K.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  scalar_germ : product.fields.phi =ᶠ[𝓝 x]
    K.physical.maxwell.scalarRepresentative
  potential_germ : product.fields.potential =ᶠ[𝓝 x]
    fun y i ↦ gaugePotential y (coordinateDirection i)
  metric_germ : product.fields.metric =ᶠ[𝓝 x]
    coordinateMetricMatrixField4 g
  diagonal_eq_minkowski : product.fields.diagonal = minkowskiSign

/-- The core already contains everything needed for the positively oriented
rotated Hodge-value identity; the omitted scalar residual is irrelevant. -/
theorem FixedChoiceStagedKaluzaConverseCore.rotatedG_eq_metricHodge_rotatedF
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    (M.exteriorJet z).rotatedG =
      coordinateMetricHodgeTwoForm4 (coordinateMetricMatrixField4 g z)
        (M.exteriorJet z).rotatedF := by
  rcases halign z hz with ⟨hL, hq⟩
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let Kinv := L⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  have hupstream : IsActualMetricUpstreamEntranceAt4 g z choice :=
    (D.accepted z hz).1
  have hmetric : coordinateMetricMatrixField4 g z =
      Lᵀ * minkowskiMetric * L := by
    simpa [L] using (K.coframe_reconstructs_metric z hz).symm
  have hKL : Kinv * L = 1 := by
    simpa [Kinv, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  have hLK : L * Kinv = 1 := by
    simpa [Kinv, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  have hdet : 0 < Matrix.det L := by
    simpa [L] using
      actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
        g z choice hupstream
  have hnatural := coordinateMetricHodgeTwoForm4_dualityRotation_of_det_pos
    (coordinateMetricMatrixField4 g z) L Kinv (Real.sqrt (2 * q))
      (M.c z) (M.s z) hmetric hKL hLK hdet
  rw [M.exteriorJet_rotatedF_eq_transport]
  unfold PositiveQPhaseIIIPatch4.exteriorJet
    localPositiveQExteriorDualityJet ExteriorDualityJet.rotatedG
    transportedPositiveQHodgeSeed
  rw [hL, hq]
  change (-M.s z) • transportTwoForm L
        (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
      M.c z • transportTwoForm L
        (canonicalHodgeStar (Real.sqrt (2 * q)) 0) = _
  rw [← transportTwoForm_smul, ← transportTwoForm_smul,
    ← transportTwoForm_add_detector]
  exact hnatural.symm

/-- Honest coordinate-metric Hodge dual of the convention physical Maxwell
matrix stored by the scalar-residual-free core. -/
noncomputable def coreStagedMetricHodgePhysicalMaxwellMatrix4
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  coordinateMetricHodgeTwoForm4 (coordinateMetricMatrixField4 g z)
    (K.conventionPhysicalMaxwellMatrix4 z)

/-- Patchwise core flux-value identity. -/
theorem FixedChoiceStagedKaluzaConverseCore.weightedHodgeFlux_eq_scaled_metricHodge
    {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {choice : ActualMetricDetectorChoice4}
    {x0 : CurvatureCoordinateSpace4}
    {C : CurvatureScalarBranchComponentPatch4 U}
    {M : PositiveQPhaseIIIPatch4 U}
    {branch : RelativeSignScalarBranch4}
    {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) (i j : Fin 4) :
    K.physical.weightedHodgeFlux z
        (coordinateDirection i) (coordinateDirection j) =
      normalWeightedHodgeFluxScale
          (K.physical.maxwell.scalarRepresentative z) *
        coreStagedMetricHodgePhysicalMaxwellMatrix4 K z i j := by
  let phiField := K.physical.maxwell.scalarRepresentative
  let phi := phiField z
  have hF : K.conventionPhysicalMaxwellMatrix4 z =
      (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) •
        (M.exteriorJet z).rotatedF := by
    ext a b
    simpa only [FixedChoiceStagedKaluzaConverseCore.conventionPhysicalMaxwellMatrix4,
      Matrix.smul_apply, smul_eq_mul, phiField, phi] using
      K.conventionMaxwell_matches_seed z hz a b
  have hseed := K.rotatedG_eq_metricHodge_rotatedF halign z hz
  have hHodge : coreStagedMetricHodgePhysicalMaxwellMatrix4 K z =
      (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) •
        (M.exteriorJet z).rotatedG := by
    unfold coreStagedMetricHodgePhysicalMaxwellMatrix4
    rw [hF]
    have hsmul : coordinateMetricHodgeTwoForm4
          (coordinateMetricMatrixField4 g z)
          ((Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) •
            (M.exteriorJet z).rotatedF) =
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) •
          coordinateMetricHodgeTwoForm4
            (coordinateMetricMatrixField4 g z)
              (M.exteriorJet z).rotatedF := by
      ext a b
      simp only [coordinateMetricHodgeTwoForm4, Matrix.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq'
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      ring
    rw [hsmul, ← hseed]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hweight : normalWeightedHodgeFluxScale phi *
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) =
      positiveEMDWeight M.coupling phiField z := by
    rw [K.coupling_eq]
    unfold normalWeightedHodgeFluxScale positiveEMDWeight
      negativeEMDWeight
    change Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2 *
        (Real.sqrt 2 * Real.exp (-(Real.sqrt 3 / 2) * phi)) =
      Real.exp (Real.sqrt 3 / 2 * phi)
    calc
      Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2 *
          (Real.sqrt 2 * Real.exp (-(Real.sqrt 3 / 2) * phi)) =
          Real.exp (Real.sqrt 3 * phi) *
            Real.exp (-(Real.sqrt 3 / 2) * phi) := by
        field_simp [hsqrt]
      _ = Real.exp
          (Real.sqrt 3 * phi + -(Real.sqrt 3 / 2) * phi) := by
        rw [Real.exp_add]
      _ = Real.exp (Real.sqrt 3 / 2 * phi) := by
        congr 1
        ring
  rw [K.physical.weightedHodgeFlux_matches_seed z hz i j, hHodge]
  simp only [Matrix.smul_apply, smul_eq_mul]
  change positiveEMDWeight M.coupling phiField z *
      (M.exteriorJet z).rotatedG i j = _
  calc
    positiveEMDWeight M.coupling phiField z *
        (M.exteriorJet z).rotatedG i j =
      (normalWeightedHodgeFluxScale phi *
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z)) *
          (M.exteriorJet z).rotatedG i j :=
      congrArg (fun t : ℝ ↦ t * (M.exteriorJet z).rotatedG i j)
        hweight.symm
    _ = normalWeightedHodgeFluxScale phi *
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z *
          (M.exteriorJet z).rotatedG i j) := by ring

namespace FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {K : FixedChoiceStagedKaluzaConverseCore D C M branch}
  {x : CurvatureCoordinateSpace4}

theorem coordinateMetric_eq_minkowski
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x) :
    coordinateMetricMatrixField4 g x = minkowskiMetric := by
  have hpoint := N.metric_germ.self_of_nhds
  calc
    coordinateMetricMatrixField4 g x = N.product.fields.metric x :=
      hpoint.symm
    _ = Matrix.diagonal N.product.fields.diagonal :=
      N.product.fields.metric_eq_diagonal
    _ = Matrix.diagonal minkowskiSign := by rw [N.diagonal_eq_minkowski]
    _ = minkowskiMetric := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [minkowskiMetric, minkowskiSign]

theorem coordinateMetric_firstJet_eq_zero
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x)
    (sigma mu nu : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateMetricMatrixField4 g y mu nu) x sigma = 0 := by
  have hcomponent :
      (fun y ↦ N.product.fields.metric y mu nu) =ᶠ[𝓝 x]
        (fun y ↦ coordinateMetricMatrixField4 g y mu nu) := by
    filter_upwards [N.metric_germ] with y hy
    exact congrFun (congrFun hy mu) nu
  unfold scalarFieldCoordinateFDeriv
  rw [← hcomponent.fderiv_eq]
  exact N.product.fields.metric_firstJet_eq_zero sigma mu nu

theorem phi0_eq_scalarRepresentative
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x) :
    N.product.fields.phi0 = K.physical.maxwell.scalarRepresentative x :=
  N.scalar_germ.self_of_nhds

theorem phi1_eq_actualMetricScalarOneForm
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x) :
    N.product.fields.phi1 =
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus x := by
  have hderiv : fderiv ℝ N.product.fields.phi x =
      fderiv ℝ K.physical.maxwell.scalarRepresentative x :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) N.scalar_germ
  funext sigma
  calc
    N.product.fields.phi1 sigma =
        fderiv ℝ N.product.fields.phi x
          (coordinateDirection sigma) := rfl
    _ = fderiv ℝ K.physical.maxwell.scalarRepresentative x
          (coordinateDirection sigma) := by rw [hderiv]
    _ = oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus x) (coordinateDirection sigma) := by
      rw [(K.scalarPotential_matches_metric x N.point_mem).fderiv]
    _ = actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus x sigma := by
      rw [oneForm4ContinuousLinearMap_coordinateDirection]

theorem gaugeCurvature_eq_conventionMaxwell
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x) :
    gaugeCurvatureOfFirstJet N.product.fields.A1 =
      K.conventionPhysicalMaxwellMatrix4 x := by
  have hAdiff : DifferentiableAt ℝ N.gaugePotential x :=
    (N.gaugePotential_is.1 x N.point_mem).differentiableAt
      (K.conventionMaxwell_closed.isOpen.mem_nhds N.point_mem)
  have hcomponent : ∀ mu,
      (fun y ↦ N.product.fields.potential y mu) =ᶠ[𝓝 x]
        (fun y ↦ N.gaugePotential y (coordinateDirection mu)) := by
    intro mu
    filter_upwards [N.potential_germ] with y hy
    exact congrFun hy mu
  have hderiv : ∀ mu,
      fderiv ℝ (fun y ↦ N.product.fields.potential y mu) x =
        fderiv ℝ (fun y ↦
          N.gaugePotential y (coordinateDirection mu)) x := by
    intro mu
    exact (hcomponent mu).fderiv_eq
  have heval : ∀ sigma mu,
      fderiv ℝ (fun y ↦
          N.gaugePotential y (coordinateDirection mu)) x
          (coordinateDirection sigma) =
        fderiv ℝ N.gaugePotential x (coordinateDirection sigma)
          (coordinateDirection mu) := by
    intro sigma mu
    rw [fderiv_clm_apply hAdiff (by fun_prop)]
    simp
  ext i j
  change N.product.fields.A1 i j - N.product.fields.A1 j i = _
  rw [show N.product.fields.A1 i j =
      fderiv ℝ (fun y ↦ N.product.fields.potential y j) x
        (coordinateDirection i) by rfl,
    show N.product.fields.A1 j i =
      fderiv ℝ (fun y ↦ N.product.fields.potential y i) x
        (coordinateDirection j) by rfl,
    hderiv j, hderiv i, heval i j, heval j i]
  exact N.gaugePotential_is.2 x N.point_mem
    (coordinateDirection i) (coordinateDirection j)

theorem gaugeCurvatureFirstJet_eq_conventionMaxwellDerivative
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x)
    (k i j : Fin 4) :
    gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k i j =
      K.physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) := by
  let pcomp := fun mu y ↦ N.product.fields.potential y mu
  let acomp := fun mu y ↦ N.gaugePotential y (coordinateDirection mu)
  let pcurv := fun y ↦
    fderiv ℝ (pcomp j) y (coordinateDirection i) -
      fderiv ℝ (pcomp i) y (coordinateDirection j)
  let acurv := fun y ↦
    fderiv ℝ (acomp j) y (coordinateDirection i) -
      fderiv ℝ (acomp i) y (coordinateDirection j)
  let Fcomp := fun y ↦
    K.physical.maxwell.conventionNormalizedPhysicalMaxwell y
      (coordinateDirection i) (coordinateDirection j)
  have hpot : ∀ mu, pcomp mu =ᶠ[𝓝 x] acomp mu := by
    intro mu
    filter_upwards [N.potential_germ] with y hy
    exact congrFun hy mu
  have hpotDeriv : ∀ mu,
      fderiv ℝ (pcomp mu) =ᶠ[𝓝 x] fderiv ℝ (acomp mu) := by
    intro mu
    exact (hpot mu).fderiv
  have hpcurv : pcurv =ᶠ[𝓝 x] acurv := by
    filter_upwards [hpotDeriv j, hpotDeriv i] with y hj hi
    simp only [pcurv, acurv]
    rw [hj, hi]
  have hacurv : acurv =ᶠ[𝓝 x] Fcomp := by
    filter_upwards [K.conventionMaxwell_closed.isOpen.mem_nhds N.point_mem]
      with y hy
    have hAdiff : DifferentiableAt ℝ N.gaugePotential y :=
      (N.gaugePotential_is.1 y hy).differentiableAt
        (K.conventionMaxwell_closed.isOpen.mem_nhds hy)
    have hiEval : fderiv ℝ (acomp j) y (coordinateDirection i) =
        fderiv ℝ N.gaugePotential y (coordinateDirection i)
          (coordinateDirection j) := by
      unfold acomp
      rw [fderiv_clm_apply hAdiff (by fun_prop)]
      simp
    have hjEval : fderiv ℝ (acomp i) y (coordinateDirection j) =
        fderiv ℝ N.gaugePotential y (coordinateDirection j)
          (coordinateDirection i) := by
      unfold acomp
      rw [fderiv_clm_apply hAdiff (by fun_prop)]
      simp
    unfold acurv Fcomp
    rw [hiEval, hjEval]
    exact N.gaugePotential_is.2 y hy
      (coordinateDirection i) (coordinateDirection j)
  have hcurv : pcurv =ᶠ[𝓝 x] Fcomp := hpcurv.trans hacurv
  have hcurvDeriv : fderiv ℝ pcurv x = fderiv ℝ Fcomp x :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hcurv
  have hpDiff : ∀ mu,
      DifferentiableAt ℝ (fderiv ℝ (pcomp mu)) x := by
    intro mu
    exact (((N.product.fields.potential_contDiffAt mu).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hpEvalDiff : ∀ mu rho,
      DifferentiableAt ℝ
        (fun y ↦ fderiv ℝ (pcomp mu) y (coordinateDirection rho)) x := by
    intro mu rho
    exact (hpDiff mu).clm_apply (by fun_prop)
  have hpcurvDeriv : fderiv ℝ pcurv x (coordinateDirection k) =
      N.product.fields.A2 k i j - N.product.fields.A2 k j i := by
    unfold pcurv
    rw [fderiv_fun_sub (hpEvalDiff j i) (hpEvalDiff i j)]
    rw [fderiv_clm_apply (hpDiff j) (by fun_prop),
      fderiv_clm_apply (hpDiff i) (by fun_prop)]
    simp [pcomp, KaluzaNormalGaugeFieldsAt.A2]
  have hFDeriv := hasFDerivAt_twoFormEvaluation
    (K.conventionMaxwell_closed.differentiable x N.point_mem)
      (coordinateDirection i) (coordinateDirection j)
  have hFcomponent : fderiv ℝ Fcomp x (coordinateDirection k) =
      K.physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) := by
    change fderiv ℝ (fun y ↦
      K.physical.maxwell.conventionNormalizedPhysicalMaxwell y
        (coordinateDirection i) (coordinateDirection j)) x
          (coordinateDirection k) = _
    rw [hFDeriv.fderiv]
    rfl
  calc
    gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k i j =
        N.product.fields.A2 k i j - N.product.fields.A2 k j i := rfl
    _ = fderiv ℝ pcurv x (coordinateDirection k) := hpcurvDeriv.symm
    _ = fderiv ℝ Fcomp x (coordinateDirection k) := by rw [hcurvDeriv]
    _ = _ := hFcomponent

end FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt

namespace FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {K : FixedChoiceStagedKaluzaConverseCore D C M branch}
  {x : CurvatureCoordinateSpace4}

/-- Exact core first-jet product rule, retained as a named intermediate for
downstream reuse. -/
def WeightedHodgeFluxFirstJetCompatible
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x) : Prop :=
  let r := normalWeightedHodgeFluxScale N.product.fields.phi0
  let F := gaugeCurvatureOfFirstJet N.product.fields.A1
  let DF := gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2
  let H := coordinateMetricHodgeTwoForm4 minkowskiMetric F
  let DH := fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k)
  ∀ k i j,
    K.physical.weightedHodgeFluxDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) =
      scaledTwoFormFirstJet r
        ((Real.sqrt 3 * r) • N.product.fields.phi1) H DH k i j

theorem weightedHodgeFluxFirstJetCompatible
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    N.WeightedHodgeFluxFirstJetCompatible := by
  let phiField := K.physical.maxwell.scalarRepresentative
  let GField := coordinateMetricMatrixField4 g
  let FField := K.conventionPhysicalMaxwellMatrix4
  let HField := coreStagedMetricHodgePhysicalMaxwellMatrix4 K
  have hGDiff : MatrixFieldDifferentiableAt4 GField x := by
    intro a b
    have hProductDiff : DifferentiableAt ℝ
        (fun y ↦ N.product.fields.metric y a b) x :=
      (N.product.fields.metric_contDiffAt a b).differentiableAt (by norm_num)
    have hcomponent :
        (fun y ↦ GField y a b) =ᶠ[𝓝 x]
          (fun y ↦ N.product.fields.metric y a b) := by
      filter_upwards [N.metric_germ] with y hy
      exact (congrFun (congrFun hy a) b).symm
    exact hProductDiff.congr_of_eventuallyEq hcomponent
  have hFDiff : ∀ a b, DifferentiableAt ℝ
      (fun y ↦ FField y a b) x := by
    intro a b
    exact (hasFDerivAt_twoFormEvaluation
      (K.conventionMaxwell_closed.differentiable x N.point_mem)
      (coordinateDirection a) (coordinateDirection b)).differentiableAt
  have hdet : Matrix.det (GField x) ≠ 0 := by
    rw [show GField x = minkowskiMetric from N.coordinateMetric_eq_minkowski,
      minkowskiMetric_det]
    norm_num
  have hHDiff : ∀ a b, DifferentiableAt ℝ
      (fun y ↦ HField y a b) x := by
    intro a b
    exact differentiableAt_coordinateMetricHodgeTwoForm4_apply
      GField FField x hGDiff hFDiff hdet a b
  have hphi : HasFDerivAt phiField
      (oneForm4ContinuousLinearMap N.product.fields.phi1) x := by
    have h := K.scalarPotential_matches_metric x N.point_mem
    rw [← N.phi1_eq_actualMetricScalarOneForm] at h
    exact h
  have hscale := hasFDerivAt_normalWeightedHodgeFluxScale hphi
  have hFJet (k : Fin 4) :
      matrixFieldCoordinateFDeriv4 FField x k =
        gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k := by
    ext a b
    have hEval := hasFDerivAt_twoFormEvaluation
      (K.conventionMaxwell_closed.differentiable x N.point_mem)
      (coordinateDirection a) (coordinateDirection b)
    have hStored : scalarFieldCoordinateFDeriv
        (fun y ↦ FField y a b) x k =
      K.physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative x
        (coordinateDirection k) (coordinateDirection a)
          (coordinateDirection b) := by
      unfold scalarFieldCoordinateFDeriv FField
        FixedChoiceStagedKaluzaConverseCore.conventionPhysicalMaxwellMatrix4
      rw [hEval.fderiv]
      rfl
    rw [show matrixFieldCoordinateFDeriv4 FField x k a b =
      scalarFieldCoordinateFDeriv (fun y ↦ FField y a b) x k by rfl,
      hStored]
    exact (N.gaugeCurvatureFirstJet_eq_conventionMaxwellDerivative
      k a b).symm
  have hHJet (k a b : Fin 4) :
      scalarFieldCoordinateFDeriv (fun y ↦ HField y a b) x k =
        coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k) a b := by
    have hnormal :=
      coordinateMetricHodgeTwoForm4_coordinateFDeriv_of_minkowskiNormal
        GField FField x hGDiff hFDiff N.coordinateMetric_eq_minkowski
        N.coordinateMetric_firstJet_eq_zero k a b
    rw [hFJet k] at hnormal
    exact hnormal
  have hHValue : HField x =
      coordinateMetricHodgeTwoForm4 minkowskiMetric
        (gaugeCurvatureOfFirstJet N.product.fields.A1) := by
    unfold HField coreStagedMetricHodgePhysicalMaxwellMatrix4
    rw [N.coordinateMetric_eq_minkowski,
      ← N.gaugeCurvature_eq_conventionMaxwell]
  have hScaleValue : normalWeightedHodgeFluxScale (phiField x) =
      normalWeightedHodgeFluxScale N.product.fields.phi0 := by
    rw [N.phi0_eq_scalarRepresentative]
  intro k i j
  let Wcomp := fun y ↦ K.physical.weightedHodgeFlux y
    (coordinateDirection i) (coordinateDirection j)
  let scaledHcomp := fun y ↦
    normalWeightedHodgeFluxScale (phiField y) * HField y i j
  have hfield : Wcomp =ᶠ[𝓝 x] scaledHcomp := by
    filter_upwards [K.weightedHodgeFlux_closed.isOpen.mem_nhds N.point_mem]
      with y hy
    exact K.weightedHodgeFlux_eq_scaled_metricHodge halign y hy i j
  have hWcoord : scalarFieldCoordinateFDeriv Wcomp x k =
      K.physical.weightedHodgeFluxDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) := by
    have hEval := hasFDerivAt_twoFormEvaluation
      (K.weightedHodgeFlux_closed.differentiable x N.point_mem)
      (coordinateDirection i) (coordinateDirection j)
    unfold scalarFieldCoordinateFDeriv Wcomp
    rw [hEval.fderiv]
    rfl
  have hderivEq : scalarFieldCoordinateFDeriv Wcomp x k =
      scalarFieldCoordinateFDeriv scaledHcomp x k := by
    unfold scalarFieldCoordinateFDeriv
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hfield]
  have hscaleDiff : DifferentiableAt ℝ
      (fun y ↦ normalWeightedHodgeFluxScale (phiField y)) x :=
    hscale.differentiableAt
  have hscaleJet : scalarFieldCoordinateFDeriv
      (fun y ↦ normalWeightedHodgeFluxScale (phiField y)) x k =
        (Real.sqrt 3 * normalWeightedHodgeFluxScale (phiField x)) *
          N.product.fields.phi1 k := by
    unfold scalarFieldCoordinateFDeriv
    rw [hscale.fderiv]
    simp only [smul_apply, smul_eq_mul,
      oneForm4ContinuousLinearMap_curvatureCoordinateDirection]
  rw [← hWcoord, hderivEq]
  unfold scaledHcomp
  rw [scalarFieldCoordinateFDeriv_mul_core_hodge]
  · rw [hscaleJet, hHJet k i j, hScaleValue, hHValue]
    simp only [scaledTwoFormFirstJet, Matrix.add_apply, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul]
  · exact hscaleDiff
  · exact hHDiff i j

/-- Core closedness plus the automatic first-jet identity gives the literal
normal exterior-Hodge law. -/
theorem hodgeExterior
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    matrixExteriorDerivative
        (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k)) =
      -(Real.sqrt 3) • matrixOneWedgeTwoTensor N.product.fields.phi1
        (coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet N.product.fields.A1)) := by
  exact matrixHodgeExterior_of_closed_scaledFirstJet
    K.weightedHodgeFlux_closed N.point_mem
    (coordinateMetricHodgeTwoForm4 minkowskiMetric
      (gaugeCurvatureOfFirstJet N.product.fields.A1))
    (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
      (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k))
    N.product.fields.phi1 (Real.sqrt 3)
    (normalWeightedHodgeFluxScale N.product.fields.phi0)
    (normalWeightedHodgeFluxScale_ne_zero N.product.fields.phi0)
    (N.weightedHodgeFluxFirstJetCompatible halign)

/-- Promote the equation-free core representative to the existing
source-derived Hodge representative. -/
def toSourceDerivedHodgeRepresentative
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    FixedChoiceCoreSourceDerivedHodgeRepresentativeAt K x where
  point_mem := N.point_mem
  gaugePotential := N.gaugePotential
  gaugePotential_is := N.gaugePotential_is
  product := N.product
  scalar_germ := N.scalar_germ
  potential_germ := N.potential_germ
  metric_germ := N.metric_germ
  diagonal_eq_minkowski := N.diagonal_eq_minkowski
  hodgeExterior := N.hodgeExterior halign

end FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt

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
  {x : CurvatureCoordinateSpace4}

/-- Strongest core-entrance endpoint with both Einstein and Hodge equations
derived rather than stored by the input representative. -/
theorem exists_completeSourceDerivedPointwiseKaluzaRecognition_of_preHodgeCoreEntrance
    (K : FixedChoiceStagedKaluzaConverseCore D C M branch)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M)
    (H : FixedChoiceNormalMatterJetDerivationAt K x)
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt K x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition K
      ((N.toSourceDerivedHodgeRepresentative halign).toHodgeRepresentative
        (H.withCoreEinsteinSource halign N.point_mem)).toDivergenceRepresentative) :=
  K.exists_completeSourceDerivedPointwiseKaluzaRecognition_of_coreEntrance
    halign H (N.toSourceDerivedHodgeRepresentative halign)

end FixedChoiceStagedKaluzaConverseCore

/-! ## Positive-cosine detector-channel endpoint -/

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 x : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- Persistent positive-cosine detector channels now require only the
equation-free pre-Hodge source-derived representative.  The core entrance
derives Einstein, weighted-flux closedness derives exterior Hodge and Maxwell
divergence, and the existing Noether bridge derives the scalar equation. -/
theorem exists_completeSourceDerivedPointwiseKaluzaRecognition_positiveCosineDetectorChannels_of_preHodge
    (D : ActualMetricFixedChoicePhasePatchData U g choice x0)
    (hchart : ∀ y ∈ U,
      (actualMetricFixedFourthOrderChannelPatch
        g choice D.accepted).cosineComponent y ≠ -Real.sqrt 3)
    (hscalarPotential : C.BranchScalarPotentialExists branch)
    (hscalarMatchesMetric : ∀ z ∈ U,
      C.branchScalarOneFormValue branch z =
        actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus z)
    (H : FixedChoiceNormalMatterJetDerivationAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x)
    (N : FixedChoiceCoreSourceDerivedPreHodgeRepresentativeAt
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric) x) :
    Nonempty (CompletePointwiseCoreKaluzaRecognition
      (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
        D hchart hscalarPotential hscalarMatchesMetric)
      ((N.toSourceDerivedHodgeRepresentative
          (FixedChoiceStagedKaluzaConverseBoundary.ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch_seedAlignment
            D hchart)).toHodgeRepresentative
        (H.withCoreEinsteinSource
          (FixedChoiceStagedKaluzaConverseBoundary.ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch_seedAlignment
            D hchart)
          N.point_mem)).toDivergenceRepresentative) :=
  FixedChoiceStagedKaluzaConverseCore.exists_completeSourceDerivedPointwiseKaluzaRecognition_of_preHodgeCoreEntrance
    (FixedChoiceStagedKaluzaConverseCore.ofPositiveCosineChartDetectorChannels
      D hchart hscalarPotential hscalarMatchesMetric)
    (FixedChoiceStagedKaluzaConverseBoundary.ActualMetricFixedChoicePhasePatchData.positiveCosinePhaseIIIPatch_seedAlignment
      D hchart) H N

end RainichKaluza
