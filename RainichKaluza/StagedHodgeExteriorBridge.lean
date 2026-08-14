import RainichKaluza.GeometricFixedChoiceKaluzaRecognition
import RainichKaluza.StagedEinsteinSourceBridge
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Staged closed Hodge flux to the normal exterior-Hodge equation

This module isolates the remaining first-jet seam between the closed weighted
Hodge flux constructed by Phase III and the literal curvature jet of a `C²`
normal/radial-gauge product representative.

The value-level Hodge identification is already forced by the accepted
actual-metric detector, its positively oriented coframe, and the staged seed
alignment.  At first-jet level the missing datum is stated as one exact
product-rule equality.  From that equality, closedness of the staged weighted
flux proves the exterior equation

`d(*F) = -sqrt(3) dphi ∧ (*F)`

with no Maxwell-divergence hypothesis.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

/-- A closed Frechet-derivative package whose coordinate first jet is a
nonzero scalar multiple of a Hodge jet forces the unweighted exterior-Hodge
equation.  This is the finite-dimensional product-rule cancellation used by
the staged bridge below. -/
theorem matrixHodgeExterior_of_closed_scaledFirstJet
    {U : Set CurvatureCoordinateSpace4}
    {W : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {DW : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ]
        ContinuousBilinForm CurvatureCoordinateSpace4}
    {x : CurvatureCoordinateSpace4}
    (hclosed : IsC1ClosedTwoFormOn W DW U) (hx : x ∈ U)
    (H : Matrix4) (DH : Fin 4 → Matrix4) (v : OneForm4)
    (a r : ℝ) (hr : r ≠ 0)
    (hfirstJet : ∀ k i j,
      DW x (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) =
        scaledTwoFormFirstJet r ((a * r) • v) H DH k i j) :
    matrixExteriorDerivative DH =
      (-a) • matrixOneWedgeTwoTensor v H := by
  have hscaled : matrixExteriorDerivative
      (scaledTwoFormFirstJet r ((a * r) • v) H DH) = 0 := by
    ext k i j
    have h := hclosed.closed x hx
      (coordinateDirection k) (coordinateDirection i)
        (coordinateDirection j)
    rw [hfirstJet k i j, hfirstJet i j k, hfirstJet j k i] at h
    simpa only [matrixExteriorDerivative, Pi.zero_apply] using h
  rw [matrixExteriorDerivative_scaledTwoFormFirstJet] at hscaled
  ext k i j
  have hcomponent := congrArg (fun T : ThreeTensor4 ↦ T k i j) hscaled
  simp only [scaledTwoFormExteriorDerivative, matrixOneWedgeTwo,
    LinearMap.coe_mk, AddHom.coe_mk, map_smul, LinearMap.smul_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    matrixOneWedgeTwoTensor] at hcomponent ⊢
  have hfactor : r *
      (matrixExteriorDerivative DH k i j +
        a * (v k * H i j + v i * H j k + v j * H k i)) = 0 := by
    linear_combination hcomponent
  have hinner := (mul_eq_zero.mp hfactor).resolve_left hr
  linarith

/-- The value of the rotated Hodge seed is the actual coordinate-metric
Hodge star of the rotated Maxwell seed.  No downstream Hodge assumption is
needed: persistent detector acceptance selects positive orientation, and
`StagedSeedEntranceAlignmentOn` identifies the abstract Phase-III frame and
magnitude with that detector entrance. -/
theorem FixedChoiceStagedKaluzaConverseBoundary.rotatedG_eq_metricHodge_rotatedF
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
    (halign : StagedSeedEntranceAlignmentOn D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) :
    (M.exteriorJet z).rotatedG =
      coordinateMetricHodgeTwoForm4 (coordinateMetricMatrixField4 g z)
        (M.exteriorJet z).rotatedF := by
  rcases halign z hz with ⟨hL, hq⟩
  let L := actualMetricPrincipalCoframeCandidateField4 g choice z
  let K := L⁻¹
  let q := positiveMaxwellMagnitudeFromSquare
    (actualRicciReconstructedQSqField4 g) z
  have hupstream : IsActualMetricUpstreamEntranceAt4 g z choice :=
    (D.accepted z hz).1
  have hmetric : coordinateMetricMatrixField4 g z =
      Lᵀ * minkowskiMetric * L := by
    simpa [L] using (B.coframe_reconstructs_metric z hz).symm
  have hKL : K * L = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_inv_mul_of_upstream
        g z choice hupstream
  have hLK : L * K = 1 := by
    simpa [K, L] using
      actualMetricPrincipalCoframeCandidate_mul_inv_of_upstream
        g z choice hupstream
  have hdet : 0 < Matrix.det L := by
    simpa [L] using
      actualMetricPrincipalCoframeCandidate_det_pos_of_upstream
        g z choice hupstream
  have hnatural := coordinateMetricHodgeTwoForm4_dualityRotation_of_det_pos
    (coordinateMetricMatrixField4 g z) L K (Real.sqrt (2 * q))
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

/-- The nonzero scalar relating the Phase-III weighted Hodge flux to the
Hodge dual of the convention-normalized physical Maxwell field:
`exp(sqrt(3) phi) / sqrt(2)`. -/
noncomputable def normalWeightedHodgeFluxScale (phi : ℝ) : ℝ :=
  Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2

theorem normalWeightedHodgeFluxScale_ne_zero (phi : ℝ) :
    normalWeightedHodgeFluxScale phi ≠ 0 := by
  unfold normalWeightedHodgeFluxScale
  exact div_ne_zero (Real.exp_ne_zero _) (by positivity)

/-- Coordinate-metric Hodge dual of the convention-normalized physical
Maxwell matrix retained by a staged boundary. -/
noncomputable def stagedMetricHodgePhysicalMaxwellMatrix4
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
  coordinateMetricHodgeTwoForm4 (coordinateMetricMatrixField4 g z)
    (stagedConventionPhysicalMaxwellMatrix4 B z)

/-- Patchwise value identity behind the bridge: the closed flux constructed
by Phase III is the scalar-weighted metric Hodge dual of the convention
Maxwell field. -/
theorem FixedChoiceStagedKaluzaConverseBoundary.weightedHodgeFlux_eq_scaled_metricHodge
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
    (halign : StagedSeedEntranceAlignmentOn D M)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U) (i j : Fin 4) :
    B.physical.weightedHodgeFlux z
        (coordinateDirection i) (coordinateDirection j) =
      normalWeightedHodgeFluxScale
          (B.physical.maxwell.scalarRepresentative z) *
        stagedMetricHodgePhysicalMaxwellMatrix4 B z i j := by
  let phiField := B.physical.maxwell.scalarRepresentative
  let phi := phiField z
  have hF : stagedConventionPhysicalMaxwellMatrix4 B z =
      (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) •
        (M.exteriorJet z).rotatedF := by
    ext a b
    simpa only [stagedConventionPhysicalMaxwellMatrix4,
      Matrix.smul_apply, smul_eq_mul, phiField, phi] using
      B.conventionMaxwell_matches_seed z hz a b
  have hseed := B.rotatedG_eq_metricHodge_rotatedF halign z hz
  have hHodge : stagedMetricHodgePhysicalMaxwellMatrix4 B z =
      (Real.sqrt 2 * negativeEMDWeight M.coupling phiField z) •
        (M.exteriorJet z).rotatedG := by
    unfold stagedMetricHodgePhysicalMaxwellMatrix4
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
      intro q hq
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
    rw [B.coupling_eq]
    unfold normalWeightedHodgeFluxScale positiveEMDWeight
      negativeEMDWeight
    change Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2 *
        (Real.sqrt 2 * Real.exp (-(Real.sqrt 3 / 2) * phi)) =
      Real.exp (Real.sqrt 3 / 2 * phi)
    calc
      Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2 *
          (Real.sqrt 2 *
            Real.exp (-(Real.sqrt 3 / 2) * phi)) =
          Real.exp (Real.sqrt 3 * phi) *
            Real.exp (-(Real.sqrt 3 / 2) * phi) := by
        field_simp [hsqrt]
      _ = Real.exp
          (Real.sqrt 3 * phi + -(Real.sqrt 3 / 2) * phi) := by
        rw [Real.exp_add]
      _ = Real.exp (Real.sqrt 3 / 2 * phi) := by
        congr 1
        ring
  rw [B.physical.weightedHodgeFlux_matches_seed z hz i j, hHodge]
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

/-! ## Compatible normal product germ -/

/-- The common geometric part of a Minkowski normal/radial-gauge
representative, before imposing any Maxwell equation.  Its `product` already
contains genuine componentwise `C²` fields and the zero base-metric first jet.
-/
structure FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt
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
    (x : CurvatureCoordinateSpace4) where
  point_mem : x ∈ U
  gaugePotential : CurvatureCoordinateSpace4 →
    CurvatureCoordinateSpace4 →L[ℝ] ℝ
  gaugePotential_is : IsGaugePotentialOn gaugePotential
    B.physical.maxwell.conventionNormalizedPhysicalMaxwell U
  product : LorentzianKaluzaLocalProductGermAt x
  scalar_germ : product.fields.phi =ᶠ[𝓝 x]
    B.physical.maxwell.scalarRepresentative
  potential_germ : product.fields.potential =ᶠ[𝓝 x]
    fun y i ↦ gaugePotential y (coordinateDirection i)
  metric_germ : product.fields.metric =ᶠ[𝓝 x]
    coordinateMetricMatrixField4 g
  diagonal_eq_minkowski : product.fields.diagonal = minkowskiSign
  einstein : NormalGaugeEinsteinEquations product
  scalarResidual : normalGaugeScalarEquationResidual product =
    actualMetricScalarEquationResidualCandidateAt4 g choice x

namespace FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt

variable {U : Set CurvatureCoordinateSpace4}
  {g : CurvatureCoordinateSpace4 →
    ContinuousBilinForm CurvatureCoordinateSpace4}
  {choice : ActualMetricDetectorChoice4}
  {x0 : CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}
  {D : ActualMetricFixedChoicePhasePatchData U g choice x0}
  {B : FixedChoiceStagedKaluzaConverseBoundary D C M branch}
  {x : CurvatureCoordinateSpace4}

/-- The product normal-coordinate metric value and its germ identification
force the recognized coordinate metric itself to be Minkowski at the base
point. -/
theorem coordinateMetric_eq_minkowski
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) :
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

/-- The metric germ also transfers the product's normal-coordinate zero
first jet to the recognized coordinate metric.  These are precisely the
metric hypotheses under which differentiating the coordinate Hodge star has
no metric-variation term. -/
theorem coordinateMetric_firstJet_eq_zero
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
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

/-- The scalar germ identifies the product's extracted first-order base value
with the staged scalar representative. -/
theorem phi0_eq_scalarRepresentative
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) :
    N.product.fields.phi0 =
      B.physical.maxwell.scalarRepresentative x := by
  exact N.scalar_germ.self_of_nhds

/-- The scalar germ and the staged scalar-potential derivative identify the
product's literal first scalar jet with the detector's actual-metric scalar
covector. -/
theorem phi1_eq_actualMetricScalarOneForm
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) :
    N.product.fields.phi1 =
      actualMetricScalarOneFormCandidateField4 g
        choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
        choice.relativeMinus x := by
  have hderiv : fderiv ℝ N.product.fields.phi x =
      fderiv ℝ B.physical.maxwell.scalarRepresentative x :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) N.scalar_germ
  funext sigma
  calc
    N.product.fields.phi1 sigma =
        fderiv ℝ N.product.fields.phi x
          (coordinateDirection sigma) := rfl
    _ = fderiv ℝ B.physical.maxwell.scalarRepresentative x
          (coordinateDirection sigma) := by rw [hderiv]
    _ = oneForm4ContinuousLinearMap
          (actualMetricScalarOneFormCandidateField4 g
            choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
            choice.relativeMinus x) (coordinateDirection sigma) := by
      rw [(B.scalarPotential_matches_metric x N.point_mem).fderiv]
    _ = actualMetricScalarOneFormCandidateField4 g
          choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
          choice.relativeMinus x sigma := by
      rw [oneForm4ContinuousLinearMap_coordinateDirection]

/-- The compatible gauge-potential germ identifies the literal curvature of
the product's first potential jet with the staged convention-normalized
physical Maxwell field at the base point. -/
theorem gaugeCurvature_eq_stagedConventionMaxwell
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) :
    gaugeCurvatureOfFirstJet N.product.fields.A1 =
      stagedConventionPhysicalMaxwellMatrix4 B x := by
  have hAdiff : DifferentiableAt ℝ N.gaugePotential x :=
    (N.gaugePotential_is.1 x N.point_mem).differentiableAt
      (B.conventionMaxwell_closed.isOpen.mem_nhds N.point_mem)
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

/-- Differentiating the compatible potential germ identifies the product's
literal curvature first jet with the staged convention-Maxwell derivative.
Thus the gauge part of the remaining Hodge first-jet seam is automatic. -/
theorem gaugeCurvatureFirstJet_eq_stagedConventionMaxwellDerivative
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (k i j : Fin 4) :
    gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k i j =
      B.physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative x
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
    B.physical.maxwell.conventionNormalizedPhysicalMaxwell y
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
    filter_upwards [B.conventionMaxwell_closed.isOpen.mem_nhds N.point_mem]
      with y hy
    have hAdiff : DifferentiableAt ℝ N.gaugePotential y :=
      (N.gaugePotential_is.1 y hy).differentiableAt
        (B.conventionMaxwell_closed.isOpen.mem_nhds hy)
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
    (B.conventionMaxwell_closed.differentiable x N.point_mem)
      (coordinateDirection i) (coordinateDirection j)
  have hFcomponent : fderiv ℝ Fcomp x (coordinateDirection k) =
      B.physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) := by
    change fderiv ℝ (fun y ↦
      B.physical.maxwell.conventionNormalizedPhysicalMaxwell y
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

/-- Value-level compatibility is not an additional hypothesis.  Seed
alignment, detector-selected positive orientation, and the scalar/potential/
metric germs identify the staged weighted flux with

`(exp(sqrt(3) phi) / sqrt(2)) * (*F)`

at the normal point. -/
theorem weightedHodgeFlux_value_eq_scaled_productHodge
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) (i j : Fin 4) :
    B.physical.weightedHodgeFlux x
        (coordinateDirection i) (coordinateDirection j) =
      normalWeightedHodgeFluxScale N.product.fields.phi0 *
        coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet N.product.fields.A1) i j := by
  let phiField := B.physical.maxwell.scalarRepresentative
  let phi := phiField x
  have hF : gaugeCurvatureOfFirstJet N.product.fields.A1 =
      (Real.sqrt 2 * negativeEMDWeight M.coupling phiField x) •
        (M.exteriorJet x).rotatedF := by
    rw [N.gaugeCurvature_eq_stagedConventionMaxwell]
    ext a b
    simpa only [stagedConventionPhysicalMaxwellMatrix4,
      Matrix.smul_apply, smul_eq_mul, phiField, phi] using
      B.conventionMaxwell_matches_seed x N.point_mem a b
  have hseed := B.rotatedG_eq_metricHodge_rotatedF
    halign x N.point_mem
  rw [N.coordinateMetric_eq_minkowski] at hseed
  have hHodge : coordinateMetricHodgeTwoForm4 minkowskiMetric
        (gaugeCurvatureOfFirstJet N.product.fields.A1) =
      (Real.sqrt 2 * negativeEMDWeight M.coupling phiField x) •
        (M.exteriorJet x).rotatedG := by
    rw [hF, coordinateMetricHodgeTwoForm4_minkowski_smul, ← hseed]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hweight : normalWeightedHodgeFluxScale N.product.fields.phi0 *
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField x) =
      positiveEMDWeight M.coupling phiField x := by
    rw [N.phi0_eq_scalarRepresentative]
    rw [B.coupling_eq]
    unfold normalWeightedHodgeFluxScale positiveEMDWeight
      negativeEMDWeight
    change Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2 *
        (Real.sqrt 2 * Real.exp (-(Real.sqrt 3 / 2) * phi)) =
      Real.exp (Real.sqrt 3 / 2 * phi)
    calc
      Real.exp (Real.sqrt 3 * phi) / Real.sqrt 2 *
          (Real.sqrt 2 *
            Real.exp (-(Real.sqrt 3 / 2) * phi)) =
          Real.exp (Real.sqrt 3 * phi) *
            Real.exp (-(Real.sqrt 3 / 2) * phi) := by
        field_simp [hsqrt]
      _ = Real.exp
          (Real.sqrt 3 * phi + -(Real.sqrt 3 / 2) * phi) := by
        rw [Real.exp_add]
      _ = Real.exp (Real.sqrt 3 / 2 * phi) := by
        congr 1
        ring
  rw [B.physical.weightedHodgeFlux_matches_seed x N.point_mem i j,
    hHodge]
  simp only [Matrix.smul_apply, smul_eq_mul]
  change positiveEMDWeight M.coupling phiField x *
      (M.exteriorJet x).rotatedG i j = _
  calc
    positiveEMDWeight M.coupling phiField x *
        (M.exteriorJet x).rotatedG i j =
      (normalWeightedHodgeFluxScale N.product.fields.phi0 *
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField x)) *
          (M.exteriorJet x).rotatedG i j :=
      congrArg (fun t : ℝ ↦ t * (M.exteriorJet x).rotatedG i j)
        hweight.symm
    _ = normalWeightedHodgeFluxScale N.product.fields.phi0 *
        (Real.sqrt 2 * (negativeEMDWeight M.coupling phiField x *
          (M.exteriorJet x).rotatedG i j)) := by ring
    _ = normalWeightedHodgeFluxScale N.product.fields.phi0 *
        (Real.sqrt 2 * negativeEMDWeight M.coupling phiField x *
          (M.exteriorJet x).rotatedG i j) := by ring

/-- Exact remaining first-jet splice.  The right side is the product-rule
first jet of

`(exp(sqrt(3) phi) / sqrt(2)) * (*F)`.

The fixed Minkowski Hodge map on the curvature first jet is the correct
normal-coordinate derivative because `product.fields.metric_firstJet_eq_zero`
is part of the `C²` product package.  Establishing that general coordinate
Hodge differentiation formula is the only analytic tensor-calculus seam not
duplicated here. -/
def WeightedHodgeFluxFirstJetCompatible
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x) : Prop :=
  let r := normalWeightedHodgeFluxScale N.product.fields.phi0
  let F := gaugeCurvatureOfFirstJet N.product.fields.A1
  let DF := gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2
  let H := coordinateMetricHodgeTwoForm4 minkowskiMetric F
  let DH := fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric (DF k)
  ∀ k i j,
    B.physical.weightedHodgeFluxDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) =
      scaledTwoFormFirstJet r
        ((Real.sqrt 3 * r) • N.product.fields.phi1) H DH k i j

/-- Closedness of the staged weighted Hodge flux, together with the exact
normal first-jet compatibility above, proves the literal exterior-Hodge
equation for the product gauge curvature. -/
theorem hodgeExterior
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (hjet : N.WeightedHodgeFluxFirstJetCompatible) :
    matrixExteriorDerivative
        (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k)) =
      -(Real.sqrt 3) • matrixOneWedgeTwoTensor N.product.fields.phi1
        (coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet N.product.fields.A1)) := by
  exact matrixHodgeExterior_of_closed_scaledFirstJet
    B.weightedHodgeFlux_closed N.point_mem
    (coordinateMetricHodgeTwoForm4 minkowskiMetric
      (gaugeCurvatureOfFirstJet N.product.fields.A1))
    (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
      (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k))
    N.product.fields.phi1 (Real.sqrt 3)
    (normalWeightedHodgeFluxScale N.product.fields.phi0)
    (normalWeightedHodgeFluxScale_ne_zero N.product.fields.phi0)
    hjet

/-- Promote the equation-free compatible `C²` product germ to the existing
exterior-Hodge representative.  No divergence or mixed Kaluza Ricci equation
is assumed. -/
def toHodgeNormalGaugeRepresentative
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (hjet : N.WeightedHodgeFluxFirstJetCompatible) :
    FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt B x where
  point_mem := N.point_mem
  gaugePotential := N.gaugePotential
  gaugePotential_is := N.gaugePotential_is
  product := N.product
  scalar_germ := N.scalar_germ
  potential_germ := N.potential_germ
  metric_germ := N.metric_germ
  diagonal_eq_minkowski := N.diagonal_eq_minkowski
  einstein := N.einstein
  hodgeExterior := N.hodgeExterior hjet
  scalarResidual := N.scalarResidual

end FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt

end RainichKaluza
