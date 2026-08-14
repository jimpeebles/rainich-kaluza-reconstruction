import RainichKaluza.StagedHodgeExteriorBridge
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The coordinate Hodge first jet in Minkowski normal coordinates

This module differentiates the explicit coordinate-metric Hodge formula at a
normal point.  It then discharges the first-jet compatibility left abstract
by `StagedHodgeExteriorBridge`.
-/

namespace RainichKaluza

open Set Filter
open scoped Matrix Topology

private theorem scalarFieldCoordinateFDeriv_mul_hodge
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

private theorem scalarFieldCoordinateFDeriv_sum_hodge
    {I : Type*} [Fintype I]
    (f : I → CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    scalarFieldCoordinateFDeriv (fun y ↦ ∑ i, f i y) z r =
      ∑ i, scalarFieldCoordinateFDeriv (f i) z r := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y ↦ ∑ i, f i y) = ∑ i, f i by
    funext y
    simp]
  rw [fderiv_sum]
  · simp
  · exact fun i _ ↦ hf i

private theorem scalarFieldCoordinateFDeriv_four_sum_hodge
    (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 →
      CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : ∀ a b c d, DifferentiableAt ℝ (f a b c d) z) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ ∑ a, ∑ b, ∑ c, ∑ d, f a b c d y) z r =
      ∑ a, ∑ b, ∑ c, ∑ d,
        scalarFieldCoordinateFDeriv (f a b c d) z r := by
  rw [scalarFieldCoordinateFDeriv_sum_hodge]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [scalarFieldCoordinateFDeriv_sum_hodge]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [scalarFieldCoordinateFDeriv_sum_hodge]
      · apply Finset.sum_congr rfl
        intro c hc
        rw [scalarFieldCoordinateFDeriv_sum_hodge]
        exact fun d ↦ hf a b c d
      · exact fun c ↦ DifferentiableAt.fun_sum
          (fun d _ ↦ hf a b c d)
    · exact fun b ↦ DifferentiableAt.fun_sum
        (fun c _ ↦ DifferentiableAt.fun_sum
          (fun d _ ↦ hf a b c d))
  · exact fun a ↦ DifferentiableAt.fun_sum
      (fun b _ ↦ DifferentiableAt.fun_sum
        (fun c _ ↦ DifferentiableAt.fun_sum
          (fun d _ ↦ hf a b c d)))

/-- A differentiable matrix field with zero coordinate first jet has zero
full Frechet derivative entrywise. -/
theorem matrixEntry_fderiv_eq_zero_of_coordinate_firstJet_zero
    (G : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (_hG : MatrixFieldDifferentiableAt4 G z)
    (hzero : ∀ r i j,
      scalarFieldCoordinateFDeriv (fun y ↦ G y i j) z r = 0)
    (i j : Fin 4) :
    fderiv ℝ (fun y ↦ G y i j) z = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin 4)).ext
  intro r
  rw [Pi.basisFun_apply, ← coordinateDirection_eq_single r]
  exact hzero r i j

/-- Consequently the determinant has zero Frechet derivative. -/
theorem matrixDet_fderiv_eq_zero_of_coordinate_firstJet_zero
    (G : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hG : MatrixFieldDifferentiableAt4 G z)
    (hzero : ∀ r i j,
      scalarFieldCoordinateFDeriv (fun y ↦ G y i j) z r = 0) :
    fderiv ℝ (fun y ↦ Matrix.det (G y)) z = 0 := by
  have hentry (i j : Fin 4) : HasFDerivAt
      (fun y ↦ G y i j)
        (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ) z := by
    have h := (hG i j).hasFDerivAt
    rw [matrixEntry_fderiv_eq_zero_of_coordinate_firstJet_zero
      G z hG hzero i j] at h
    exact h
  have hterm (σ : Equiv.Perm (Fin 4)) : HasFDerivAt
      (fun y ↦ Equiv.Perm.sign σ • ∏ k, G y (σ k) k)
        (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ) z := by
    have hprod : HasFDerivAt
        (fun y ↦ ∏ k, G y (σ k) k)
          (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ) z := by
      have hp := HasFDerivAt.finsetProd (u := Finset.univ)
        (g := fun k y ↦ G y (σ k) k)
        (g' := fun _ ↦ (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ))
        (fun k _ ↦ hentry (σ k) k)
      simpa using hp
    have hreal := hprod.const_smul
      ((Equiv.Perm.sign σ : ℤ) : ℝ)
    have heq :
        (((Equiv.Perm.sign σ : ℤ) : ℝ) •
          (fun y ↦ ∏ k, G y (σ k) k)) =
        (fun y ↦ Equiv.Perm.sign σ • ∏ k, G y (σ k) k) := by
      funext y
      rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
      rfl
    rw [heq] at hreal
    simpa only [smul_zero] using hreal
  have hsum : HasFDerivAt
      (fun y ↦ ∑ σ : Equiv.Perm (Fin 4),
        Equiv.Perm.sign σ • ∏ k, G y (σ k) k)
          (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ) z := by
    simpa using HasFDerivAt.fun_sum (u := Finset.univ)
      (A := fun σ y ↦ Equiv.Perm.sign σ • ∏ k, G y (σ k) k)
      (A' := fun _ ↦ (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ))
      (fun σ _ ↦ hterm σ)
  have hdet : HasFDerivAt (fun y ↦ Matrix.det (G y))
      (0 : CurvatureCoordinateSpace4 →L[ℝ] ℝ) z := by
    simpa only [Matrix.det_apply] using hsum
  exact hdet.fderiv

/-- Entrywise differentiability of the metric and two-form fields makes each
component of the coordinate Hodge field differentiable wherever the metric
determinant is nonzero. -/
theorem differentiableAt_coordinateMetricHodgeTwoForm4_apply
    (G F : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hG : MatrixFieldDifferentiableAt4 G z)
    (hF : ∀ m n, DifferentiableAt ℝ (fun y ↦ F y m n) z)
    (hdet : Matrix.det (G z) ≠ 0)
    (i j : Fin 4) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateMetricHodgeTwoForm4 (G y) (F y) i j) z := by
  have hInv (a b : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ (G y)⁻¹ a b) z :=
    differentiableAt_matrixNonsingInv_apply4 G z hG hdet a b
  have hNegDet : DifferentiableAt ℝ (fun y ↦ -Matrix.det (G y)) z :=
    hG.det.neg
  have hNegDetNe : -Matrix.det (G z) ≠ 0 := neg_ne_zero.mpr hdet
  have hSqrt : DifferentiableAt ℝ
      (fun y ↦ Real.sqrt (-Matrix.det (G y))) z :=
    hNegDet.sqrt hNegDetNe
  have hVolume : DifferentiableAt ℝ
      (fun y ↦ -(Real.sqrt (-Matrix.det (G y)) / 2)) z := by
    fun_prop
  unfold coordinateMetricHodgeTwoForm4
  apply hVolume.mul
  exact DifferentiableAt.fun_sum fun a _ ↦
    DifferentiableAt.fun_sum fun b _ ↦
      DifferentiableAt.fun_sum fun m _ ↦
        DifferentiableAt.fun_sum fun n _ ↦
          (((differentiableAt_const _).mul (hInv a m)).mul
            (hInv b n)).mul (hF m n)

/-- At a Minkowski normal point, differentiating the honest coordinate
metric Hodge star contributes no metric term.  Its first jet is exactly the
fixed Minkowski Hodge star of the two-form first jet. -/
theorem coordinateMetricHodgeTwoForm4_coordinateFDeriv_of_minkowskiNormal
    (G F : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hG : MatrixFieldDifferentiableAt4 G z)
    (hF : ∀ m n, DifferentiableAt ℝ (fun y ↦ F y m n) z)
    (hG0 : G z = minkowskiMetric)
    (hG1 : ∀ r m n,
      scalarFieldCoordinateFDeriv (fun y ↦ G y m n) z r = 0)
    (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateMetricHodgeTwoForm4 (G y) (F y) i j) z r =
      coordinateMetricHodgeTwoForm4 minkowskiMetric
        (matrixFieldCoordinateFDeriv4 F z r) i j := by
  let invEntry := fun a b y ↦ (G y)⁻¹ a b
  let volume := fun y ↦ -(Real.sqrt (-Matrix.det (G y)) / 2)
  let term := fun a b m n y ↦
    leviCivitaSymbol4 i j a b * invEntry a m y * invEntry b n y * F y m n
  let total := fun y ↦ ∑ a, ∑ b, ∑ m, ∑ n, term a b m n y
  have hdet : Matrix.det (G z) ≠ 0 := by
    rw [hG0, minkowskiMetric_det]
    norm_num
  have hInvValue : (G z)⁻¹ = minkowskiMetric := by
    rw [hG0]
    exact Matrix.inv_eq_right_inv minkowskiMetric_sq
  have hInvDiff (a b : Fin 4) : DifferentiableAt ℝ (invEntry a b) z := by
    exact differentiableAt_matrixNonsingInv_apply4 G z hG hdet a b
  have hInvJet (a b : Fin 4) :
      scalarFieldCoordinateFDeriv (invEntry a b) z r = 0 := by
    unfold invEntry
    rw [scalarFieldCoordinateFDeriv_matrixNonsingInv_apply4 G z hG hdet]
    simp_rw [hG1]
    simp
  have hDetDiff : DifferentiableAt ℝ (fun y ↦ Matrix.det (G y)) z :=
    hG.det
  have hDetFDeriv : fderiv ℝ (fun y ↦ Matrix.det (G y)) z = 0 :=
    matrixDet_fderiv_eq_zero_of_coordinate_firstJet_zero G z hG hG1
  have hNegDetDiff : DifferentiableAt ℝ
      (fun y ↦ -Matrix.det (G y)) z := hDetDiff.neg
  have hNegDetNe : -Matrix.det (G z) ≠ 0 := by
    rw [hG0, minkowskiMetric_det]
    norm_num
  have hNegDetFDeriv :
      fderiv ℝ (fun y ↦ -Matrix.det (G y)) z = 0 := by
    change fderiv ℝ (-(fun y ↦ Matrix.det (G y))) z = 0
    rw [fderiv_neg, hDetFDeriv]
    simp
  have hSqrtDiff : DifferentiableAt ℝ
      (fun y ↦ Real.sqrt (-Matrix.det (G y))) z :=
    hNegDetDiff.sqrt hNegDetNe
  have hSqrtJet : scalarFieldCoordinateFDeriv
      (fun y ↦ Real.sqrt (-Matrix.det (G y))) z r = 0 := by
    unfold scalarFieldCoordinateFDeriv
    rw [fderiv_sqrt hNegDetDiff hNegDetNe, hNegDetFDeriv]
    simp
  have hVolumeDiff : DifferentiableAt ℝ volume z := by
    unfold volume
    fun_prop
  have hVolumeJet : scalarFieldCoordinateFDeriv volume z r = 0 := by
    have hrewrite : volume = fun y ↦
        (-1 / 2 : ℝ) * Real.sqrt (-Matrix.det (G y)) := by
      funext y
      unfold volume
      ring
    rw [hrewrite, scalarFieldCoordinateFDeriv_mul_hodge]
    · rw [show scalarFieldCoordinateFDeriv
          (fun _ : CurvatureCoordinateSpace4 ↦ (-1 / 2 : ℝ)) z r = 0 by
          simp [scalarFieldCoordinateFDeriv]]
      rw [hSqrtJet]
      ring
    · fun_prop
    · exact hSqrtDiff
  have hTermDiff (a b m n : Fin 4) :
      DifferentiableAt ℝ (term a b m n) z := by
    unfold term
    exact (((differentiableAt_const _).mul (hInvDiff a m)).mul
      (hInvDiff b n)).mul (hF m n)
  have hTermJet (a b m n : Fin 4) :
      scalarFieldCoordinateFDeriv (term a b m n) z r =
        leviCivitaSymbol4 i j a b * invEntry a m z * invEntry b n z *
          scalarFieldCoordinateFDeriv (fun y ↦ F y m n) z r := by
    unfold term
    rw [scalarFieldCoordinateFDeriv_mul_hodge]
    · rw [scalarFieldCoordinateFDeriv_mul_hodge]
      · rw [scalarFieldCoordinateFDeriv_mul_hodge]
        · rw [show scalarFieldCoordinateFDeriv
              (fun _ : CurvatureCoordinateSpace4 ↦
                leviCivitaSymbol4 i j a b) z r = 0 by
              simp [scalarFieldCoordinateFDeriv]]
          rw [hInvJet a m, hInvJet b n]
          ring
        · fun_prop
        · exact hInvDiff a m
      · exact (differentiableAt_const _).mul (hInvDiff a m)
      · exact hInvDiff b n
    · exact ((differentiableAt_const _).mul (hInvDiff a m)).mul
        (hInvDiff b n)
    · exact hF m n
  have hTotalDiff : DifferentiableAt ℝ total z := by
    unfold total
    exact DifferentiableAt.fun_sum fun a _ ↦
      DifferentiableAt.fun_sum fun b _ ↦
        DifferentiableAt.fun_sum fun m _ ↦
          DifferentiableAt.fun_sum fun n _ ↦ hTermDiff a b m n
  have hTotalJet : scalarFieldCoordinateFDeriv total z r =
      ∑ a, ∑ b, ∑ m, ∑ n,
        leviCivitaSymbol4 i j a b * invEntry a m z * invEntry b n z *
          scalarFieldCoordinateFDeriv (fun y ↦ F y m n) z r := by
    unfold total
    rw [scalarFieldCoordinateFDeriv_four_sum_hodge]
    · simp_rw [hTermJet]
    · exact hTermDiff
  change scalarFieldCoordinateFDeriv (fun y ↦ volume y * total y) z r = _
  rw [scalarFieldCoordinateFDeriv_mul_hodge volume total z r
    hVolumeDiff hTotalDiff, hVolumeJet, hTotalJet]
  simp only [zero_mul, zero_add]
  unfold volume invEntry
  rw [hG0, minkowskiMetric_det]
  simp only [neg_neg, Real.sqrt_one, one_div]
  unfold coordinateMetricHodgeTwoForm4 matrixFieldCoordinateFDeriv4
  rw [minkowskiMetric_det]
  simp only [neg_neg, Real.sqrt_one, one_div]

/-- Frechet derivative of the full Hodge-flux scale. -/
theorem hasFDerivAt_normalWeightedHodgeFluxScale
    {phi : CurvatureCoordinateSpace4 → ℝ}
    {v : CurvatureCoordinateSpace4 →L[ℝ] ℝ}
    {z : CurvatureCoordinateSpace4}
    (hphi : HasFDerivAt phi v z) :
    HasFDerivAt
      (fun y ↦ normalWeightedHodgeFluxScale (phi y))
      ((Real.sqrt 3 * normalWeightedHodgeFluxScale (phi z)) • v) z := by
  have hExp := (hphi.const_smul (Real.sqrt 3)).exp
  have hScale := hExp.const_smul (Real.sqrt 2)⁻¹
  have hfun :
      ((Real.sqrt 2)⁻¹ •
        (fun y ↦ Real.exp ((Real.sqrt 3 • phi) y))) =
      (fun y ↦ (Real.sqrt 2)⁻¹ *
        Real.exp (Real.sqrt 3 * phi y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hfun] at hScale
  have hScale' : HasFDerivAt
      (fun y ↦ (Real.sqrt 2)⁻¹ *
        Real.exp (Real.sqrt 3 * phi y))
      (((Real.sqrt 2)⁻¹ * Real.sqrt 3 *
        Real.exp (Real.sqrt 3 * phi z)) • v) z := by
    simpa only [Pi.smul_apply, smul_eq_mul, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hScale
  change HasFDerivAt
    (fun y ↦ Real.exp (Real.sqrt 3 * phi y) / Real.sqrt 2)
    ((Real.sqrt 3 *
      (Real.exp (Real.sqrt 3 * phi z) / Real.sqrt 2)) • v) z
  simpa [div_eq_mul_inv, smul_smul, mul_assoc, mul_left_comm,
    mul_comm] using hScale'

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

/-- The normal-coordinate Hodge calculation makes the formerly explicit
weighted-flux first-jet compatibility automatic.  The only additional input
is the same staged seed/coframe alignment already used for the value-level
Hodge identification. -/
theorem weightedHodgeFluxFirstJetCompatible
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    N.WeightedHodgeFluxFirstJetCompatible := by
  let phiField := B.physical.maxwell.scalarRepresentative
  let GField := coordinateMetricMatrixField4 g
  let FField := stagedConventionPhysicalMaxwellMatrix4 B
  let HField := stagedMetricHodgePhysicalMaxwellMatrix4 B
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
      (B.conventionMaxwell_closed.differentiable x N.point_mem)
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
    have h := B.scalarPotential_matches_metric x N.point_mem
    rw [← N.phi1_eq_actualMetricScalarOneForm] at h
    exact h
  have hscale := hasFDerivAt_normalWeightedHodgeFluxScale hphi
  have hFJet (k : Fin 4) :
      matrixFieldCoordinateFDeriv4 FField x k =
        gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k := by
    ext a b
    have hEval := hasFDerivAt_twoFormEvaluation
      (B.conventionMaxwell_closed.differentiable x N.point_mem)
      (coordinateDirection a) (coordinateDirection b)
    have hStored : scalarFieldCoordinateFDeriv
        (fun y ↦ FField y a b) x k =
      B.physical.maxwell.conventionNormalizedPhysicalMaxwellDerivative x
        (coordinateDirection k) (coordinateDirection a)
          (coordinateDirection b) := by
      unfold scalarFieldCoordinateFDeriv FField
        stagedConventionPhysicalMaxwellMatrix4
      rw [hEval.fderiv]
      rfl
    rw [show matrixFieldCoordinateFDeriv4 FField x k a b =
      scalarFieldCoordinateFDeriv (fun y ↦ FField y a b) x k by rfl,
      hStored]
    exact (N.gaugeCurvatureFirstJet_eq_stagedConventionMaxwellDerivative
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
    unfold HField stagedMetricHodgePhysicalMaxwellMatrix4
    rw [N.coordinateMetric_eq_minkowski,
      ← N.gaugeCurvature_eq_stagedConventionMaxwell]
  have hScaleValue : normalWeightedHodgeFluxScale (phiField x) =
      normalWeightedHodgeFluxScale N.product.fields.phi0 := by
    rw [N.phi0_eq_scalarRepresentative]
  intro k i j
  let Wcomp := fun y ↦ B.physical.weightedHodgeFlux y
    (coordinateDirection i) (coordinateDirection j)
  let scaledHcomp := fun y ↦
    normalWeightedHodgeFluxScale (phiField y) * HField y i j
  have hfield : Wcomp =ᶠ[𝓝 x] scaledHcomp := by
    filter_upwards [B.weightedHodgeFlux_closed.isOpen.mem_nhds N.point_mem]
      with y hy
    exact B.weightedHodgeFlux_eq_scaled_metricHodge halign y hy i j
  have hWcoord : scalarFieldCoordinateFDeriv Wcomp x k =
      B.physical.weightedHodgeFluxDerivative x
        (coordinateDirection k) (coordinateDirection i)
          (coordinateDirection j) := by
    have hEval := hasFDerivAt_twoFormEvaluation
      (B.weightedHodgeFlux_closed.differentiable x N.point_mem)
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
  rw [scalarFieldCoordinateFDeriv_mul_hodge]
  · rw [hscaleJet, hHJet k i j, hScaleValue, hHValue]
    simp only [scaledTwoFormFirstJet, Matrix.add_apply, Matrix.smul_apply,
      Pi.smul_apply, smul_eq_mul]
  · exact hscaleDiff
  · exact hHDiff i j

/-- The literal normal exterior-Hodge equation now follows from staged
alignment alone; no separate first-jet compatibility is required. -/
theorem hodgeExterior_of_stagedAlignment
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    matrixExteriorDerivative
        (fun k ↦ coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureFirstJetOfSecondJet N.product.fields.A2 k)) =
      -(Real.sqrt 3) • matrixOneWedgeTwoTensor N.product.fields.phi1
        (coordinateMetricHodgeTwoForm4 minkowskiMetric
          (gaugeCurvatureOfFirstJet N.product.fields.A1)) :=
  N.hodgeExterior (N.weightedHodgeFluxFirstJetCompatible halign)

/-- Automatic promotion to the existing Hodge-normal representative. -/
def toHodgeNormalGaugeRepresentative_of_stagedAlignment
    (N : FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt B x)
    (halign :
      FixedChoiceStagedKaluzaConverseBoundary.StagedSeedEntranceAlignmentOn
        D M) :
    FixedChoiceMinkowskiHodgeNormalGaugeRepresentativeAt B x :=
  N.toHodgeNormalGaugeRepresentative
    (N.weightedHodgeFluxFirstJetCompatible halign)

end FixedChoiceMinkowskiPreHodgeNormalGaugeRepresentativeAt

end RainichKaluza
