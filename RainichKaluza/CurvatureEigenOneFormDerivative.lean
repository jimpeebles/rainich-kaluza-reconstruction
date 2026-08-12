import RainichKaluza.SmoothCurvatureProjector
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Derivatives of normalized curvature eigen-one-forms

This file differentiates the fixed-probe construction used by the smooth
curvature projectors.  It exposes exact Frechet product rules for metric
pairing, timelike/spacelike normalization, metric duality, and the projected
matrix probe.  The coordinate specialization is packaged by
`CurvatureBranchIntegration`.
-/

namespace RainichKaluza

open scoped Topology

variable {X V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Evaluated product-rule derivative of a varying metric pairing. -/
noncomputable def smoothMetricPairingFDeriv
    (g : X → ContinuousBilinForm V) (x y : X → V)
    (z u : X) : ℝ :=
  fderiv ℝ g z u (x z) (y z) +
    g z (fderiv ℝ x z u) (y z) +
    g z (x z) (fderiv ℝ y z u)

/-- The actual Frechet derivative of the metric pairing is the displayed
three-term product rule. -/
theorem smoothMetricPairing_fderiv_apply
    (g : X → ContinuousBilinForm V) (x y : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (hy : DifferentiableAt ℝ y z) :
    fderiv ℝ (smoothMetricPairing g x y) z u =
      smoothMetricPairingFDeriv g x y z u := by
  change fderiv ℝ (fun q => g q (x q) (y q)) z u = _
  rw [fderiv_clm_apply (hg.clm_apply hx) hy]
  rw [fderiv_clm_apply hg hx]
  simp [smoothMetricPairingFDeriv]
  ring

/-- Evaluated product-rule derivative of the metric dual of a varying vector. -/
noncomputable def smoothMetricDualCovectorFDeriv
    (g : X → ContinuousBilinForm V) (v : X → V)
    (z u : X) : V →L[ℝ] ℝ :=
  fderiv ℝ g z u (v z) + g z (fderiv ℝ v z u)

/-- The actual Frechet derivative of a varying metric dual is the displayed
two-term product rule. -/
theorem smoothMetricDualCovector_fderiv_apply
    (g : X → ContinuousBilinForm V) (v : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hv : DifferentiableAt ℝ v z) :
    fderiv ℝ (smoothMetricDualCovector g v) z u =
      smoothMetricDualCovectorFDeriv g v z u := by
  change fderiv ℝ (fun q => g q (v q)) z u = _
  rw [fderiv_clm_apply hg hv]
  ext w
  simp [smoothMetricDualCovectorFDeriv]
  ring

/-- Reciprocal square-root scale used for timelike normalization. -/
noncomputable def timelikeNormalizationScale
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X) : ℝ :=
  (Real.sqrt (-smoothMetricPairing g x x z))⁻¹

/-- Reciprocal square-root scale used for spacelike normalization. -/
noncomputable def spacelikeNormalizationScale
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X) : ℝ :=
  (Real.sqrt (smoothMetricPairing g x x z))⁻¹

theorem differentiableAt_timelikeNormalizationScale
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (ht : smoothMetricPairing g x x z < 0) :
    DifferentiableAt ℝ (timelikeNormalizationScale g x) z := by
  have hp : DifferentiableAt ℝ (smoothMetricPairing g x x) z :=
    (hg.clm_apply hx).clm_apply hx
  have hn : DifferentiableAt ℝ (fun q => -smoothMetricPairing g x x q) z := hp.neg
  have hn0 : -smoothMetricPairing g x x z ≠ 0 := ne_of_gt (neg_pos.mpr ht)
  have hs := hn.sqrt hn0
  have hs0 : Real.sqrt (-smoothMetricPairing g x x z) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (neg_pos.mpr ht)
  exact hs.inv hs0

theorem differentiableAt_spacelikeNormalizationScale
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (hs : 0 < smoothMetricPairing g x x z) :
    DifferentiableAt ℝ (spacelikeNormalizationScale g x) z := by
  have hp : DifferentiableAt ℝ (smoothMetricPairing g x x) z :=
    (hg.clm_apply hx).clm_apply hx
  have hp0 : smoothMetricPairing g x x z ≠ 0 := ne_of_gt hs
  have hr := hp.sqrt hp0
  have hr0 : Real.sqrt (smoothMetricPairing g x x z) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hs
  exact hr.inv hr0

/-- Derivative of the timelike reciprocal square-root normalization scale. -/
theorem timelikeNormalizationScale_fderiv_apply
    (g : X → ContinuousBilinForm V) (x : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (ht : smoothMetricPairing g x x z < 0) :
    fderiv ℝ (timelikeNormalizationScale g x) z u =
      (1 / 2 : ℝ) * (timelikeNormalizationScale g x z) ^ 3 *
        smoothMetricPairingFDeriv g x x z u := by
  have hp : DifferentiableAt ℝ (smoothMetricPairing g x x) z :=
    (hg.clm_apply hx).clm_apply hx
  have hn : DifferentiableAt ℝ (fun q => -smoothMetricPairing g x x q) z := hp.neg
  have hn0 : -smoothMetricPairing g x x z ≠ 0 := ne_of_gt (neg_pos.mpr ht)
  have hs := hn.sqrt hn0
  have hs0 : Real.sqrt (-smoothMetricPairing g x x z) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (neg_pos.mpr ht)
  change (fderiv ℝ
    (Inv.inv ∘ fun q => Real.sqrt (-smoothMetricPairing g x x q)) z) u = _
  have hcomp := fderiv_comp (f := fun q => Real.sqrt (-smoothMetricPairing g x x q))
    (g := Inv.inv) (x := z) (differentiableAt_inv hs0) hs
  rw [hcomp]
  rw [fderiv_inv' hs0]
  rw [fderiv_sqrt hn hn0]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_apply]
  rw [fderiv_fun_neg]
  simp only [neg_apply]
  rw [smoothMetricPairing_fderiv_apply g x x z u hg hx hx]
  simp [timelikeNormalizationScale]
  ring

/-- Derivative of the spacelike reciprocal square-root normalization scale. -/
theorem spacelikeNormalizationScale_fderiv_apply
    (g : X → ContinuousBilinForm V) (x : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (hsign : 0 < smoothMetricPairing g x x z) :
    fderiv ℝ (spacelikeNormalizationScale g x) z u =
      -(1 / 2 : ℝ) * (spacelikeNormalizationScale g x z) ^ 3 *
        smoothMetricPairingFDeriv g x x z u := by
  have hp : DifferentiableAt ℝ (smoothMetricPairing g x x) z :=
    (hg.clm_apply hx).clm_apply hx
  have hp0 : smoothMetricPairing g x x z ≠ 0 := ne_of_gt hsign
  have hs := hp.sqrt hp0
  have hs0 : Real.sqrt (smoothMetricPairing g x x z) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hsign
  change (fderiv ℝ
    (Inv.inv ∘ fun q => Real.sqrt (smoothMetricPairing g x x q)) z) u = _
  have hcomp := fderiv_comp (f := fun q => Real.sqrt (smoothMetricPairing g x x q))
    (g := Inv.inv) (x := z) (differentiableAt_inv hs0) hs
  rw [hcomp]
  rw [fderiv_inv' hs0]
  rw [fderiv_sqrt hp hp0]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_apply]
  rw [smoothMetricPairing_fderiv_apply g x x z u hg hx hx]
  simp [spacelikeNormalizationScale]
  ring

/-- Product-rule derivative of a timelike-normalized varying vector. -/
noncomputable def smoothNormalizeTimelikeFDeriv
    (g : X → ContinuousBilinForm V) (x : X → V)
    (z u : X) : V :=
  timelikeNormalizationScale g x z • fderiv ℝ x z u +
    ((1 / 2 : ℝ) * (timelikeNormalizationScale g x z) ^ 3 *
      smoothMetricPairingFDeriv g x x z u) • x z

/-- Product-rule derivative of a spacelike-normalized varying vector. -/
noncomputable def smoothNormalizeSpacelikeFDeriv
    (g : X → ContinuousBilinForm V) (x : X → V)
    (z u : X) : V :=
  spacelikeNormalizationScale g x z • fderiv ℝ x z u +
    (-(1 / 2 : ℝ) * (spacelikeNormalizationScale g x z) ^ 3 *
      smoothMetricPairingFDeriv g x x z u) • x z

/-- Exact derivative of timelike normalization, including the derivative of
the normalization scale. -/
theorem smoothNormalizeTimelike_fderiv_apply
    (g : X → ContinuousBilinForm V) (x : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (ht : smoothMetricPairing g x x z < 0) :
    fderiv ℝ (smoothNormalizeTimelike g x) z u =
      smoothNormalizeTimelikeFDeriv g x z u := by
  have hs := differentiableAt_timelikeNormalizationScale g x z hg hx ht
  change fderiv ℝ (fun q => timelikeNormalizationScale g x q • x q) z u = _
  rw [fderiv_fun_smul hs hx]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [timelikeNormalizationScale_fderiv_apply g x z u hg hx ht]
  rfl

/-- Exact derivative of spacelike normalization, including the derivative of
the normalization scale. -/
theorem smoothNormalizeSpacelike_fderiv_apply
    (g : X → ContinuousBilinForm V) (x : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (hsign : 0 < smoothMetricPairing g x x z) :
    fderiv ℝ (smoothNormalizeSpacelike g x) z u =
      smoothNormalizeSpacelikeFDeriv g x z u := by
  have hs := differentiableAt_spacelikeNormalizationScale g x z hg hx hsign
  change fderiv ℝ (fun q => spacelikeNormalizationScale g x q • x q) z u = _
  rw [fderiv_fun_smul hs hx]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [spacelikeNormalizationScale_fderiv_apply g x z u hg hx hsign]
  rfl

/-- Explicit derivative of the metric dual of a timelike-normalized vector. -/
noncomputable def smoothTimelikeNormalizedMetricDualFDeriv
    (g : X → ContinuousBilinForm V) (x : X → V)
    (z u : X) : V →L[ℝ] ℝ :=
  fderiv ℝ g z u (smoothNormalizeTimelike g x z) +
    g z (smoothNormalizeTimelikeFDeriv g x z u)

/-- Explicit derivative of the metric dual of a spacelike-normalized vector. -/
noncomputable def smoothSpacelikeNormalizedMetricDualFDeriv
    (g : X → ContinuousBilinForm V) (x : X → V)
    (z u : X) : V →L[ℝ] ℝ :=
  fderiv ℝ g z u (smoothNormalizeSpacelike g x z) +
    g z (smoothNormalizeSpacelikeFDeriv g x z u)

theorem differentiableAt_smoothNormalizeTimelike
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (ht : smoothMetricPairing g x x z < 0) :
    DifferentiableAt ℝ (smoothNormalizeTimelike g x) z := by
  have hs := differentiableAt_timelikeNormalizationScale g x z hg hx ht
  change DifferentiableAt ℝ (fun q => timelikeNormalizationScale g x q • x q) z
  exact hs.smul hx

theorem differentiableAt_smoothNormalizeSpacelike
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (hsign : 0 < smoothMetricPairing g x x z) :
    DifferentiableAt ℝ (smoothNormalizeSpacelike g x) z := by
  have hs := differentiableAt_spacelikeNormalizationScale g x z hg hx hsign
  change DifferentiableAt ℝ (fun q => spacelikeNormalizationScale g x q • x q) z
  exact hs.smul hx

/-- The timelike normalized metric dual has exactly the displayed explicit
Frechet derivative. -/
theorem smoothTimelikeNormalizedMetricDual_fderiv_apply
    (g : X → ContinuousBilinForm V) (x : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (ht : smoothMetricPairing g x x z < 0) :
    fderiv ℝ (smoothMetricDualCovector g (smoothNormalizeTimelike g x)) z u =
      smoothTimelikeNormalizedMetricDualFDeriv g x z u := by
  have hn := differentiableAt_smoothNormalizeTimelike g x z hg hx ht
  rw [smoothMetricDualCovector_fderiv_apply g (smoothNormalizeTimelike g x) z u hg hn]
  unfold smoothMetricDualCovectorFDeriv smoothTimelikeNormalizedMetricDualFDeriv
  rw [smoothNormalizeTimelike_fderiv_apply g x z u hg hx ht]

/-- The spacelike normalized metric dual has exactly the displayed explicit
Frechet derivative. -/
theorem smoothSpacelikeNormalizedMetricDual_fderiv_apply
    (g : X → ContinuousBilinForm V) (x : X → V) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hx : DifferentiableAt ℝ x z)
    (hsign : 0 < smoothMetricPairing g x x z) :
    fderiv ℝ (smoothMetricDualCovector g (smoothNormalizeSpacelike g x)) z u =
      smoothSpacelikeNormalizedMetricDualFDeriv g x z u := by
  have hn := differentiableAt_smoothNormalizeSpacelike g x z hg hx hsign
  rw [smoothMetricDualCovector_fderiv_apply g (smoothNormalizeSpacelike g x) z u hg hn]
  unfold smoothMetricDualCovectorFDeriv smoothSpacelikeNormalizedMetricDualFDeriv
  rw [smoothNormalizeSpacelike_fderiv_apply g x z u hg hx hsign]

section FixedMatrixProbe

/-- Entrywise derivative of a fixed vector acted on by a varying matrix. -/
noncomputable def smoothMatrixProjectedVectorFDeriv
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X) : Fin 4 → ℝ :=
  fun i => ∑ j, fderiv ℝ (fun q => P q i j) z u * probe j

/-- A fixed-probe matrix product differentiates entrywise with no residual
derivative placeholder for the projected vector. -/
theorem smoothMatrixProjectedVector_fderiv_apply
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X)
    (hP : DifferentiableAt ℝ P z) :
    fderiv ℝ (smoothMatrixProjectedVector P probe) z u =
      smoothMatrixProjectedVectorFDeriv P probe z u := by
  have hPij : ∀ i j, DifferentiableAt ℝ (fun q => P q i j) z := by
    intro i j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 hP i) j
  have hv : DifferentiableAt ℝ (smoothMatrixProjectedVector P probe) z := by
    rw [differentiableAt_pi]
    intro i
    simp only [smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact DifferentiableAt.fun_sum fun j _ => (hPij i j).mul_const (probe j)
  ext i
  have happ := congrArg (fun L => L u) (fderiv_apply hv i)
  have happ' :
      fderiv ℝ (fun q => smoothMatrixProjectedVector P probe q i) z u =
        fderiv ℝ (smoothMatrixProjectedVector P probe) z u i := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using happ
  rw [← happ']
  simp only [smoothMatrixProjectedVector, Matrix.mulVec, dotProduct,
    smoothMatrixProjectedVectorFDeriv]
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_mul_const (hPij i j) (probe j)]
    simp
    ring
  · intro j _
    exact (hPij i j).mul_const (probe j)

theorem differentiableAt_smoothMatrixProjectedVector
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z : X)
    (hP : DifferentiableAt ℝ P z) :
    DifferentiableAt ℝ (smoothMatrixProjectedVector P probe) z := by
  rw [differentiableAt_pi]
  intro i
  simp only [smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun j _ =>
    (differentiableAt_pi.1 (differentiableAt_pi.1 hP i) j).mul_const (probe j)

/-- Fully expanded pairing derivative for a fixed matrix-projected probe. -/
noncomputable def smoothProjectedMetricPairingFDeriv
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X) : ℝ :=
  let p := smoothMatrixProjectedVector P probe z
  let dp := smoothMatrixProjectedVectorFDeriv P probe z u
  fderiv ℝ g z u p p + g z dp p + g z p dp

/-- Fully expanded derivative of the normalized timelike fixed probe. -/
noncomputable def smoothNormalizeTimelikeProjectedFDeriv
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X) : Fin 4 → ℝ :=
  let pField := smoothMatrixProjectedVector P probe
  timelikeNormalizationScale g pField z •
      smoothMatrixProjectedVectorFDeriv P probe z u +
    ((1 / 2 : ℝ) * (timelikeNormalizationScale g pField z) ^ 3 *
      smoothProjectedMetricPairingFDeriv g P probe z u) • pField z

/-- Fully expanded derivative of the normalized spacelike fixed probe. -/
noncomputable def smoothNormalizeSpacelikeProjectedFDeriv
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X) : Fin 4 → ℝ :=
  let pField := smoothMatrixProjectedVector P probe
  spacelikeNormalizationScale g pField z •
      smoothMatrixProjectedVectorFDeriv P probe z u +
    (-(1 / 2 : ℝ) * (spacelikeNormalizationScale g pField z) ^ 3 *
      smoothProjectedMetricPairingFDeriv g P probe z u) • pField z

theorem smoothNormalizeTimelikeFDeriv_projected_eq
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X)
    (hP : DifferentiableAt ℝ P z) :
    smoothNormalizeTimelikeFDeriv g (smoothMatrixProjectedVector P probe) z u =
      smoothNormalizeTimelikeProjectedFDeriv g P probe z u := by
  unfold smoothNormalizeTimelikeFDeriv smoothNormalizeTimelikeProjectedFDeriv
  unfold smoothMetricPairingFDeriv smoothProjectedMetricPairingFDeriv
  rw [smoothMatrixProjectedVector_fderiv_apply P probe z u hP]

theorem smoothNormalizeSpacelikeFDeriv_projected_eq
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X)
    (hP : DifferentiableAt ℝ P z) :
    smoothNormalizeSpacelikeFDeriv g (smoothMatrixProjectedVector P probe) z u =
      smoothNormalizeSpacelikeProjectedFDeriv g P probe z u := by
  unfold smoothNormalizeSpacelikeFDeriv smoothNormalizeSpacelikeProjectedFDeriv
  unfold smoothMetricPairingFDeriv smoothProjectedMetricPairingFDeriv
  rw [smoothMatrixProjectedVector_fderiv_apply P probe z u hP]

/-- Fully expanded derivative of the timelike fixed-probe curvature
eigen-one-form. -/
noncomputable def smoothTimelikeCurvatureEigenCovectorFDeriv
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X) :
    (Fin 4 → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ g z u
      (smoothNormalizeTimelike g (smoothMatrixProjectedVector P probe) z) +
    g z (smoothNormalizeTimelikeProjectedFDeriv g P probe z u)

/-- Fully expanded derivative of the spacelike fixed-probe curvature
eigen-one-form. -/
noncomputable def smoothSpacelikeCurvatureEigenCovectorFDeriv
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X) :
    (Fin 4 → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ g z u
      (smoothNormalizeSpacelike g (smoothMatrixProjectedVector P probe) z) +
    g z (smoothNormalizeSpacelikeProjectedFDeriv g P probe z u)

/-- Exact Frechet derivative of the timelike fixed-probe curvature
eigen-one-form. -/
theorem smoothTimelikeCurvatureEigenCovector_fderiv_apply
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hP : DifferentiableAt ℝ P z)
    (ht : smoothMetricPairing g (smoothMatrixProjectedVector P probe)
      (smoothMatrixProjectedVector P probe) z < 0) :
    fderiv ℝ (smoothTimelikeCurvatureEigenCovector g P probe) z u =
      smoothTimelikeCurvatureEigenCovectorFDeriv g P probe z u := by
  have hp := differentiableAt_smoothMatrixProjectedVector P probe z hP
  unfold smoothTimelikeCurvatureEigenCovector
  rw [smoothTimelikeNormalizedMetricDual_fderiv_apply g
    (smoothMatrixProjectedVector P probe) z u hg hp ht]
  unfold smoothTimelikeNormalizedMetricDualFDeriv
  rw [smoothNormalizeTimelikeFDeriv_projected_eq g P probe z u hP]
  rfl

/-- Exact Frechet derivative of the spacelike fixed-probe curvature
eigen-one-form. -/
theorem smoothSpacelikeCurvatureEigenCovector_fderiv_apply
    (g : X → ContinuousBilinForm (Fin 4 → ℝ))
    (P : X → Matrix4) (probe : Fin 4 → ℝ) (z u : X)
    (hg : DifferentiableAt ℝ g z)
    (hP : DifferentiableAt ℝ P z)
    (hsign : 0 < smoothMetricPairing g (smoothMatrixProjectedVector P probe)
      (smoothMatrixProjectedVector P probe) z) :
    fderiv ℝ (smoothSpacelikeCurvatureEigenCovector g P probe) z u =
      smoothSpacelikeCurvatureEigenCovectorFDeriv g P probe z u := by
  have hp := differentiableAt_smoothMatrixProjectedVector P probe z hP
  unfold smoothSpacelikeCurvatureEigenCovector
  rw [smoothSpacelikeNormalizedMetricDual_fderiv_apply g
    (smoothMatrixProjectedVector P probe) z u hg hp hsign]
  unfold smoothSpacelikeNormalizedMetricDualFDeriv
  rw [smoothNormalizeSpacelikeFDeriv_projected_eq g P probe z u hP]
  rfl

end FixedMatrixProbe

end RainichKaluza
