import RainichKaluza.AffineCoordinateRicci
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Smooth coordinate-field realization of the Kaluza reduction

`KaluzaRicciBase.lean` proves the full convention-fixed Kaluza reduction for
abstract coordinate jets satisfying the symmetries of genuine second
derivatives.  This file supplies the first geometric wrapper: the jets are
extracted from actual `C²` scalar, gauge-potential, and symmetric metric fields
on the four-dimensional coordinate space `Fin 4 → ℝ`.

The structure `KaluzaNormalGaugeFieldsAt` records precisely the coordinate
preparations used by the curvature calculation at a point `x`: diagonal
nondegenerate base metric, vanishing first metric jet, and radial gauge
`A(x)=0`.  Mathlib's Schwarz theorem then discharges every commuting-second-
jet hypothesis.  The endpoint `conventionKaluzaFieldRicciFlatAt_iff_emd`
instantiates the complete `5×5` Ricci-flatness equivalence with those genuine
field derivatives.

This remains a coordinate-germ theorem, but `CoordinateRicci.lean` now
separates the standard coordinate Levi--Civita/Ricci construction from the
Kaluza ansatz, and this file proves that the genuine five-coordinate
derivatives of the actual local-product metric produce exactly that Ricci
tensor.  The remaining intrinsic wrapper is chart-independence/manifold
packaging; Mathlib currently has no ready-made Lorentzian Ricci API.
-/

namespace RainichKaluza

open Filter Matrix
open scoped Topology ContDiff

/-- The four-dimensional real coordinate space used by the local wrapper. -/
abbrev BaseCoordinateSpace := Fin 4 → ℝ

/-- Coordinates on the local product of the base patch with the circle
direction (represented locally by a real coordinate). -/
abbrev LocalProductCoordinateSpace := BaseCoordinateSpace × ℝ

/-- Standard coordinate direction `∂/∂xⁱ`. -/
def coordinateDirection (i : Fin 4) : BaseCoordinateSpace :=
  fun j => if j = i then 1 else 0

/-- The five coordinate directions on the local product. -/
def localProductCoordinateDirection (I : Fin 4 ⊕ Unit) :
    LocalProductCoordinateSpace :=
  match I with
  | Sum.inl i => (coordinateDirection i, 0)
  | Sum.inr _ => (0, 1)

/-- First derivatives of a circle-invariant scalar field are the base
derivatives applied to the base component of the direction. -/
theorem pullback_fst_fderiv_apply
    {x : BaseCoordinateSpace} (z : ℝ) (f : BaseCoordinateSpace → ℝ)
    (hf : DifferentiableAt ℝ f x) (v : LocalProductCoordinateSpace) :
    fderiv ℝ (fun p : LocalProductCoordinateSpace => f p.1) (x, z) v =
      fderiv ℝ f x v.1 := by
  have h := hf.hasFDerivAt.comp (x, z)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := BaseCoordinateSpace) (F := ℝ)
      (p := (x, z)))
  change fderiv ℝ (f ∘ Prod.fst) (x, z) v = _
  rw [h.fderiv]
  rfl

/-- Second derivatives of a circle-invariant `C²` scalar field are exactly
the base Hessian evaluated on the two base components. -/
theorem pullback_fst_second_fderiv_apply
    {x : BaseCoordinateSpace} (z : ℝ) (f : BaseCoordinateSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (v w : LocalProductCoordinateSpace) :
    fderiv ℝ
        (fderiv ℝ (fun p : LocalProductCoordinateSpace => f p.1)) (x, z)
        v w =
      fderiv ℝ (fderiv ℝ f) x v.1 w.1 := by
  change fderiv ℝ (fderiv ℝ (f ∘ Prod.fst)) (x, z) v w = _
  let L := ContinuousLinearMap.fst ℝ BaseCoordinateSpace ℝ
  have hdiffEvent : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono fun _ hy =>
      hy.differentiableAt (by norm_num)
  have hdiffProd :
      ∀ᶠ p in 𝓝 (x, z), DifferentiableAt ℝ f p.1 :=
    (continuousAt_fst.tendsto.eventually hdiffEvent)
  have hfirstEvent :
      fderiv ℝ (f ∘ Prod.fst) =ᶠ[𝓝 (x, z)]
        (fun p => (fderiv ℝ f p.1).comp L) := by
    filter_upwards [hdiffProd] with p hp
    have h := hp.hasFDerivAt.comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (E := BaseCoordinateSpace) (F := ℝ)
        (p := p))
    simpa only [L] using h.fderiv
  have hDf : HasFDerivAt (fderiv ℝ f)
      (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hDfPull := hDf.comp (x, z)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := BaseCoordinateSpace) (F := ℝ)
      (p := (x, z)))
  let K := (ContinuousLinearMap.compL ℝ LocalProductCoordinateSpace
    BaseCoordinateSpace ℝ).flip L
  have hprecomp := K.hasFDerivAt.comp (x, z) hDfPull
  change HasFDerivAt (fun p => (fderiv ℝ f p.1).comp L) _ (x, z) at hprecomp
  rw [hfirstEvent.fderiv_eq, hprecomp.fderiv]
  simp [K, L, ContinuousLinearMap.compL_apply]

/-- Second-order chain rule for an exponential of a scalar `C²` field.  This
is the reusable analytic core of the assembled metric's warp second jet. -/
theorem exp_const_mul_second_fderiv_apply
    {x : BaseCoordinateSpace} (phi : BaseCoordinateSpace → ℝ)
    (hphi : ContDiffAt ℝ 2 phi x) (k : ℝ) (v w : BaseCoordinateSpace) :
    fderiv ℝ (fderiv ℝ (fun y => Real.exp (k * phi y))) x v w =
      (k * fderiv ℝ (fderiv ℝ phi) x v w +
        k ^ 2 * fderiv ℝ phi x v * fderiv ℝ phi x w) *
          Real.exp (k * phi x) := by
  have hphiEvent : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ phi y :=
    (hphi.eventually (by norm_num)).mono fun _ hy =>
      hy.differentiableAt (by norm_num)
  have hfirstEvent :
      fderiv ℝ (fun y => Real.exp (k * phi y)) =ᶠ[𝓝 x]
        (fun y => (k * Real.exp (k * phi y)) • fderiv ℝ phi y) := by
    filter_upwards [hphiEvent] with y hy
    have h := ((hy.hasFDerivAt.const_smul k).exp).fderiv
    simpa only [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm] using h
  have hphi' : HasFDerivAt phi (fderiv ℝ phi x) x :=
    (hphi.differentiableAt (by norm_num)).hasFDerivAt
  have hwarp := (hphi'.const_smul k).exp
  have hcoeff := hwarp.const_mul k
  have hfderivPhi : HasFDerivAt (fderiv ℝ phi)
      (fderiv ℝ (fderiv ℝ phi) x) x :=
    ((hphi.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hproduct := hcoeff.smul hfderivPhi
  change HasFDerivAt
    (fun y => (k * Real.exp (k * phi y)) • fderiv ℝ phi y) _ x at hproduct
  rw [hfirstEvent.fderiv_eq, hproduct.fderiv]
  simp
  ring

/-- Second-order product rule for scalar `C²` fields, stated in the same
`fderiv (fderiv ·)` convention used by the coordinate jets. -/
theorem mul_second_fderiv_apply
    {x : BaseCoordinateSpace} (f g : BaseCoordinateSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v w : BaseCoordinateSpace) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
        g x * fderiv ℝ (fderiv ℝ f) x v w +
        fderiv ℝ f x v * fderiv ℝ g x w +
        fderiv ℝ f x w * fderiv ℝ g x v := by
  have hfEvent : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono fun _ hy =>
      hy.differentiableAt (by norm_num)
  have hgEvent : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by norm_num)).mono fun _ hy =>
      hy.differentiableAt (by norm_num)
  have hfirstEvent :
      fderiv ℝ (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    filter_upwards [hfEvent, hgEvent] with y hyf hyg
    exact fderiv_fun_mul hyf hyg
  have hf' : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt g (fderiv ℝ g x) x :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hDg : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hsum := (hf'.smul hDg).add (hg'.smul hDf)
  change HasFDerivAt
    (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) _ x at hsum
  rw [hfirstEvent.fderiv_eq, hsum.fderiv]
  simp
  ring

/-- Second derivatives distribute over addition for scalar `C²` fields. -/
theorem add_second_fderiv_apply
    {x : BaseCoordinateSpace} (f g : BaseCoordinateSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v w : BaseCoordinateSpace) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w +
        fderiv ℝ (fderiv ℝ g) x v w := by
  have hfEvent : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by norm_num)).mono fun _ hy =>
      hy.differentiableAt (by norm_num)
  have hgEvent : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by norm_num)).mono fun _ hy =>
      hy.differentiableAt (by norm_num)
  have hfirstEvent :
      fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x]
        (fun y => fderiv ℝ f y + fderiv ℝ g y) := by
    filter_upwards [hfEvent, hgEvent] with y hyf hyg
    exact fderiv_fun_add hyf hyg
  have hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hDg : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hsum := hDf.add hDg
  change HasFDerivAt
    (fun y => fderiv ℝ f y + fderiv ℝ g y) _ x at hsum
  rw [hfirstEvent.fderiv_eq, hsum.fderiv]
  rfl

/-- Actual `C²` coordinate fields in base normal coordinates and radial gauge
at `x`.  Smoothness is recorded componentwise, matching the coordinate Ricci
calculation and avoiding any choice of norm on spaces of tensors. -/
structure KaluzaNormalGaugeFieldsAt (x : BaseCoordinateSpace) where
  phi : BaseCoordinateSpace → ℝ
  potential : BaseCoordinateSpace → OneForm4
  metric : BaseCoordinateSpace → Matrix4
  phi_contDiffAt : ContDiffAt ℝ 2 phi x
  potential_contDiffAt :
    ∀ mu, ContDiffAt ℝ 2 (fun y => potential y mu) x
  metric_contDiffAt :
    ∀ mu nu, ContDiffAt ℝ 2 (fun y => metric y mu nu) x
  metric_symmetric :
    ∀ᶠ y in 𝓝 x, ∀ mu nu, metric y mu nu = metric y nu mu
  potential_eq_zero : potential x = 0
  metric_offDiagonal_eq_zero :
    ∀ mu nu, mu ≠ nu → metric x mu nu = 0
  metric_firstJet_eq_zero :
    ∀ sigma mu nu,
      fderiv ℝ (fun y => metric y mu nu) x (coordinateDirection sigma) = 0
  metric_diagonal_ne_zero : ∀ i, metric x i i ≠ 0

namespace KaluzaNormalGaugeFieldsAt

variable {x : BaseCoordinateSpace} (D : KaluzaNormalGaugeFieldsAt x)

/-- Scalar value at the normal-gauge point. -/
def phi0 : ℝ := D.phi x

/-- Diagonal entries of the base metric at the normal-coordinate point. -/
def diagonal : Fin 4 → ℝ := fun i => D.metric x i i

/-- First scalar jet in the coordinate frame. -/
noncomputable def phi1 : OneForm4 := fun sigma =>
  fderiv ℝ D.phi x (coordinateDirection sigma)

/-- Scalar Hessian in the coordinate frame. -/
noncomputable def phi2 : Fin 4 → Fin 4 → ℝ := fun sigma rho =>
  fderiv ℝ (fderiv ℝ D.phi) x
    (coordinateDirection sigma) (coordinateDirection rho)

/-- First coordinate jet of the gauge potential. -/
noncomputable def A1 : Fin 4 → Fin 4 → ℝ := fun sigma mu =>
  fderiv ℝ (fun y => D.potential y mu) x (coordinateDirection sigma)

/-- Second coordinate jet of the gauge potential. -/
noncomputable def A2 : Fin 4 → Fin 4 → Fin 4 → ℝ := fun sigma rho mu =>
  fderiv ℝ (fderiv ℝ (fun y => D.potential y mu)) x
    (coordinateDirection sigma) (coordinateDirection rho)

/-- Second coordinate jet of the base metric. -/
noncomputable def g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun sigma rho mu nu =>
    fderiv ℝ (fderiv ℝ (fun y => D.metric y mu nu)) x
      (coordinateDirection sigma) (coordinateDirection rho)

/-- The actual convention-fixed Kaluza metric field assembled from the three
four-dimensional fields. -/
noncomputable def upliftMetric (y : BaseCoordinateSpace) : Matrix5 :=
  kaluzaBlockMetric (kaluzaBaseWarp (D.phi y))
    (kaluzaFiberWarp (D.phi y)) kaluzaGaugeNormalization
    (D.metric y) (D.potential y)

/-- Circle-invariant extension of the uplift metric to the local product. -/
noncomputable def localProductUpliftMetric
    (p : LocalProductCoordinateSpace) : Matrix5 :=
  D.upliftMetric p.1

theorem localProductUpliftMetric_circle_invariant
    (y : BaseCoordinateSpace) (z z' : ℝ) :
    D.localProductUpliftMetric (y, z) =
      D.localProductUpliftMetric (y, z') := rfl

theorem upliftMetric_base_base (y : BaseCoordinateSpace) (mu nu : Fin 4) :
    D.upliftMetric y (Sum.inl mu) (Sum.inl nu) =
      kaluzaBaseWarp (D.phi y) * D.metric y mu nu +
        kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization ^ 2 *
          D.potential y mu * D.potential y nu := by
  unfold upliftMetric
  rw [kaluzaBlockMetric_eq_fromBlocks]
  simp [oneFormColumn, oneFormRow, Matrix.mul_apply]
  ring

theorem upliftMetric_base_fiber (y : BaseCoordinateSpace) (mu : Fin 4) :
    D.upliftMetric y (Sum.inl mu) (Sum.inr ()) =
      kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization *
        D.potential y mu := by
  unfold upliftMetric
  rw [kaluzaBlockMetric_eq_fromBlocks]
  simp [oneFormColumn]

theorem upliftMetric_fiber_base (y : BaseCoordinateSpace) (nu : Fin 4) :
    D.upliftMetric y (Sum.inr ()) (Sum.inl nu) =
      kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization *
        D.potential y nu := by
  unfold upliftMetric
  rw [kaluzaBlockMetric_eq_fromBlocks]
  simp [oneFormRow]

theorem upliftMetric_fiber_fiber (y : BaseCoordinateSpace) :
    D.upliftMetric y (Sum.inr ()) (Sum.inr ()) =
      kaluzaFiberWarp (D.phi y) := by
  unfold upliftMetric
  rw [kaluzaBlockMetric_eq_fromBlocks]
  simp

theorem diagonal_ne_zero (i : Fin 4) : D.diagonal i ≠ 0 :=
  D.metric_diagonal_ne_zero i

theorem hasFDerivAt_phi :
    HasFDerivAt D.phi (fderiv ℝ D.phi x) x :=
  D.phi_contDiffAt.differentiableAt (by norm_num) |>.hasFDerivAt

theorem hasFDerivAt_potential_component (mu : Fin 4) :
    HasFDerivAt (fun y => D.potential y mu)
      (fderiv ℝ (fun y => D.potential y mu) x) x :=
  (D.potential_contDiffAt mu).differentiableAt (by norm_num) |>.hasFDerivAt

theorem hasFDerivAt_metric_component (mu nu : Fin 4) :
    HasFDerivAt (fun y => D.metric y mu nu)
      (fderiv ℝ (fun y => D.metric y mu nu) x) x :=
  (D.metric_contDiffAt mu nu).differentiableAt (by norm_num) |>.hasFDerivAt

/-- Chain rule for the base warp as a full Frechet derivative. -/
theorem hasFDerivAt_baseWarp :
    HasFDerivAt (fun y => kaluzaBaseWarp (D.phi y))
      ((kaluzaBaseWarpExponent * kaluzaBaseWarp D.phi0) •
        fderiv ℝ D.phi x) x := by
  have h := (D.hasFDerivAt_phi.const_smul kaluzaBaseWarpExponent).exp
  simpa only [Pi.smul_apply, smul_eq_mul, kaluzaBaseWarp, phi0, smul_smul,
    mul_comm] using h

/-- Chain rule for the fiber warp as a full Frechet derivative. -/
theorem hasFDerivAt_fiberWarp :
    HasFDerivAt (fun y => kaluzaFiberWarp (D.phi y))
      ((kaluzaFiberWarpExponent * kaluzaFiberWarp D.phi0) •
        fderiv ℝ D.phi x) x := by
  have h := (D.hasFDerivAt_phi.const_smul kaluzaFiberWarpExponent).exp
  simpa only [Pi.smul_apply, smul_eq_mul, kaluzaFiberWarp, phi0, smul_smul,
    mul_comm] using h

/-- The base warp inherits the stored `C²` regularity of the scalar field. -/
theorem baseWarp_contDiffAt :
    ContDiffAt ℝ 2 (fun y => kaluzaBaseWarp (D.phi y)) x := by
  simpa only [kaluzaBaseWarp] using
    (contDiffAt_const.mul D.phi_contDiffAt).exp

/-- The fiber warp inherits the stored `C²` regularity of the scalar field. -/
theorem fiberWarp_contDiffAt :
    ContDiffAt ℝ 2 (fun y => kaluzaFiberWarp (D.phi y)) x := by
  simpa only [kaluzaFiberWarp] using
    (contDiffAt_const.mul D.phi_contDiffAt).exp

/-- Every component of the actually assembled uplift metric is `C²` at the
normal-gauge point. -/
theorem upliftMetric_component_contDiffAt (M N : Fin 4 ⊕ Unit) :
    ContDiffAt ℝ 2 (fun y => D.upliftMetric y M N) x := by
  rcases M with mu | _ <;> rcases N with nu | _
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inl nu)) =
          (fun y =>
            kaluzaBaseWarp (D.phi y) * D.metric y mu nu +
              ((kaluzaFiberWarp (D.phi y) *
                kaluzaGaugeNormalization ^ 2) * D.potential y mu) *
                D.potential y nu) := by
      funext y
      rw [D.upliftMetric_base_base]
    rw [hfun]
    exact (D.baseWarp_contDiffAt.mul (D.metric_contDiffAt mu nu)).add
      (((D.fiberWarp_contDiffAt.mul contDiffAt_const).mul
        (D.potential_contDiffAt mu)).mul (D.potential_contDiffAt nu))
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inr ())) =
          (fun y => (kaluzaFiberWarp (D.phi y) *
            kaluzaGaugeNormalization) * D.potential y mu) := by
      funext y
      rw [D.upliftMetric_base_fiber]
    rw [hfun]
    exact (D.fiberWarp_contDiffAt.mul contDiffAt_const).mul
      (D.potential_contDiffAt mu)
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inl nu)) =
          (fun y => (kaluzaFiberWarp (D.phi y) *
            kaluzaGaugeNormalization) * D.potential y nu) := by
      funext y
      rw [D.upliftMetric_fiber_base]
    rw [hfun]
    exact (D.fiberWarp_contDiffAt.mul contDiffAt_const).mul
      (D.potential_contDiffAt nu)
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inr ())) =
          (fun y => kaluzaFiberWarp (D.phi y)) := by
      funext y
      rw [D.upliftMetric_fiber_fiber]
    rw [hfun]
    exact D.fiberWarp_contDiffAt

/-- The actual local-product metric is symmetric throughout a neighborhood
of `(x,z)`, inherited from the base metric field. -/
theorem localProductUpliftMetric_eventually_symmetric (z : ℝ) :
    ∀ᶠ p in 𝓝 (x, z), ∀ M N,
      D.localProductUpliftMetric p M N =
        D.localProductUpliftMetric p N M := by
  have hfst : Tendsto (fun p : LocalProductCoordinateSpace => p.1)
      (𝓝 (x, z)) (𝓝 x) := continuousAt_fst
  have hbase : ∀ᶠ p in 𝓝 (x, z), ∀ mu nu,
      D.metric p.1 mu nu = D.metric p.1 nu mu :=
    hfst.eventually D.metric_symmetric
  filter_upwards [hbase] with p hp
  intro M N
  have hg : (D.metric p.1)ᵀ = D.metric p.1 := by
    ext mu nu
    exact hp nu mu
  have htranspose := kaluzaBlockMetric_transpose
    (kaluzaBaseWarp (D.phi p.1)) (kaluzaFiberWarp (D.phi p.1))
    kaluzaGaugeNormalization (D.metric p.1) (D.potential p.1) hg
  have hentry := congrArg (fun G : Matrix5 => G N M) htranspose
  simpa only [Matrix.transpose_apply, localProductUpliftMetric, upliftMetric]
    using hentry

/-- Every component of the circle-invariant local-product metric is genuinely
`C²` in all five coordinates at `(x,z)`. -/
theorem localProductUpliftMetric_component_contDiffAt (z : ℝ)
    (M N : Fin 4 ⊕ Unit) :
    ContDiffAt ℝ 2 (fun p => D.localProductUpliftMetric p M N) (x, z) := by
  exact (D.upliftMetric_component_contDiffAt M N).comp (x, z) contDiffAt_fst

/-- Actual first coordinate jet of the circle-invariant local-product uplift. -/
noncomputable def localProductMetricJet1 (z : ℝ) :
    CoordinateMetricJet1 (Fin 4 ⊕ Unit) :=
  fun R M N =>
    fderiv ℝ (fun p => D.localProductUpliftMetric p M N) (x, z)
      (localProductCoordinateDirection R)

/-- Actual second coordinate jet of the circle-invariant local-product
uplift. -/
noncomputable def localProductMetricJet2 (z : ℝ) :
    CoordinateMetricJet2 (Fin 4 ⊕ Unit) :=
  fun R S M N =>
    fderiv ℝ (fderiv ℝ
      (fun p => D.localProductUpliftMetric p M N)) (x, z)
        (localProductCoordinateDirection R)
        (localProductCoordinateDirection S)

theorem fderiv_baseWarp_apply (rho : Fin 4) :
    fderiv ℝ (fun y => kaluzaBaseWarp (D.phi y)) x
        (coordinateDirection rho) =
      kaluzaBaseWarpExponent * D.phi1 rho * kaluzaBaseWarp D.phi0 := by
  rw [D.hasFDerivAt_baseWarp.fderiv]
  simp [phi1]
  ring

theorem fderiv_fiberWarp_apply (rho : Fin 4) :
    fderiv ℝ (fun y => kaluzaFiberWarp (D.phi y)) x
        (coordinateDirection rho) =
      kaluzaFiberWarpExponent * D.phi1 rho * kaluzaFiberWarp D.phi0 := by
  rw [D.hasFDerivAt_fiberWarp.fderiv]
  simp [phi1]
  ring

/-- The first derivative of the actual assembled metric field is exactly the
normal-gauge metric jet used by the Christoffel and Ricci calculation. -/
theorem upliftMetric_fderiv_apply_at (rho : Fin 4)
    (M N : Fin 4 ⊕ Unit) :
    fderiv ℝ (fun y => D.upliftMetric y M N) x
        (coordinateDirection rho) =
      kaluzaNormalGaugeMetricJet (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.A1 (Sum.inl rho) M N := by
  rcases M with mu | _ <;> rcases N with nu | _
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inl nu)) =
          (fun y =>
            kaluzaBaseWarp (D.phi y) * D.metric y mu nu +
              ((kaluzaFiberWarp (D.phi y) *
                kaluzaGaugeNormalization ^ 2) * D.potential y mu) *
                D.potential y nu) := by
      funext y
      rw [D.upliftMetric_base_base]
    have hbase := D.hasFDerivAt_baseWarp.mul
      (D.hasFDerivAt_metric_component mu nu)
    have hquad := ((D.hasFDerivAt_fiberWarp.mul_const
      (kaluzaGaugeNormalization ^ 2)).mul
        (D.hasFDerivAt_potential_component mu)).mul
          (D.hasFDerivAt_potential_component nu)
    have htotal := hbase.add hquad
    change HasFDerivAt (fun y =>
      kaluzaBaseWarp (D.phi y) * D.metric y mu nu +
        ((kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization ^ 2) *
          D.potential y mu) * D.potential y nu) _ x at htotal
    rw [hfun, htotal.fderiv]
    have hgpoint : D.metric x mu nu = Matrix.diagonal D.diagonal mu nu :=
      by
        by_cases h : mu = nu
        · subst nu
          simp [diagonal]
        · simp [h, D.metric_offDiagonal_eq_zero mu nu h]
    have hAmu : D.potential x mu = 0 := by
      rw [D.potential_eq_zero]
      rfl
    have hAnu : D.potential x nu = 0 := by
      rw [D.potential_eq_zero]
      rfl
    simp [kaluzaNormalGaugeMetricJet, hgpoint, hAmu, hAnu, phi0,
      phi1, D.metric_firstJet_eq_zero rho mu nu]
    ring
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inr ())) =
          (fun y =>
            (kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization) *
              D.potential y mu) := by
      funext y
      rw [D.upliftMetric_base_fiber]
    have hmix := (D.hasFDerivAt_fiberWarp.mul_const
      kaluzaGaugeNormalization).mul (D.hasFDerivAt_potential_component mu)
    change HasFDerivAt (fun y =>
      (kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization) *
        D.potential y mu) _ x at hmix
    rw [hfun, hmix.fderiv]
    have hAmu : D.potential x mu = 0 := by
      rw [D.potential_eq_zero]
      rfl
    simp [kaluzaNormalGaugeMetricJet, hAmu, A1, phi0]
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inl nu)) =
          (fun y =>
            (kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization) *
              D.potential y nu) := by
      funext y
      rw [D.upliftMetric_fiber_base]
    have hmix := (D.hasFDerivAt_fiberWarp.mul_const
      kaluzaGaugeNormalization).mul (D.hasFDerivAt_potential_component nu)
    change HasFDerivAt (fun y =>
      (kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization) *
        D.potential y nu) _ x at hmix
    rw [hfun, hmix.fderiv]
    have hAnu : D.potential x nu = 0 := by
      rw [D.potential_eq_zero]
      rfl
    simp [kaluzaNormalGaugeMetricJet, hAnu, A1, phi0]
  · have hfun :
        (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inr ())) =
          (fun y => kaluzaFiberWarp (D.phi y)) := by
      funext y
      rw [D.upliftMetric_fiber_fiber]
    rw [hfun, D.hasFDerivAt_fiberWarp.fderiv]
    simp [kaluzaNormalGaugeMetricJet, phi1]
    ring

/-- The fiber--fiber component of the actual assembled second jet agrees with
the chain-rule block metric jet. -/
theorem upliftMetric_secondJet_fiber_fiber (sigma rho : Fin 4) :
    fderiv ℝ
        (fderiv ℝ (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inr ()))) x
        (coordinateDirection sigma) (coordinateDirection rho) =
      kaluzaNormalGaugeMetricJet2 (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 sigma rho
        (Sum.inr ()) (Sum.inr ()) := by
  have hfun :
      (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inr ())) =
        (fun y => Real.exp (kaluzaFiberWarpExponent * D.phi y)) := by
    funext y
    rw [D.upliftMetric_fiber_fiber]
    rfl
  rw [hfun, exp_const_mul_second_fderiv_apply D.phi D.phi_contDiffAt]
  unfold kaluzaNormalGaugeMetricJet2 phi0 phi1 phi2 kaluzaFiberWarp
  ring

/-- The base--fiber component of the actual assembled second jet agrees with
the chain-rule block metric jet. -/
theorem upliftMetric_secondJet_base_fiber (sigma rho mu : Fin 4) :
    fderiv ℝ
        (fderiv ℝ (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inr ()))) x
        (coordinateDirection sigma) (coordinateDirection rho) =
      kaluzaNormalGaugeMetricJet2 (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 sigma rho
        (Sum.inl mu) (Sum.inr ()) := by
  have hfun :
      (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inr ())) =
        (fun y => (kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization) *
          D.potential y mu) := by
    funext y
    rw [D.upliftMetric_base_fiber]
  have hproduct := mul_second_fderiv_apply
    (fun y => kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization)
    (fun y => D.potential y mu)
    (D.fiberWarp_contDiffAt.mul contDiffAt_const)
    (D.potential_contDiffAt mu)
    (coordinateDirection sigma) (coordinateDirection rho)
  rw [hfun, hproduct]
  have hA : D.potential x mu = 0 := by
    rw [D.potential_eq_zero]
    rfl
  have hDwarp (i : Fin 4) :
      fderiv ℝ
          (fun y => kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization) x
          (coordinateDirection i) =
        kaluzaGaugeNormalization * kaluzaFiberWarpExponent * D.phi1 i *
          kaluzaFiberWarp D.phi0 := by
    rw [(D.hasFDerivAt_fiberWarp.mul_const
      kaluzaGaugeNormalization).fderiv]
    simp [phi1]
    ring
  rw [hDwarp sigma, hDwarp rho]
  unfold kaluzaNormalGaugeMetricJet2 A1 A2 phi0
  simp [hA]
  ring

/-- The fiber--base second jet is the symmetric companion of the
base--fiber block. -/
theorem upliftMetric_secondJet_fiber_base (sigma rho nu : Fin 4) :
    fderiv ℝ
        (fderiv ℝ (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inl nu))) x
        (coordinateDirection sigma) (coordinateDirection rho) =
      kaluzaNormalGaugeMetricJet2 (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 sigma rho
        (Sum.inr ()) (Sum.inl nu) := by
  have hcomponents :
      (fun y => D.upliftMetric y (Sum.inr ()) (Sum.inl nu)) =
        (fun y => D.upliftMetric y (Sum.inl nu) (Sum.inr ())) := by
    funext y
    rw [D.upliftMetric_fiber_base, D.upliftMetric_base_fiber]
  calc
    _ = fderiv ℝ
          (fderiv ℝ
            (fun y => D.upliftMetric y (Sum.inl nu) (Sum.inr ()))) x
          (coordinateDirection sigma) (coordinateDirection rho) := by
        exact congrArg
          (fun f => fderiv ℝ (fderiv ℝ f) x
            (coordinateDirection sigma) (coordinateDirection rho)) hcomponents
    _ = _ := by
      simpa only [kaluzaNormalGaugeMetricJet2] using
        D.upliftMetric_secondJet_base_fiber sigma rho nu

/-- The base--base component of the actual assembled second jet agrees with
the chain-rule block metric jet, including both the warped base Hessian and
the quadratic gauge contribution. -/
theorem upliftMetric_secondJet_base_base
    (sigma rho mu nu : Fin 4) :
    fderiv ℝ
        (fderiv ℝ (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inl nu))) x
        (coordinateDirection sigma) (coordinateDirection rho) =
      kaluzaNormalGaugeMetricJet2 (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 sigma rho
        (Sum.inl mu) (Sum.inl nu) := by
  let baseTerm : BaseCoordinateSpace → ℝ := fun y =>
    kaluzaBaseWarp (D.phi y) * D.metric y mu nu
  let gaugeTerm : BaseCoordinateSpace → ℝ := fun y =>
    ((kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization ^ 2) *
      D.potential y mu) * D.potential y nu
  have hfun :
      (fun y => D.upliftMetric y (Sum.inl mu) (Sum.inl nu)) =
        (fun y => baseTerm y + gaugeTerm y) := by
    funext y
    rw [D.upliftMetric_base_base]
  have hmetric : D.metric x mu nu = Matrix.diagonal D.diagonal mu nu := by
    by_cases h : mu = nu
    · subst nu
      simp [diagonal]
    · simp [h, D.metric_offDiagonal_eq_zero mu nu h]
  have hAmu : D.potential x mu = 0 := by
    rw [D.potential_eq_zero]
    rfl
  have hAnu : D.potential x nu = 0 := by
    rw [D.potential_eq_zero]
    rfl
  have hHbaseWarp :
      fderiv ℝ (fderiv ℝ (fun y => kaluzaBaseWarp (D.phi y))) x
          (coordinateDirection sigma) (coordinateDirection rho) =
        (kaluzaBaseWarpExponent * D.phi2 sigma rho +
          kaluzaBaseWarpExponent ^ 2 * D.phi1 sigma * D.phi1 rho) *
            kaluzaBaseWarp D.phi0 := by
    simpa only [kaluzaBaseWarp, phi0, phi1, phi2] using
      exp_const_mul_second_fderiv_apply D.phi D.phi_contDiffAt
        kaluzaBaseWarpExponent (coordinateDirection sigma)
        (coordinateDirection rho)
  have hbase :
      fderiv ℝ (fderiv ℝ baseTerm) x
          (coordinateDirection sigma) (coordinateDirection rho) =
        kaluzaBaseWarp D.phi0 * D.g2 sigma rho mu nu +
          (kaluzaBaseWarpExponent * D.phi2 sigma rho +
            kaluzaBaseWarpExponent ^ 2 * D.phi1 sigma * D.phi1 rho) *
              kaluzaBaseWarp D.phi0 * Matrix.diagonal D.diagonal mu nu := by
    change fderiv ℝ
      (fderiv ℝ (fun y =>
        kaluzaBaseWarp (D.phi y) * D.metric y mu nu)) x
      (coordinateDirection sigma) (coordinateDirection rho) = _
    rw [mul_second_fderiv_apply
      (fun y => kaluzaBaseWarp (D.phi y))
      (fun y => D.metric y mu nu)
      D.baseWarp_contDiffAt (D.metric_contDiffAt mu nu),
      hHbaseWarp, D.fderiv_baseWarp_apply sigma,
      D.fderiv_baseWarp_apply rho,
      D.metric_firstJet_eq_zero sigma mu nu,
      D.metric_firstJet_eq_zero rho mu nu]
    unfold g2 phi0
    rw [hmetric]
    ring
  have hDgaugeLeft (i : Fin 4) :
      fderiv ℝ
          (fun y => (kaluzaFiberWarp (D.phi y) *
            kaluzaGaugeNormalization ^ 2) * D.potential y mu) x
          (coordinateDirection i) =
        kaluzaFiberWarp D.phi0 * kaluzaGaugeNormalization ^ 2 * D.A1 i mu := by
    have hderiv := ((D.hasFDerivAt_fiberWarp.mul_const
      (kaluzaGaugeNormalization ^ 2)).mul
        (D.hasFDerivAt_potential_component mu)).fderiv
    change fderiv ℝ
      (fun y => (kaluzaFiberWarp (D.phi y) *
        kaluzaGaugeNormalization ^ 2) * D.potential y mu) x = _ at hderiv
    rw [hderiv]
    simp [hAmu, A1, phi0]
  have hgauge :
      fderiv ℝ (fderiv ℝ gaugeTerm) x
          (coordinateDirection sigma) (coordinateDirection rho) =
        kaluzaFiberWarp D.phi0 * kaluzaGaugeNormalization ^ 2 *
          (D.A1 sigma mu * D.A1 rho nu +
            D.A1 rho mu * D.A1 sigma nu) := by
    change fderiv ℝ
      (fderiv ℝ (fun y =>
        ((kaluzaFiberWarp (D.phi y) * kaluzaGaugeNormalization ^ 2) *
          D.potential y mu) * D.potential y nu)) x
      (coordinateDirection sigma) (coordinateDirection rho) = _
    rw [mul_second_fderiv_apply
      (fun y => (kaluzaFiberWarp (D.phi y) *
        kaluzaGaugeNormalization ^ 2) * D.potential y mu)
      (fun y => D.potential y nu)
      ((D.fiberWarp_contDiffAt.mul contDiffAt_const).mul
        (D.potential_contDiffAt mu))
      (D.potential_contDiffAt nu),
      hDgaugeLeft sigma, hDgaugeLeft rho]
    unfold A1 phi0
    simp [hAmu, hAnu]
    ring
  rw [hfun, add_second_fderiv_apply baseTerm gaugeTerm
    (D.baseWarp_contDiffAt.mul (D.metric_contDiffAt mu nu))
    (((D.fiberWarp_contDiffAt.mul contDiffAt_const).mul
      (D.potential_contDiffAt mu)).mul (D.potential_contDiffAt nu)),
    hbase, hgauge]
  unfold kaluzaNormalGaugeMetricJet2
  ring

/-- The second derivative of the actual assembled metric field agrees with
the chain-rule jet used in `KaluzaRicci.lean`. -/
noncomputable def UpliftSecondJetMatches : Prop :=
  ∀ sigma rho : Fin 4, ∀ M N : Fin 4 ⊕ Unit,
    fderiv ℝ (fderiv ℝ (fun y => D.upliftMetric y M N)) x
        (coordinateDirection sigma) (coordinateDirection rho) =
      kaluzaNormalGaugeMetricJet2 (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 sigma rho M N

/-- **Complete assembled-metric second-jet bridge.** Every component of the
actual `C²` Kaluza metric has exactly the pointwise Hessian supplied to the
coordinate Ricci calculation. -/
theorem upliftSecondJetMatches : D.UpliftSecondJetMatches := by
  intro sigma rho M N
  rcases M with mu | _ <;> rcases N with nu | _
  · exact D.upliftMetric_secondJet_base_base sigma rho mu nu
  · exact D.upliftMetric_secondJet_base_fiber sigma rho mu
  · exact D.upliftMetric_secondJet_fiber_base sigma rho nu
  · exact D.upliftMetric_secondJet_fiber_fiber sigma rho

/-- The actual five-dimensional first coordinate jet of the local-product
metric is the full normal-gauge Kaluza first jet, including the vanishing
circle derivative. -/
theorem localProductMetricJet1_eq (z : ℝ) :
    D.localProductMetricJet1 z =
      kaluzaNormalGaugeMetricJet (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.A1 := by
  funext R M N
  unfold localProductMetricJet1 localProductUpliftMetric
  rw [pullback_fst_fderiv_apply z (fun y => D.upliftMetric y M N)
    ((D.upliftMetric_component_contDiffAt M N).differentiableAt
      (by norm_num))]
  rcases R with r | _
  · simpa only [localProductCoordinateDirection, Prod.fst] using
      D.upliftMetric_fderiv_apply_at r M N
  · simp [localProductCoordinateDirection, kaluzaNormalGaugeMetricJet]

/-- The actual five-dimensional second coordinate jet of the local-product
metric is the full circle-invariant Kaluza Hessian. -/
theorem localProductMetricJet2_eq (z : ℝ) :
    D.localProductMetricJet2 z =
      kaluzaNormalGaugeFullMetricJet2 (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 := by
  funext R S M N
  unfold localProductMetricJet2 localProductUpliftMetric
  rw [pullback_fst_second_fderiv_apply z
    (fun y => D.upliftMetric y M N)
    (D.upliftMetric_component_contDiffAt M N)]
  rcases R with r | _ <;> rcases S with s | _
  · simpa only [localProductCoordinateDirection, Prod.fst,
      kaluzaNormalGaugeFullMetricJet2, Sum.elim_inl,
      kaluzaNormalGaugeDoubleJet] using
      D.upliftSecondJetMatches r s M N
  · simp [localProductCoordinateDirection, kaluzaNormalGaugeFullMetricJet2,
      kaluzaNormalGaugeDoubleJet]
  · simp [localProductCoordinateDirection, kaluzaNormalGaugeFullMetricJet2]
  · simp [localProductCoordinateDirection, kaluzaNormalGaugeFullMetricJet2]

/-- The stored point metric really is `diag d`. -/
theorem metric_eq_diagonal : D.metric x = Matrix.diagonal D.diagonal := by
  ext mu nu
  by_cases h : mu = nu
  · subst nu
    simp [diagonal]
  · simp [h, D.metric_offDiagonal_eq_zero mu nu h]

/-- At the normal-gauge point, the assembled field has exactly the block
diagonal value used by the coordinate Ricci calculation. -/
theorem upliftMetric_apply_at (M N : Fin 4 ⊕ Unit) :
    D.upliftMetric x M N =
      kaluzaNormalGaugePointMetric (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) D.diagonal M N := by
  unfold upliftMetric phi0
  rw [kaluzaBlockMetric_eq_fromBlocks, D.potential_eq_zero,
    D.metric_eq_diagonal]
  rcases M with mu | _ <;> rcases N with nu | _ <;>
    simp [kaluzaNormalGaugePointMetric, oneFormColumn, oneFormRow,
      Matrix.mul_apply, Matrix.diagonal_apply]

/-- The evaluated block inverse is genuinely inverse to the actual
local-product metric at `(x,z)`. -/
theorem localProductUpliftMetric_mul_pointInverse (z : ℝ)
    (M N : Fin 4 ⊕ Unit) :
    (∑ A : Fin 4 ⊕ Unit, D.localProductUpliftMetric (x, z) M A *
      kaluzaNormalGaugePointInverse (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) D.diagonal A N) =
      if M = N then 1 else 0 := by
  simp only [localProductUpliftMetric]
  rw [show D.upliftMetric x =
      kaluzaNormalGaugePointMetric (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) D.diagonal from by
    funext M' N'
    exact D.upliftMetric_apply_at M' N']
  exact kaluzaNormalGaugePointMetric_mul_inverse
    (kaluzaBaseWarp D.phi0) (kaluzaFiberWarp D.phi0) D.diagonal
    (kaluzaBaseWarp_ne_zero D.phi0) (kaluzaFiberWarp_ne_zero D.phi0)
    D.diagonal_ne_zero M N

/-- The extracted scalar Hessian commutes by Schwarz's theorem. -/
theorem phi2_symm (sigma rho : Fin 4) :
    D.phi2 sigma rho = D.phi2 rho sigma := by
  exact ((D.phi_contDiffAt.isSymmSndFDerivAt (by norm_num)).eq
    (coordinateDirection sigma) (coordinateDirection rho))

/-- Every component of the extracted gauge second jet commutes. -/
theorem A2_symm (sigma rho mu : Fin 4) :
    D.A2 sigma rho mu = D.A2 rho sigma mu := by
  exact (((D.potential_contDiffAt mu).isSymmSndFDerivAt (by norm_num)).eq
    (coordinateDirection sigma) (coordinateDirection rho))

/-- The derivative slots of the extracted metric second jet commute. -/
theorem g2_deriv_symm (sigma rho mu nu : Fin 4) :
    D.g2 sigma rho mu nu = D.g2 rho sigma mu nu := by
  exact (((D.metric_contDiffAt mu nu).isSymmSndFDerivAt (by norm_num)).eq
    (coordinateDirection sigma) (coordinateDirection rho))

/-- Symmetry of the actual metric field propagates through two derivatives,
so the metric slots of `g2` remain symmetric. -/
theorem g2_metric_symm (sigma rho mu nu : Fin 4) :
    D.g2 sigma rho mu nu = D.g2 sigma rho nu mu := by
  have hcomp :
      (fun y => D.metric y mu nu) =ᶠ[𝓝 x]
        (fun y => D.metric y nu mu) :=
    D.metric_symmetric.mono fun y hy => hy mu nu
  have hfirst :
      fderiv ℝ (fun y => D.metric y mu nu) =ᶠ[𝓝 x]
        fderiv ℝ (fun y => D.metric y nu mu) :=
    hcomp.fderiv
  have hsecond :
      fderiv ℝ (fderiv ℝ (fun y => D.metric y mu nu)) x =
        fderiv ℝ (fderiv ℝ (fun y => D.metric y nu mu)) x :=
    hfirst.fderiv_eq
  exact congrArg
    (fun L => L (coordinateDirection sigma) (coordinateDirection rho)) hsecond

/-- Convention-fixed coordinate Ricci-flatness evaluated on the genuine
field jets extracted at `x`. -/
noncomputable def RicciFlat : Prop :=
  ConventionKaluzaRicciFlatAt D.phi0 D.diagonal D.phi1 D.phi2
    D.A1 D.A2 D.g2

/-- Convention-fixed normal-frame EMD equations evaluated on the genuine
field jets extracted at `x`. -/
noncomputable def EMDEquations : Prop :=
  ConventionEMDNormalFrameEquations D.phi0 D.diagonal D.phi1 D.phi2
    D.A1 D.A2 D.g2

/-- Coordinate Ricci tensor of the actual circle-invariant local-product
metric at `(x,z)`, computed from its genuine first and second Frechet
derivatives and its certified point inverse. -/
noncomputable def localProductCoordinateRicci (z : ℝ)
    (N P : Fin 4 ⊕ Unit) : ℝ :=
  coordinateRicci
    (kaluzaNormalGaugePointInverse (kaluzaBaseWarp D.phi0)
      (kaluzaFiberWarp D.phi0) D.diagonal)
    (D.localProductMetricJet1 z) (D.localProductMetricJet2 z) N P

/-- Coordinate Ricci-flatness of the actual local-product uplift at `(x,z)`. -/
noncomputable def LocalProductCoordinateRicciFlat (z : ℝ) : Prop :=
  ∀ N P : Fin 4 ⊕ Unit, D.localProductCoordinateRicci z N P = 0

/-- Ricci-flatness of the same genuine local-product metric jet after an
arbitrary invertible affine change of the five coordinates. -/
noncomputable def AffineLocalProductCoordinateRicciFlat
    (C : AffineCoordinateChange (Fin 4 ⊕ Unit)) (z : ℝ) : Prop :=
  ∀ N P : Fin 4 ⊕ Unit,
    coordinateRicci
      (C.transformContravariant2
        (kaluzaNormalGaugePointInverse (kaluzaBaseWarp D.phi0)
          (kaluzaFiberWarp D.phi0) D.diagonal))
      (C.transformCovariant3 (D.localProductMetricJet1 z))
      (C.transformCovariant4 (D.localProductMetricJet2 z)) N P = 0

/-- The coordinate Ricci tensor extracted from the actual local-product
metric is exactly the audited normal-gauge Kaluza Ricci tensor. -/
theorem localProductCoordinateRicci_eq (z : ℝ) (N P : Fin 4 ⊕ Unit) :
    D.localProductCoordinateRicci z N P =
      kaluzaNormalGaugeRicci (kaluzaBaseWarp D.phi0)
        (kaluzaFiberWarp D.phi0) kaluzaGaugeNormalization
        kaluzaBaseWarpExponent kaluzaFiberWarpExponent D.diagonal
        D.phi1 D.phi2 D.A1 D.A2 D.g2 N P := by
  unfold localProductCoordinateRicci
  rw [D.localProductMetricJet1_eq z, D.localProductMetricJet2_eq z]
  exact coordinateRicci_kaluzaNormalGauge
    (kaluzaBaseWarp D.phi0) (kaluzaFiberWarp D.phi0)
    kaluzaGaugeNormalization kaluzaBaseWarpExponent
    kaluzaFiberWarpExponent D.diagonal D.phi1 D.phi2 D.A1 D.A2 D.g2 N P

/-- The actual first metric jet has symmetric metric slots, hence its
coordinate Christoffel symbols are torsion-free. -/
theorem localProductMetricJet1_symm (z : ℝ) (R M N : Fin 4 ⊕ Unit) :
    D.localProductMetricJet1 z R M N =
      D.localProductMetricJet1 z R N M := by
  rw [D.localProductMetricJet1_eq z]
  exact kaluzaNormalGaugeMetricJet_symm
    (kaluzaBaseWarp D.phi0) (kaluzaFiberWarp D.phi0)
    kaluzaGaugeNormalization kaluzaBaseWarpExponent
    kaluzaFiberWarpExponent D.diagonal D.phi1 D.A1 R M N

theorem localProductCoordinateChristoffel_symm (z : ℝ)
    (M N P : Fin 4 ⊕ Unit) :
    coordinateChristoffel
        (kaluzaNormalGaugePointInverse (kaluzaBaseWarp D.phi0)
          (kaluzaFiberWarp D.phi0) D.diagonal)
        (D.localProductMetricJet1 z) M N P =
      coordinateChristoffel
        (kaluzaNormalGaugePointInverse (kaluzaBaseWarp D.phi0)
          (kaluzaFiberWarp D.phi0) D.diagonal)
        (D.localProductMetricJet1 z) M P N := by
  exact coordinateChristoffel_symm _ _ (D.localProductMetricJet1_symm z)
    M N P

/-- **Smooth coordinate-field Kaluza reduction.** For actual `C²` fields in
base normal coordinates and radial gauge, the complete convention-fixed
five-dimensional coordinate Ricci tensor vanishes at the point exactly when
the four-dimensional normal-frame EMD equations hold there. -/
theorem conventionKaluzaFieldRicciFlatAt_iff_emd :
    D.RicciFlat ↔ D.EMDEquations := by
  exact conventionKaluzaRicciFlatAt_iff_emd
    D.phi0 D.diagonal D.phi1 D.phi2 D.A1 D.A2 D.g2
    D.diagonal_ne_zero D.phi2_symm D.A2_symm D.g2_deriv_symm
    D.g2_metric_symm

/-- **Coordinate-geometric Kaluza reduction for the actual uplift.** The
actual circle-invariant `C²` local-product metric is coordinate Ricci-flat at
`(x,z)` if and only if its extracted four-dimensional fields satisfy the
convention-fixed normal-frame EMD equations at `x`. -/
theorem localProductCoordinateRicciFlat_iff_emd (z : ℝ) :
    D.LocalProductCoordinateRicciFlat z ↔ D.EMDEquations := by
  rw [← D.conventionKaluzaFieldRicciFlatAt_iff_emd]
  constructor
  · intro h N P
    rw [← D.localProductCoordinateRicci_eq z N P]
    exact h N P
  · intro h N P
    rw [D.localProductCoordinateRicci_eq z N P]
    exact h N P

/-- **Affine-coordinate geometric Kaluza reduction.** The normal-coordinate
calculation is not tied to that chosen coordinate basis: after any invertible
constant change of all five coordinates, the transformed genuine metric jet
is Ricci-flat exactly when the extracted four-dimensional EMD equations hold.
The change may mix base and circle coordinate directions. -/
theorem affineLocalProductCoordinateRicciFlat_iff_emd
    (C : AffineCoordinateChange (Fin 4 ⊕ Unit)) (z : ℝ) :
    D.AffineLocalProductCoordinateRicciFlat C z ↔ D.EMDEquations := by
  rw [← D.localProductCoordinateRicciFlat_iff_emd z]
  exact C.coordinateRicciFlat_transform_iff
    (kaluzaNormalGaugePointInverse (kaluzaBaseWarp D.phi0)
      (kaluzaFiberWarp D.phi0) D.diagonal)
    (D.localProductMetricJet1 z) (D.localProductMetricJet2 z)

/-- **Assembled smooth coordinate-germ reduction.** The actual `C²` uplift
metric supplies the complete second jet used by the Ricci calculation, and
the resulting convention-fixed coordinate Ricci tensor is flat exactly when
the extracted normal-frame EMD equations hold. -/
theorem conventionKaluzaFieldReduction :
    D.UpliftSecondJetMatches ∧ (D.RicciFlat ↔ D.EMDEquations) :=
  ⟨D.upliftSecondJetMatches, D.conventionKaluzaFieldRicciFlatAt_iff_emd⟩

end KaluzaNormalGaugeFieldsAt

end RainichKaluza
