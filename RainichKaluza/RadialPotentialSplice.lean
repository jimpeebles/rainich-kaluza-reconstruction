import RainichKaluza.RadialGaugePotential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Compactness.Compact

/-!
# The Phase-IV.1 analytic splice: `dF = 0 → d(radialGaugePotential F) = F`

`RadialGaugePotential.lean` proves that the integrated radial derivative
candidate has curvature exactly `F`, and records an honest dominated
differentiation-under-the-integral interface.  This file closes the remaining
Phase-IV.1 gap: it derives that derivative candidate from a single usable
regularity package, discharging every measurability, integrability,
domination, and Lipschitz obligation uniformly — at the level of the full
operator-valued derivative, hence simultaneously for every evaluation
direction.

The package `IsC1ClosedTwoFormOn F DF U` asks for an open patch `U`,
star-shaped about the origin of the local chart, on which `F` is an
alternating two-form field, differentiable with derivative field `DF`, with
`DF` continuous, and with the exterior-derivative cyclic sum vanishing.  These
are exactly the data produced by the Phase-III interface for the closed
physical Maxwell two-form after one `C¹` step of regularity bookkeeping.

Main results:

* `hasFDerivAt_radialGaugePotential`: on the package, the radial gauge
  potential is differentiable at every point of `U`, with the explicit
  integrated derivative `radialPotentialTotalDerivative`.
* `radialGaugePotential_gaugeCurvature`: the antisymmetrized derivative of the
  radial potential is `F`.  This is the desired local theorem `dA = F`.
* `exists_gaugePotentialOn_orbit_of_closed`: existence of a differentiable
  local gauge potential together with the complete gauge orbit `A + dχ` from
  the verified one-form Poincare lemma.

The uniform bounds come from a tube argument: continuity of `(F, DF)` on `U`
bounds both fields on a neighborhood of the compact radial segment, without
any finite-dimensionality or properness assumption on `E`.
-/

set_option maxSynthPendingDepth 2

namespace RainichKaluza

open scoped Interval Topology NNReal
open MeasureTheory Set Filter Metric

section SegmentTube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Segment tube bound.** A map continuous on an open set containing the
radial segment `{t • x : t ∈ [0,1]}` is uniformly bounded on the radial cone
over some ball around `x`, and that cone stays inside the open set.  The
proof is a tube-lemma compactness argument and does not require the ambient
space to be finite-dimensional. -/
theorem exists_segmentTube_bound
    {G : Type*} [NormedAddCommGroup G] {f : E → G} {U : Set E} {x : E}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) :
    ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ Metric.ball x r ⊆ U ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Metric.ball x r,
        t • y ∈ U ∧ ‖f (t • y)‖ ≤ C := by
  have hmcont : Continuous fun p : ℝ × E => p.1 • p.2 :=
    continuous_fst.smul continuous_snd
  have hOopen : IsOpen ((fun p : ℝ × E => p.1 • p.2) ⁻¹' U) :=
    hU.preimage hmcont
  have hKO : Set.Icc (0 : ℝ) 1 ×ˢ ({x} : Set E) ⊆
      (fun p : ℝ × E => p.1 • p.2) ⁻¹' U := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hseg t ht
  have hKcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ ({x} : Set E)) :=
    isCompact_Icc.prod isCompact_singleton
  have hfm : ContinuousOn (fun p : ℝ × E => f (p.1 • p.2))
      ((fun p : ℝ × E => p.1 • p.2) ⁻¹' U) :=
    hf.comp hmcont.continuousOn fun _ hp => hp
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn (hfm.mono hKO)
  have hC0 : 0 ≤ C :=
    le_trans (norm_nonneg _)
      (hC (1, x) ⟨Set.right_mem_Icc.mpr zero_le_one, rfl⟩)
  have hWopen : IsOpen ((fun p : ℝ × E => p.1 • p.2) ⁻¹' U ∩
      (fun p : ℝ × E => ‖f (p.1 • p.2)‖) ⁻¹' Set.Iio (C + 1)) :=
    hfm.norm.isOpen_inter_preimage hOopen isOpen_Iio
  have hKW : Set.Icc (0 : ℝ) 1 ×ˢ ({x} : Set E) ⊆
      (fun p : ℝ × E => p.1 • p.2) ⁻¹' U ∩
        (fun p : ℝ × E => ‖f (p.1 • p.2)‖) ⁻¹' Set.Iio (C + 1) :=
    fun p hp => ⟨hKO hp, lt_of_le_of_lt (hC p hp) (lt_add_one C)⟩
  obtain ⟨w₁, w₂, _, hw₂open, hIccw₁, hxw₂, hprod⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hWopen hKW
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hw₂open x (hxw₂ rfl)
  refine ⟨r, hr, C + 1, by linarith, ?_, ?_⟩
  · intro y hy
    have h1 : ((1 : ℝ), y) ∈ w₁ ×ˢ w₂ :=
      ⟨hIccw₁ (Set.right_mem_Icc.mpr zero_le_one), hball hy⟩
    have hone := (hprod h1).1
    simpa using hone
  · intro t ht y hy
    have hmem : (t, y) ∈ w₁ ×ˢ w₂ := ⟨hIccw₁ ht, hball hy⟩
    exact ⟨(hprod hmem).1, le_of_lt (hprod hmem).2⟩

end SegmentTube

section RegularityPackage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Phase-IV regularity package.** On an open patch `U`, star-shaped
about the origin of the local chart, the two-form field `F` is alternating,
differentiable with derivative field `DF`, the derivative field is
continuous, and the coordinate exterior derivative vanishes (cyclic sum).
This is the single usable hypothesis under which the radial homotopy operator
is a genuine local gauge potential. -/
structure IsC1ClosedTwoFormOn
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E) (U : Set E) : Prop where
  isOpen : IsOpen U
  starShaped : StarConvex ℝ 0 U
  alternating : ∀ x ∈ U, ∀ u v, F x u v = -F x v u
  differentiable : ∀ x ∈ U, HasFDerivAt F (DF x) x
  derivContinuousOn : ContinuousOn DF U
  closed : ∀ x ∈ U, ∀ a b c, DF x a b c + DF x b c a + DF x c a b = 0

namespace IsC1ClosedTwoFormOn

variable {F : E → ContinuousBilinForm E}
  {DF : E → E →L[ℝ] ContinuousBilinForm E} {U : Set E}

/-- Radial segments from the chart origin stay inside the patch. -/
theorem smul_mem (h : IsC1ClosedTwoFormOn F DF U) {x : E} (hx : x ∈ U)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • x ∈ U :=
  h.starShaped.smul_mem hx ht.1 ht.2

/-- Differentiability makes the two-form field continuous on the patch. -/
theorem continuousOn_self (h : IsC1ClosedTwoFormOn F DF U) :
    ContinuousOn F U :=
  fun x hx => ((h.differentiable x hx).continuousAt).continuousWithinAt

end IsC1ClosedTwoFormOn

/-- Frechet differentiation of the doubly evaluated two-form field.  The
derivative in direction `w` is `DF x w a b`. -/
theorem hasFDerivAt_twoFormEvaluation
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E} {x : E}
    (hF : HasFDerivAt F (DF x) x) (a b : E) :
    HasFDerivAt (fun y => F y a b) (((DF x).flip a).flip b) x := by
  have h1 : HasFDerivAt (fun y => F y a) ((DF x).flip a) x := by
    simpa using hF.clm_apply (hasFDerivAt_const a x)
  simpa using h1.clm_apply (hasFDerivAt_const b x)

/-- Differentiating the pointwise alternation identity shows that the
derivative field is automatically alternating in its two form slots.  No
extra package field is needed. -/
theorem IsC1ClosedTwoFormOn.deriv_alternating
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E} {U : Set E}
    (h : IsC1ClosedTwoFormOn F DF U) {x : E} (hx : x ∈ U) (w a b : E) :
    DF x w a b = -DF x w b a := by
  have hzero : (fun y => F y a b + F y b a) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [h.isOpen.mem_nhds hx] with y hy
    have halt := h.alternating y hy a b
    simp [halt]
  have hsum : HasFDerivAt (fun y => F y a b + F y b a)
      (((DF x).flip a).flip b + ((DF x).flip b).flip a) x :=
    (hasFDerivAt_twoFormEvaluation (h.differentiable x hx) a b).add
      (hasFDerivAt_twoFormEvaluation (h.differentiable x hx) b a)
  have hconst : HasFDerivAt (fun y => F y a b + F y b a)
      (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hzero
  have huniq := hsum.unique hconst
  have happ := congrArg (fun T : E →L[ℝ] ℝ => T w) huniq
  simp only [add_apply, ContinuousLinearMap.flip_apply,
    zero_apply] at happ
  linarith

end RegularityPackage

section DerivativeIntegrand

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Operator-valued derivative integrand of the radial potential: the
`y`-derivative of `y ↦ radialGaugeIntegrand F y t` at `x`.  Evaluated on
`(u, v)` it is exactly `radialPotentialDerivativeIntegrand F DF x u v t`. -/
noncomputable def radialGaugeIntegrandDerivative
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E)
    (x : E) (t : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  t ^ 2 • (DF (t • x)).flip x + t • F (t • x)

@[simp] theorem radialGaugeIntegrandDerivative_apply
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E)
    (x : E) (t : ℝ) (u v : E) :
    radialGaugeIntegrandDerivative F DF x t u v =
      radialPotentialDerivativeIntegrand F DF x u v t := by
  simp [radialGaugeIntegrandDerivative, radialPotentialDerivativeIntegrand]

/-- Chain-rule differentiation of the radial integrand in its base point.
This is the analytic content the dominated-integral interface consumes. -/
theorem hasFDerivAt_radialGaugeIntegrand
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E} {y : E} (t : ℝ)
    (hF : HasFDerivAt F (DF (t • y)) (t • y)) :
    HasFDerivAt (fun z => radialGaugeIntegrand F z t)
      (radialGaugeIntegrandDerivative F DF y t) y := by
  have hline : HasFDerivAt (fun z : E => t • z)
      (t • ContinuousLinearMap.id ℝ E) y :=
    (hasFDerivAt_id y).const_smul t
  have hcomp : HasFDerivAt (fun z => F (t • z))
      ((DF (t • y)).comp (t • ContinuousLinearMap.id ℝ E)) y := by
    simpa [Function.comp_def] using hF.comp y hline
  have happly := (hcomp.clm_apply (hasFDerivAt_id y)).const_smul t
  have hderiv :
      radialGaugeIntegrandDerivative F DF y t =
        t • ((F (t • y)).comp (ContinuousLinearMap.id ℝ E) +
          ((DF (t • y)).comp
            (t • ContinuousLinearMap.id ℝ E)).flip y) := by
    ext u v
    simp [radialGaugeIntegrandDerivative]
    ring
  unfold radialGaugeIntegrand
  rw [hderiv]
  exact happly

/-- Norm control for the operator-valued integrand derivative on a tube. -/
theorem radialGaugeIntegrandDerivative_norm_le
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E}
    {C r : ℝ} {x y : E} (hy : y ∈ Metric.ball x r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hDFb : ‖DF (t • y)‖ ≤ C) (hFb : ‖F (t • y)‖ ≤ C) :
    ‖radialGaugeIntegrandDerivative F DF y t‖ ≤ C * (‖x‖ + r) + C := by
  have hrpos : (0 : ℝ) < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp hy)
  have hyn : ‖y‖ ≤ ‖x‖ + r := by
    have hlt : ‖y - x‖ < r := mem_ball_iff_norm.mp hy
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + r := by linarith
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hFb
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  calc ‖radialGaugeIntegrandDerivative F DF y t‖
      ≤ ‖t ^ 2 • (DF (t • y)).flip y‖ + ‖t • F (t • y)‖ :=
        norm_add_le _ _
    _ = t ^ 2 * ‖(DF (t • y)).flip y‖ + t * ‖F (t • y)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2),
          abs_of_nonneg ht0]
    _ ≤ 1 * (‖DF (t • y)‖ * ‖y‖) + 1 * ‖F (t • y)‖ := by
        have hflip : ‖(DF (t • y)).flip y‖ ≤ ‖DF (t • y)‖ * ‖y‖ := by
          calc ‖(DF (t • y)).flip y‖
              ≤ ‖(DF (t • y)).flip‖ * ‖y‖ :=
                ContinuousLinearMap.le_opNorm _ y
            _ = ‖DF (t • y)‖ * ‖y‖ := by
                rw [ContinuousLinearMap.opNorm_flip]
        have hsq : t ^ 2 ≤ 1 := by nlinarith
        have h1 : t ^ 2 * ‖(DF (t • y)).flip y‖ ≤
            1 * (‖DF (t • y)‖ * ‖y‖) := by
          have := mul_le_mul hsq hflip (norm_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 1)
          simpa using this
        have h2 : t * ‖F (t • y)‖ ≤ 1 * ‖F (t • y)‖ :=
          mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        linarith
    _ ≤ C * (‖x‖ + r) + C := by
        have hxr0 : 0 ≤ ‖x‖ + r := by
          have := norm_nonneg x
          linarith
        have hDFy : ‖DF (t • y)‖ * ‖y‖ ≤ C * (‖x‖ + r) :=
          mul_le_mul hDFb hyn (norm_nonneg _) hC0
        linarith

end DerivativeIntegrand

section MainSplice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E → ContinuousBilinForm E}
  {DF : E → E →L[ℝ] ContinuousBilinForm E} {U : Set E}

/-- Continuity of the radial integrand in its one-dimensional variable, for
any base point whose radial segment lies in the patch. -/
theorem continuousOn_radialGaugeIntegrand
    (h : IsC1ClosedTwoFormOn F DF U) {y : E}
    (hyseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • y ∈ U) :
    ContinuousOn (fun t => radialGaugeIntegrand F y t)
      (Set.Icc (0 : ℝ) 1) := by
  have hline : ContinuousOn (fun t : ℝ => t • y) (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have hFy : ContinuousOn (fun t : ℝ => F (t • y)) (Set.Icc (0 : ℝ) 1) :=
    h.continuousOn_self.comp hline fun t ht => hyseg t ht
  have happ : ContinuousOn (fun t : ℝ => F (t • y) y)
      (Set.Icc (0 : ℝ) 1) := hFy.clm_apply continuousOn_const
  exact continuousOn_id.smul happ

/-- Continuity of the operator-valued derivative integrand in its
one-dimensional variable. -/
theorem continuousOn_radialGaugeIntegrandDerivative
    (h : IsC1ClosedTwoFormOn F DF U) {x : E} (hx : x ∈ U) :
    ContinuousOn (radialGaugeIntegrandDerivative F DF x)
      (Set.Icc (0 : ℝ) 1) := by
  have hline : ContinuousOn (fun t : ℝ => t • x) (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have hmaps : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U :=
    fun t ht => h.smul_mem hx ht
  have hDFt : ContinuousOn (fun t : ℝ => DF (t • x))
      (Set.Icc (0 : ℝ) 1) := h.derivContinuousOn.comp hline hmaps
  have hFt : ContinuousOn (fun t : ℝ => F (t • x))
      (Set.Icc (0 : ℝ) 1) := h.continuousOn_self.comp hline hmaps
  have hflip : ContinuousOn (fun t : ℝ => (DF (t • x)).flip x)
      (Set.Icc (0 : ℝ) 1) := by
    have hcomp : ContinuousOn (fun t : ℝ =>
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) x).comp (DF (t • x)))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.clm_comp hDFt
    refine ContinuousOn.congr hcomp fun t _ => ?_
    ext u
    simp
  exact (((continuous_pow 2).continuousOn).smul hflip).add
    (continuousOn_id.smul hFt)

/-- The integrated operator-valued derivative of the radial potential. -/
noncomputable def radialPotentialTotalDerivative
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, radialGaugeIntegrandDerivative F DF x t

/-- **The Phase-IV.1 splice.** Under the `C¹` closed regularity package, the
radial gauge potential is Frechet differentiable at every point of the patch,
and its derivative is the integrated derivative candidate.  All dominated
differentiation-under-the-integral hypotheses are discharged uniformly at the
operator level, hence for every evaluation direction simultaneously. -/
theorem hasFDerivAt_radialGaugePotential
    (h : IsC1ClosedTwoFormOn F DF U) {x : E} (hx : x ∈ U) :
    HasFDerivAt (radialGaugePotential F)
      (radialPotentialTotalDerivative F DF x) x := by
  obtain ⟨r, hr, C, hC0, hballU, htube⟩ :=
    exists_segmentTube_bound (f := fun y => (F y, DF y)) h.isOpen
      (h.continuousOn_self.prodMk h.derivContinuousOn)
      (fun t ht => h.smul_mem hx ht)
  have htubeF : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Metric.ball x r,
      t • y ∈ U ∧ ‖F (t • y)‖ ≤ C ∧ ‖DF (t • y)‖ ≤ C := by
    intro t ht y hy
    refine ⟨(htube t ht y hy).1, ?_, ?_⟩
    · exact le_trans (norm_fst_le (F (t • y), DF (t • y)))
        (htube t ht y hy).2
    · exact le_trans (norm_snd_le (F (t • y), DF (t • y)))
        (htube t ht y hy).2
  have hIccOf : ∀ {t : ℝ}, t ∈ Ι (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact Set.Ioc_subset_Icc_self ht
  set M : ℝ := C * (‖x‖ + r) + C with hM
  have hM0 : 0 ≤ M := by
    have hxr0 : 0 ≤ ‖x‖ + r := by
      have := norm_nonneg x
      linarith
    have := mul_nonneg hC0 hxr0
    simp only [hM]
    linarith
  -- the seven dominated-differentiation obligations
  have hs : Metric.ball x r ∈ 𝓝 x := Metric.ball_mem_nhds x hr
  have hF_meas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun t => radialGaugeIntegrand F y t)
        (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    have hcont := continuousOn_radialGaugeIntegrand h
      (fun t ht => (htubeF t ht y hy).1)
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact hcont.mono (by
      rw [Set.uIoc_of_le zero_le_one]
      exact Set.Ioc_subset_Icc_self)
  have hF_int : IntervalIntegrable
      (fun t => radialGaugeIntegrand F x t) volume 0 1 := by
    have hcont := continuousOn_radialGaugeIntegrand h
      (fun t ht => h.smul_mem hx ht)
    exact (hcont.mono
      (le_of_eq (Set.uIcc_of_le zero_le_one))).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable
      (radialGaugeIntegrandDerivative F DF x)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact (continuousOn_radialGaugeIntegrandDerivative h hx).mono (by
      rw [Set.uIoc_of_le zero_le_one]
      exact Set.Ioc_subset_Icc_self)
  have h_lip : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
      LipschitzOnWith (Real.nnabs M)
        (fun y => radialGaugeIntegrand F y t) (Metric.ball x r) := by
    refine MeasureTheory.ae_of_all _ fun t ht => ?_
    have htIcc := hIccOf ht
    refine (convex_ball x r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun y => radialGaugeIntegrandDerivative F DF y t)
      (fun y hy => ?_) (fun y hy => ?_)
    · exact (hasFDerivAt_radialGaugeIntegrand t
        (h.differentiable _ (htubeF t htIcc y hy).1)).hasFDerivWithinAt
    · have hnorm := radialGaugeIntegrandDerivative_norm_le hy htIcc
        (htubeF t htIcc y hy).2.2 (htubeF t htIcc y hy).2.1
      rw [← NNReal.coe_le_coe]
      calc (‖radialGaugeIntegrandDerivative F DF y t‖₊ : ℝ)
          = ‖radialGaugeIntegrandDerivative F DF y t‖ := coe_nnnorm _
        _ ≤ M := hnorm
        _ = |M| := (abs_of_nonneg hM0).symm
        _ = (Real.nnabs M : ℝ) := (Real.coe_nnabs M).symm
  have hbound : IntervalIntegrable (fun _ : ℝ => M) volume 0 1 :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0 : ℝ) 1 →
      HasFDerivAt (fun y => radialGaugeIntegrand F y t)
        (radialGaugeIntegrandDerivative F DF x t) x := by
    refine MeasureTheory.ae_of_all _ fun t ht => ?_
    exact hasFDerivAt_radialGaugeIntegrand t
      (h.differentiable _ (h.smul_mem hx (hIccOf ht)))
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (bound := fun _ => M)
    (F := fun y t => radialGaugeIntegrand F y t)
    (F' := radialGaugeIntegrandDerivative F DF x)
    hs hF_meas hF_int hF'_meas h_lip hbound h_diff
  exact hmain.2

/-- Evaluating the integrated operator derivative recovers the scalar
derivative candidate of `RadialGaugePotential.lean`. -/
theorem radialPotentialTotalDerivative_apply
    (h : IsC1ClosedTwoFormOn F DF U) {x : E} (hx : x ∈ U) (u v : E) :
    radialPotentialTotalDerivative F DF x u v =
      radialPotentialDerivativeCandidate F DF x u v := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le zero_le_one
  have hD := continuousOn_radialGaugeIntegrandDerivative h hx
  have hDint : IntervalIntegrable
      (radialGaugeIntegrandDerivative F DF x) volume 0 1 :=
    (hD.mono (le_of_eq huIcc)).intervalIntegrable
  have hDu : IntervalIntegrable
      (fun t => radialGaugeIntegrandDerivative F DF x t u) volume 0 1 :=
    ((hD.clm_apply continuousOn_const).mono
      (le_of_eq huIcc)).intervalIntegrable
  rw [radialPotentialTotalDerivative,
    ContinuousLinearMap.intervalIntegral_apply hDint u,
    ContinuousLinearMap.intervalIntegral_apply hDu v,
    radialPotentialDerivativeCandidate]
  exact intervalIntegral.integral_congr fun t _ =>
    radialGaugeIntegrandDerivative_apply F DF x t u v

/-- **`dA = F` for the radial gauge potential.** On the regularity package,
the antisymmetrized Frechet derivative of the radial gauge potential is
exactly the supplied closed two-form.  Together with
`radialGaugePotential_self_eq_zero` this closes the constructive local
two-form Poincare step of Phase IV.1. -/
theorem radialGaugePotential_gaugeCurvature
    (h : IsC1ClosedTwoFormOn F DF U) {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (radialGaugePotential F) x u v -
        fderiv ℝ (radialGaugePotential F) x v u = F x u v := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le zero_le_one
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, t • x ∈ U := by
    intro t ht
    exact h.smul_mem hx (huIcc ▸ ht)
  rw [(hasFDerivAt_radialGaugePotential h hx).fderiv,
    radialPotentialTotalDerivative_apply h hx u v,
    radialPotentialTotalDerivative_apply h hx v u]
  -- integrabilities of the three scalar integrands
  have hD := continuousOn_radialGaugeIntegrandDerivative h hx
  have hintD : ∀ a b : E, IntervalIntegrable
      (radialPotentialDerivativeIntegrand F DF x a b) volume 0 1 := by
    intro a b
    have h1 : ContinuousOn
        (fun t => radialGaugeIntegrandDerivative F DF x t a b)
        (Set.Icc (0 : ℝ) 1) :=
      (hD.clm_apply continuousOn_const).clm_apply continuousOn_const
    have h2 : ContinuousOn
        (radialPotentialDerivativeIntegrand F DF x a b)
        (Set.Icc (0 : ℝ) 1) := by
      refine ContinuousOn.congr h1 fun t _ => ?_
      exact (radialGaugeIntegrandDerivative_apply F DF x t a b).symm
    exact (h2.mono (le_of_eq huIcc)).intervalIntegrable
  have hline : ContinuousOn (fun t : ℝ => t • x) (Set.Icc (0 : ℝ) 1) :=
    (continuous_id.smul continuous_const).continuousOn
  have hmaps : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U :=
    fun t ht => h.smul_mem hx ht
  have hDFt : ContinuousOn (fun t : ℝ => DF (t • x))
      (Set.Icc (0 : ℝ) 1) := h.derivContinuousOn.comp hline hmaps
  have hFt : ContinuousOn (fun t : ℝ => F (t • x))
      (Set.Icc (0 : ℝ) 1) := h.continuousOn_self.comp hline hmaps
  have hintCurv : IntervalIntegrable
      (radialCurvatureIntegrand F DF x u v) volume 0 1 := by
    have hDF3 : ContinuousOn (fun t : ℝ => DF (t • x) x u v)
        (Set.Icc (0 : ℝ) 1) :=
      ((hDFt.clm_apply continuousOn_const).clm_apply
        continuousOn_const).clm_apply continuousOn_const
    have hF2 : ContinuousOn (fun t : ℝ => F (t • x) u v)
        (Set.Icc (0 : ℝ) 1) :=
      (hFt.clm_apply continuousOn_const).clm_apply continuousOn_const
    have hcont : ContinuousOn
        (radialCurvatureIntegrand F DF x u v) (Set.Icc (0 : ℝ) 1) := by
      have hsum : ContinuousOn (fun t : ℝ =>
          t ^ 2 * DF (t • x) x u v + 2 * t * F (t • x) u v)
          (Set.Icc (0 : ℝ) 1) :=
        (((continuous_pow 2).continuousOn).mul hDF3).add
          ((((continuous_const.mul continuous_id)).continuousOn).mul hF2)
      exact hsum
    exact (hcont.mono (le_of_eq huIcc)).intervalIntegrable
  refine radialPotentialDerivativeCandidate_curvature x u v
    (fun t ht a b => h.alternating _ (hmem t ht) a b)
    (fun t ht w a b => h.deriv_alternating (hmem t ht) w a b)
    (fun t ht a b c => h.closed _ (hmem t ht) a b c)
    (fun t ht => ?_) (hintD u v) (hintD v u) hintCurv
  -- curve differentiation along the radial segment
  have hlineDeriv : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have heval := hasFDerivAt_twoFormEvaluation
    (h.differentiable _ (hmem t ht)) u v
  have hcomp := heval.comp_hasDerivAt t hlineDeriv
  simpa [Function.comp_def] using hcomp

end MainSplice

section GaugePotentialField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E → ContinuousBilinForm E}
  {DF : E → E →L[ℝ] ContinuousBilinForm E} {U : Set E}

/-- A differentiable one-form field whose coordinate exterior derivative is
`F` on the patch.  This is the local statement `dA = F`. -/
def IsGaugePotentialOn
    (A : E → E →L[ℝ] ℝ) (F : E → ContinuousBilinForm E)
    (U : Set E) : Prop :=
  DifferentiableOn ℝ A U ∧
    ∀ x ∈ U, ∀ u v,
      fderiv ℝ A x u v - fderiv ℝ A x v u = F x u v

/-- The radial gauge potential is a genuine differentiable local gauge
potential on the whole patch. -/
theorem radialGaugePotential_isGaugePotentialOn
    (h : IsC1ClosedTwoFormOn F DF U) :
    IsGaugePotentialOn (radialGaugePotential F) F U := by
  constructor
  · intro x hx
    exact (hasFDerivAt_radialGaugePotential
      h hx).differentiableAt.differentiableWithinAt
  · intro x hx u v
    exact radialGaugePotential_gaugeCurvature h hx u v

/-- **Local two-form Poincare lemma, existence half.** Every `C¹` closed
alternating two-form field on a star-shaped open patch has a differentiable
local gauge potential: `dF = 0 → ∃ A, dA = F`. -/
theorem exists_gaugePotentialOn_of_closed
    (h : IsC1ClosedTwoFormOn F DF U) :
    ∃ A : E → E →L[ℝ] ℝ, IsGaugePotentialOn A F U :=
  ⟨radialGaugePotential F, radialGaugePotential_isGaugePotentialOn h⟩

/-- Any two differentiable local gauge potentials for the same two-form are
related by an exact scalar differential.  This is the uniqueness half of the
local Poincare lemma, inherited from the verified one-form theorem. -/
theorem gaugePotentialOn_unique_up_to_gaugeParameter
    {A A' : E → E →L[ℝ] ℝ}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hA : IsGaugePotentialOn A F U) (hA' : IsGaugePotentialOn A' F U) :
    ∃ chi : E → ℝ, IsScalarPotentialOn chi (A' - A) U := by
  apply exists_localGaugeParameter_of_same_curvature hconvex hopen
  exact ⟨hA.1, hA'.1, fun x hx u v =>
    (hA.2 x hx u v).trans (hA'.2 x hx u v).symm⟩

/-- **Phase-IV.1 exit theorem.** On an open convex patch around the chart
origin, a `C¹` closed alternating two-form field has a differentiable local
gauge potential, and the complete local potential orbit is `A + dχ`: any
second potential differs from the constructed one by the differential of a
scalar gauge parameter, itself unique up to an additive constant. -/
theorem exists_gaugePotentialOn_orbit_of_closed
    (h : IsC1ClosedTwoFormOn F DF U) (hconvex : Convex ℝ U) :
    ∃ A : E → E →L[ℝ] ℝ, IsGaugePotentialOn A F U ∧
      ∀ A' : E → E →L[ℝ] ℝ, IsGaugePotentialOn A' F U →
        ∃ chi : E → ℝ, IsScalarPotentialOn chi (A' - A) U := by
  refine ⟨radialGaugePotential F,
    radialGaugePotential_isGaugePotentialOn h, fun A' hA' => ?_⟩
  exact gaugePotentialOn_unique_up_to_gaugeParameter hconvex h.isOpen
    (radialGaugePotential_isGaugePotentialOn h) hA'

end GaugePotentialField

end RainichKaluza
