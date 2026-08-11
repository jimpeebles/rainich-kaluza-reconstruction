import RainichKaluza.PhaseIVReadiness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Radial gauge potentials and Kaluza gauge invariance

This file starts Phase IV with two pieces that can be proved without assuming
the still-missing two-form Poincare theorem.

* It defines the standard radial homotopy candidate
  `A_x(v) = integral_0^1 t F_(t x)(x,v) dt` for a continuous two-form field,
  and proves its radial-gauge condition `A_x(x)=0` for alternating `F`.
  Proving `dA=F` for closed `F` is deliberately left as the next analytic
  theorem: it requires a justified derivative-under-the-integral argument.
* It separates pointwise first-jet reconstruction from that analytic theorem,
  proves the exact gauge freedom of the jet, and verifies gauge invariance of
  the Kaluza fiber one-form and metric evaluation.

The distinction matters: the pointwise jet theorem below is algebraic and is
not presented as a local existence theorem for a gauge-potential field.
-/

namespace RainichKaluza

open scoped Interval Topology
open MeasureTheory
open TopologicalSpace Filter

section RadialHomotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A field of continuous bilinear forms is alternating when each value is a
two-form. -/
def IsAlternatingTwoFormField (F : E → ContinuousBilinForm E) : Prop :=
  ∀ x u v, F x u v = -F x v u

/-- The integrand in the radial homotopy operator on a two-form. -/
noncomputable def radialGaugeIntegrand
    (F : E → ContinuousBilinForm E) (x : E) (t : ℝ) : E →L[ℝ] ℝ :=
  t • (F (t • x) x)

/-- The standard radial-gauge candidate for a potential of `F` on a
star-shaped coordinate patch centered at the origin. -/
noncomputable def radialGaugePotential
    (F : E → ContinuousBilinForm E) (x : E) : E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, radialGaugeIntegrand F x t

/-- A continuous two-form field gives an interval-integrable radial
integrand. -/
theorem radialGaugeIntegrand_intervalIntegrable
    {F : E → ContinuousBilinForm E} (hF : Continuous F) (x : E) :
    IntervalIntegrable (radialGaugeIntegrand F x) volume 0 1 := by
  apply Continuous.intervalIntegrable
  unfold radialGaugeIntegrand
  fun_prop

/-- The radial homotopy candidate vanishes at the center of the patch. -/
@[simp] theorem radialGaugePotential_zero
    (F : E → ContinuousBilinForm E) :
    radialGaugePotential F 0 = 0 := by
  simp [radialGaugePotential, radialGaugeIntegrand]

/-- For an alternating field, the radial homotopy candidate satisfies radial
gauge: `A_x(x)=0`. -/
theorem radialGaugePotential_self_eq_zero
    {F : E → ContinuousBilinForm E} (hFcont : Continuous F)
    (hFalt : IsAlternatingTwoFormField F) (x : E) :
    radialGaugePotential F x x = 0 := by
  rw [radialGaugePotential,
    ContinuousLinearMap.intervalIntegral_apply
      (radialGaugeIntegrand_intervalIntegrable hFcont x) x]
  have hzero : ∀ t : ℝ, radialGaugeIntegrand F x t x = 0 := by
    intro t
    have hdiag := hFalt (t • x) x x
    have hdiagZero : F (t • x) x x = 0 := by linarith
    unfold radialGaugeIntegrand
    simp [hdiagZero]
  simp_rw [hzero]
  exact intervalIntegral.integral_zero

/-- Evaluation of the Bochner-valued radial potential is the corresponding
scalar interval integral. -/
theorem radialGaugePotential_apply_eq_integral
    {F : E → ContinuousBilinForm E} (hF : Continuous F) (x v : E) :
    radialGaugePotential F x v =
      ∫ t in (0 : ℝ)..1, radialGaugeIntegrand F x t v := by
  rw [radialGaugePotential,
    ContinuousLinearMap.intervalIntegral_apply
      (radialGaugeIntegrand_intervalIntegrable hF x) v]

/-- Honest componentwise differentiation-under-the-integral bridge for the
radial potential.  This is a specialization of Mathlib's dominated local
Lipschitz theorem; unlike a formal manipulation of the integral, all
measurability, integrability, and uniform domination obligations remain
visible. -/
theorem hasFDerivAt_radialGaugePotentialEvaluation_of_dominated_loc_of_lip
    {F : E → ContinuousBilinForm E}
    {D : ℝ → E →L[ℝ] ℝ} {x v : E} {s : Set E}
    {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 x)
    (hFmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (fun t => radialGaugeIntegrand F y t v)
        (volume.restrict (Set.uIoc 0 1)))
    (hFint : IntervalIntegrable
      (fun t => radialGaugeIntegrand F x t v) volume 0 1)
    (hDmeas : AEStronglyMeasurable D
      (volume.restrict (Set.uIoc 0 1)))
    (hlip : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      LipschitzOnWith (Real.nnabs (bound t))
        (fun y => radialGaugeIntegrand F y t v) s)
    (hbound : IntervalIntegrable bound volume 0 1)
    (hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      HasFDerivAt (fun y => radialGaugeIntegrand F y t v) (D t) x) :
    IntervalIntegrable D volume 0 1 ∧
      HasFDerivAt
        (fun y => ∫ t in (0 : ℝ)..1, radialGaugeIntegrand F y t v)
        (∫ t in (0 : ℝ)..1, D t) x :=
  intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    hs hFmeas hFint hDmeas hlip hbound hdiff

/-- The scalar integrand obtained by formally differentiating the radial
potential at `x` in direction `u` and evaluating it on `v`. -/
noncomputable def radialPotentialDerivativeIntegrand
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E)
    (x u v : E) (t : ℝ) : ℝ :=
  t ^ 2 * DF (t • x) u x v + t * F (t • x) u v

/-- The corresponding integrated first-derivative candidate.  The separate
analytic task is to prove that this is genuinely the Frechet derivative of
`radialGaugePotential F`. -/
noncomputable def radialPotentialDerivativeCandidate
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E)
    (x u v : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, radialPotentialDerivativeIntegrand F DF x u v t

/-- The one-variable integrand whose integral is the endpoint value `F_x`.
It is the derivative of `t ↦ t² F_(t x)(u,v)`. -/
noncomputable def radialCurvatureIntegrand
    (F : E → ContinuousBilinForm E)
    (DF : E → E →L[ℝ] ContinuousBilinForm E)
    (x u v : E) (t : ℝ) : ℝ :=
  t ^ 2 * DF (t • x) x u v + 2 * t * F (t • x) u v

/-- Fundamental-calculus core of the radial homotopy identity. -/
theorem integral_radialCurvatureIntegrand_eq
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E}
    (x u v : E)
    (hcurve : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => F (s • x) u v) (DF (t • x) x u v) t)
    (hint : IntervalIntegrable
      (radialCurvatureIntegrand F DF x u v) volume 0 1) :
    (∫ t in (0 : ℝ)..1, radialCurvatureIntegrand F DF x u v t) =
      F x u v := by
  have hprod : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s ^ 2 * F (s • x) u v)
        (radialCurvatureIntegrand F DF x u v t) t := by
    intro t _
    have h := ((hasDerivAt_id t).pow 2).mul (hcurve t)
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [] with s
      rfl
    · simp [radialCurvatureIntegrand, Function.id_def, Pi.pow_apply]
      ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod hint
  simpa using hFTC

/-- Closedness converts antisymmetrization of the formally differentiated
radial potential into the one-variable fundamental-calculus integrand. -/
theorem radialPotentialDerivativeIntegrand_antisymmetrize
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E}
    (hFalt : ∀ y a b, F y a b = -F y b a)
    (hDFalt : ∀ y w a b, DF y w a b = -DF y w b a)
    (hclosed : ∀ y a b c,
      DF y a b c + DF y b c a + DF y c a b = 0)
    (x u v : E) (t : ℝ) :
    radialPotentialDerivativeIntegrand F DF x u v t -
        radialPotentialDerivativeIntegrand F DF x v u t =
      radialCurvatureIntegrand F DF x u v t := by
  have hF := hFalt (t • x) v u
  have hDF := hDFalt (t • x) u x v
  have hd := hclosed (t • x) u v x
  unfold radialPotentialDerivativeIntegrand radialCurvatureIntegrand
  rw [hF, hDF]
  ring_nf at hd ⊢
  linear_combination -(t ^ 2) * hd

/-- **Curvature identity for the Phase-IV derivative candidate.** Under
alternation, differential closedness, curve differentiation, and the stated
integrability hypotheses, antisymmetrizing the integrated candidate gives
the original two-form. -/
theorem radialPotentialDerivativeCandidate_curvature
    {F : E → ContinuousBilinForm E}
    {DF : E → E →L[ℝ] ContinuousBilinForm E}
    (hFalt : ∀ y a b, F y a b = -F y b a)
    (hDFalt : ∀ y w a b, DF y w a b = -DF y w b a)
    (hclosed : ∀ y a b c,
      DF y a b c + DF y b c a + DF y c a b = 0)
    (x u v : E)
    (hcurve : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => F (s • x) u v) (DF (t • x) x u v) t)
    (hintDuv : IntervalIntegrable
      (radialPotentialDerivativeIntegrand F DF x u v) volume 0 1)
    (hintDvu : IntervalIntegrable
      (radialPotentialDerivativeIntegrand F DF x v u) volume 0 1)
    (hintCurv : IntervalIntegrable
      (radialCurvatureIntegrand F DF x u v) volume 0 1) :
    radialPotentialDerivativeCandidate F DF x u v -
        radialPotentialDerivativeCandidate F DF x v u =
      F x u v := by
  calc
    radialPotentialDerivativeCandidate F DF x u v -
        radialPotentialDerivativeCandidate F DF x v u =
        ∫ t in (0 : ℝ)..1,
          (radialPotentialDerivativeIntegrand F DF x u v t -
            radialPotentialDerivativeIntegrand F DF x v u t) := by
              symm
              exact intervalIntegral.integral_sub hintDuv hintDvu
    _ = ∫ t in (0 : ℝ)..1, radialCurvatureIntegrand F DF x u v t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact radialPotentialDerivativeIntegrand_antisymmetrize
        hFalt hDFalt hclosed x u v t
    _ = F x u v :=
      integral_radialCurvatureIntegrand_eq x u v hcurve hintCurv

end RadialHomotopy

section GaugePotentialJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Antisymmetrization of the first derivative of a one-form.  This is the
pointwise coordinate value of its exterior derivative. -/
noncomputable def gaugeCurvatureJet (D : ContinuousBilinForm E) (u v : E) : ℝ :=
  D u v - D v u

/-- `D` is a pointwise first-derivative jet for a potential of `F`. -/
def IsGaugePotentialJet
    (D F : ContinuousBilinForm E) : Prop :=
  ∀ u v, gaugeCurvatureJet D u v = F u v

/-- Every alternating two-form has a pointwise potential jet.  This is only
linear algebra; it is not the local Poincare lemma for a field of two-forms. -/
theorem exists_gaugePotentialJet_of_alternating
    (F : ContinuousBilinForm E)
    (hF : ∀ u v, F u v = -F v u) :
    ∃ D : ContinuousBilinForm E, IsGaugePotentialJet D F := by
  refine ⟨(1 / 2 : ℝ) • F, ?_⟩
  intro u v
  simp only [gaugeCurvatureJet, smul_apply, smul_eq_mul]
  rw [hF]
  ring

/-- Adding a symmetric first-derivative jet is a pointwise gauge
transformation and leaves curvature unchanged. -/
theorem gaugeCurvatureJet_add_symmetric
    (D H : ContinuousBilinForm E)
    (hH : ∀ u v, H u v = H v u) (u v : E) :
    gaugeCurvatureJet (D + H) u v = gaugeCurvatureJet D u v := by
  simp only [gaugeCurvatureJet, add_apply]
  rw [hH]
  ring

/-- Two potential jets with equal curvature differ by a symmetric jet. -/
theorem gaugePotentialJets_difference_symmetric
    {D D' : ContinuousBilinForm E}
    (hcurv : ∀ u v, gaugeCurvatureJet D u v = gaugeCurvatureJet D' u v) :
    ∀ u v, (D - D') u v = (D - D') v u := by
  intro u v
  have h := hcurv u v
  simp only [gaugeCurvatureJet, sub_apply] at h ⊢
  linarith

end GaugePotentialJets

section LocalGaugeOrbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equality of the exterior derivatives of two differentiable one-form
fields, written in local Frechet coordinates. -/
def HaveSameGaugeCurvatureOn
    (A A' : E → E →L[ℝ] ℝ) (U : Set E) : Prop :=
  DifferentiableOn ℝ A U ∧ DifferentiableOn ℝ A' U ∧
    ∀ x ∈ U, ∀ u v,
      fderiv ℝ A x u v - fderiv ℝ A x v u =
        fderiv ℝ A' x u v - fderiv ℝ A' x v u

/-- **Local gauge-orbit theorem.** On an open convex patch, two differentiable
one-form potentials with the same curvature differ by the differential of a
scalar gauge parameter. -/
theorem exists_localGaugeParameter_of_same_curvature
    {A A' : E → E →L[ℝ] ℝ} {U : Set E}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hsame : HaveSameGaugeCurvatureOn A A' U) :
    ∃ chi : E → ℝ, IsScalarPotentialOn chi (A' - A) U := by
  apply exists_scalarPotential_of_closed hconvex hopen
  refine ⟨hsame.2.1.sub hsame.1, ?_⟩
  intro x hx u v
  have hA : DifferentiableAt ℝ A x :=
    (hsame.1 x hx).differentiableAt (hopen.mem_nhds hx)
  have hA' : DifferentiableAt ℝ A' x :=
    (hsame.2.1 x hx).differentiableAt (hopen.mem_nhds hx)
  have hcurv := hsame.2.2 x hx u v
  rw [fderiv_sub hA' hA]
  simp only [sub_apply]
  linarith

/-- Gauge parameters relating the same two potentials are unique up to an
additive constant on the convex patch. -/
theorem localGaugeParameter_unique_up_to_constant
    {A A' : E → E →L[ℝ] ℝ} {U : Set E}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    {chi psi : E → ℝ}
    (hchi : IsScalarPotentialOn chi (A' - A) U)
    (hpsi : IsScalarPotentialOn psi (A' - A) U) :
    ∃ c : ℝ, U.EqOn chi (fun x => psi x + c) :=
  scalarPotential_unique_up_to_constant hconvex hopen hchi hpsi

end LocalGaugeOrbit

section KaluzaGaugeInvariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gauge shift of the four-dimensional connection one-form. -/
def gaugeShiftOneForm
    (A dchi : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  A + dchi

/-- Compensating shift of the fifth-coordinate component of a tangent
vector. -/
def gaugeShiftFiber
    (c : ℝ) (dchi : E →L[ℝ] ℝ) (X : E) (xi : ℝ) : ℝ :=
  xi - c * dchi X

/-- Evaluation of the Kaluza fiber one-form `dz + c A`. -/
def kaluzaFiberOneForm
    (c : ℝ) (A : E →L[ℝ] ℝ) (X : E) (xi : ℝ) : ℝ :=
  xi + c * A X

/-- The fiber one-form is exactly invariant under the simultaneous connection
and fifth-coordinate gauge shifts. -/
theorem kaluzaFiberOneForm_gauge_invariant
    (c : ℝ) (A dchi : E →L[ℝ] ℝ) (X : E) (xi : ℝ) :
    kaluzaFiberOneForm c (gaugeShiftOneForm A dchi) X
        (gaugeShiftFiber c dchi X xi) =
      kaluzaFiberOneForm c A X xi := by
  simp [kaluzaFiberOneForm, gaugeShiftOneForm, gaugeShiftFiber]
  ring

/-- Pointwise evaluation of the warped Kaluza metric
`u g + v (dz + c A)^2`. -/
noncomputable def kaluzaMetricEvaluation
    (u v c : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (X : E) (xi : ℝ) : ℝ :=
  u * g X X + v * (kaluzaFiberOneForm c A X xi) ^ 2

/-- Full bilinear pairing of the convention-independent warped Kaluza block
metric. -/
noncomputable def kaluzaMetricPairing
    (u v c : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (X Y : E) (xi eta : ℝ) : ℝ :=
  u * g X Y +
    v * kaluzaFiberOneForm c A X xi * kaluzaFiberOneForm c A Y eta

/-- The quadratic metric evaluation is the diagonal of the full pairing. -/
theorem kaluzaMetricEvaluation_eq_pairing_self
    (u v c : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (X : E) (xi : ℝ) :
    kaluzaMetricEvaluation u v c g A X xi =
      kaluzaMetricPairing u v c g A X X xi xi := by
  unfold kaluzaMetricEvaluation kaluzaMetricPairing
  ring

/-- A symmetric base metric produces a symmetric Kaluza block metric. -/
theorem kaluzaMetricPairing_symmetric
    (u v c : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (hg : ∀ X Y, g X Y = g Y X)
    (X Y : E) (xi eta : ℝ) :
    kaluzaMetricPairing u v c g A X Y xi eta =
      kaluzaMetricPairing u v c g A Y X eta xi := by
  unfold kaluzaMetricPairing
  rw [hg]
  ring

/-- The assembled Kaluza metric evaluation is gauge invariant. -/
theorem kaluzaMetricEvaluation_gauge_invariant
    (u v c : ℝ) (g : ContinuousBilinForm E)
    (A dchi : E →L[ℝ] ℝ) (X : E) (xi : ℝ) :
    kaluzaMetricEvaluation u v c g (gaugeShiftOneForm A dchi) X
        (gaugeShiftFiber c dchi X xi) =
      kaluzaMetricEvaluation u v c g A X xi := by
  unfold kaluzaMetricEvaluation
  rw [kaluzaFiberOneForm_gauge_invariant]

/-- The full bilinear Kaluza metric is invariant under the paired gauge shift
on both tangent arguments. -/
theorem kaluzaMetricPairing_gauge_invariant
    (u v c : ℝ) (g : ContinuousBilinForm E)
    (A dchi : E →L[ℝ] ℝ) (X Y : E) (xi eta : ℝ) :
    kaluzaMetricPairing u v c g (gaugeShiftOneForm A dchi) X Y
        (gaugeShiftFiber c dchi X xi) (gaugeShiftFiber c dchi Y eta) =
      kaluzaMetricPairing u v c g A X Y xi eta := by
  unfold kaluzaMetricPairing
  rw [kaluzaFiberOneForm_gauge_invariant,
    kaluzaFiberOneForm_gauge_invariant]

/-- Nondegeneracy of the base metric and nonzero warp factors imply
nondegeneracy of the assembled Kaluza block. -/
theorem kaluzaMetricPairing_nondegenerate
    (u v c : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hg : ∀ X, (∀ Y, g X Y = 0) → X = 0)
    (X : E) (xi : ℝ)
    (hzero : ∀ Y eta, kaluzaMetricPairing u v c g A X Y xi eta = 0) :
    X = 0 ∧ xi = 0 := by
  have hfiber : kaluzaFiberOneForm c A X xi = 0 := by
    have h := hzero 0 1
    simp [kaluzaMetricPairing, kaluzaFiberOneForm] at h
    exact h.resolve_left hv
  have hX : X = 0 := by
    apply hg X
    intro Y
    have h := hzero Y 0
    simp [kaluzaMetricPairing, hfiber] at h
    exact h.resolve_left hu
  refine ⟨hX, ?_⟩
  simpa [hX, kaluzaFiberOneForm] using hfiber

/-- Gauge shifts compose additively on the connection. -/
theorem gaugeShiftOneForm_add
    (A dchi₁ dchi₂ : E →L[ℝ] ℝ) :
    gaugeShiftOneForm (gaugeShiftOneForm A dchi₁) dchi₂ =
      gaugeShiftOneForm A (dchi₁ + dchi₂) := by
  simp [gaugeShiftOneForm, add_assoc]

/-- The compensating fiber shifts obey the same additive composition law. -/
theorem gaugeShiftFiber_add
    (c : ℝ) (dchi₁ dchi₂ : E →L[ℝ] ℝ) (X : E) (xi : ℝ) :
    gaugeShiftFiber c dchi₂ X (gaugeShiftFiber c dchi₁ X xi) =
      gaugeShiftFiber c (dchi₁ + dchi₂) X xi := by
  simp [gaugeShiftFiber]
  ring

end KaluzaGaugeInvariance

end RainichKaluza
