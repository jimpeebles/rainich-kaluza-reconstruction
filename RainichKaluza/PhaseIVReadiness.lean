import RainichKaluza.LocalExteriorSeed
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module

/-!
# Generic local handoff to the five-dimensional uplift phase

This file closes the local analytic interface between the reconstructed
four-dimensional fields and Phase IV.

First, Mathlib's Poincare lemma for one-forms on convex sets is specialized to
the reconstructed scalar covector.  A differentiable closed scalar one-form
therefore has a local potential, unique up to an additive constant.

Second, the rescaled EMD equations are unweighted by an abstract product rule.
If `calF = exp(a phi / 2) F`, its first closure equation makes the physical
Maxwell two-form `F` closed.  The second equation similarly makes the weighted
dual flux closed.  A final theorem feeds the explicit Phase-III obstruction
pair into these two conclusions.

The remaining new Phase-IV operation is the Poincare lemma for the resulting
closed two-form, producing a local gauge potential `A`, followed by assembly
and Ricci-flatness of the five-dimensional Kaluza metric.
-/

namespace RainichKaluza

open Set

section ScalarPotential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differentiable scalar one-form is closed on `U` when its Frechet
derivative is symmetric there.  This is the coordinate expression of
`dv=0`. -/
def IsClosedScalarOneFormOn
    (v : E → E →L[ℝ] ℝ) (U : Set E) : Prop :=
  DifferentiableOn ℝ v U ∧
    ∀ x ∈ U, ∀ u w, fderiv ℝ v x u w = fderiv ℝ v x w u

/-- A function is a scalar potential for `v` on `U` when its Frechet
derivative is exactly `v` at every point of the patch. -/
def IsScalarPotentialOn
    (phi : E → ℝ) (v : E → E →L[ℝ] ℝ) (U : Set E) : Prop :=
  ∀ x ∈ U, HasFDerivAt phi (v x) x

/-- **Local scalar integrability.** On an open convex coordinate patch, every
differentiable closed scalar covector is the differential of a scalar
potential. -/
theorem exists_scalarPotential_of_closed
    {v : E → E →L[ℝ] ℝ} {U : Set E}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hclosed : IsClosedScalarOneFormOn v U) :
    ∃ phi : E → ℝ, IsScalarPotentialOn phi v U := by
  exact hconvex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    hopen hclosed.1 hclosed.2

/-- Any two scalar potentials for the same reconstructed covector differ by
an additive constant on the convex patch. -/
theorem scalarPotential_unique_up_to_constant
    {phi psi : E → ℝ} {v : E → E →L[ℝ] ℝ} {U : Set E}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hphi : IsScalarPotentialOn phi v U)
    (hpsi : IsScalarPotentialOn psi v U) :
    ∃ c : ℝ, U.EqOn phi (fun x => psi x + c) := by
  apply hopen.exists_eq_add_of_fderiv_eq (𝕜 := ℝ) hconvex.isPreconnected
  · exact fun x hx => (hphi x hx).differentiableAt.differentiableWithinAt
  · exact fun x hx => (hpsi x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hphi x hx).fderiv, (hpsi x hx).fderiv]

/-- For differentiable scalar one-form fields, the two relative-sign branches
are simultaneously closed exactly when their two spectral components are
separately closed.  This is the analytic local realization of
`both_relativeSign_branches_closed_iff`. -/
theorem both_relativeSign_scalarOneForms_closed_iff
    {alpha beta : E → E →L[ℝ] ℝ} {U : Set E}
    (hopen : IsOpen U)
    (halphaDiff : DifferentiableOn ℝ alpha U)
    (hbetaDiff : DifferentiableOn ℝ beta U) :
    (IsClosedScalarOneFormOn (alpha + beta) U ∧
        IsClosedScalarOneFormOn (alpha - beta) U) ↔
      (IsClosedScalarOneFormOn alpha U ∧
        IsClosedScalarOneFormOn beta U) := by
  have hdiffAt (x : E) (hx : x ∈ U) :
      DifferentiableAt ℝ alpha x ∧ DifferentiableAt ℝ beta x :=
    ⟨(halphaDiff x hx).differentiableAt (hopen.mem_nhds hx),
      (hbetaDiff x hx).differentiableAt (hopen.mem_nhds hx)⟩
  constructor
  · rintro ⟨hplus, hminus⟩
    refine ⟨⟨halphaDiff, ?_⟩, ⟨hbetaDiff, ?_⟩⟩
    · intro x hx u w
      have hp := hplus.2 x hx u w
      have hm := hminus.2 x hx u w
      rw [fderiv_add (hdiffAt x hx).1 (hdiffAt x hx).2] at hp
      rw [fderiv_sub (hdiffAt x hx).1 (hdiffAt x hx).2] at hm
      simp only [add_apply, sub_apply] at hp hm
      linarith
    · intro x hx u w
      have hp := hplus.2 x hx u w
      have hm := hminus.2 x hx u w
      rw [fderiv_add (hdiffAt x hx).1 (hdiffAt x hx).2] at hp
      rw [fderiv_sub (hdiffAt x hx).1 (hdiffAt x hx).2] at hm
      simp only [add_apply, sub_apply] at hp hm
      linarith
  · rintro ⟨halpha, hbeta⟩
    constructor
    · refine ⟨halphaDiff.add hbetaDiff, ?_⟩
      intro x hx u w
      rw [fderiv_add (hdiffAt x hx).1 (hdiffAt x hx).2]
      simp only [add_apply]
      rw [halpha.2 x hx u w, hbeta.2 x hx u w]
    · refine ⟨halphaDiff.sub hbetaDiff, ?_⟩
      intro x hx u w
      rw [fderiv_sub (hdiffAt x hx).1 (hdiffAt x hx).2]
      simp only [sub_apply]
      rw [halpha.2 x hx u w, hbeta.2 x hx u w]

/-- **Generic scalar-branch integration theorem.** If at least one
relative-sign branch is closed but the two spectral components are not
separately closed, exactly one branch is closed, and that branch has a local
scalar potential on the open convex patch. -/
theorem relativeSign_scalarPotential_exists_unique_branch
    {alpha beta : E → E →L[ℝ] ℝ} {U : Set E}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (halphaDiff : DifferentiableOn ℝ alpha U)
    (hbetaDiff : DifferentiableOn ℝ beta U)
    (hexists :
      IsClosedScalarOneFormOn (alpha + beta) U ∨
        IsClosedScalarOneFormOn (alpha - beta) U)
    (hgeneric :
      ¬(IsClosedScalarOneFormOn alpha U ∧
        IsClosedScalarOneFormOn beta U)) :
    (IsClosedScalarOneFormOn (alpha + beta) U ∧
        ¬IsClosedScalarOneFormOn (alpha - beta) U ∧
        ∃ phi, IsScalarPotentialOn phi (alpha + beta) U) ∨
      (¬IsClosedScalarOneFormOn (alpha + beta) U ∧
        IsClosedScalarOneFormOn (alpha - beta) U ∧
        ∃ phi, IsScalarPotentialOn phi (alpha - beta) U) := by
  rcases hexists with hplus | hminus
  · left
    refine ⟨hplus, ?_, exists_scalarPotential_of_closed hconvex hopen hplus⟩
    intro hminus
    exact hgeneric <|
      (both_relativeSign_scalarOneForms_closed_iff hopen halphaDiff
        hbetaDiff).mp ⟨hplus, hminus⟩
  · right
    refine ⟨?_, hminus, exists_scalarPotential_of_closed hconvex hopen hminus⟩
    intro hplus
    exact hgeneric <|
      (both_relativeSign_scalarOneForms_closed_iff hopen halphaDiff
        hbetaDiff).mp ⟨hplus, hminus⟩

/-- Reversing the scalar orientation sends a potential `phi` to `-phi`. -/
theorem neg_isScalarPotentialOn
    {phi : E → ℝ} {v : E → E →L[ℝ] ℝ} {U : Set E}
    (hphi : IsScalarPotentialOn phi v U) :
    IsScalarPotentialOn (-phi) (fun x => -(v x)) U := by
  intro x hx
  simpa only [Pi.neg_apply] using (hphi x hx).neg

/-- Negative EMD weight used to recover the physical Maxwell field from the
rescaled field. -/
noncomputable def negativeEMDWeight
    (a : ℝ) (phi : E → ℝ) (x : E) : ℝ :=
  Real.exp (-(a / 2) * phi x)

/-- Positive EMD weight used for the closed dual flux. -/
noncomputable def positiveEMDWeight
    (a : ℝ) (phi : E → ℝ) (x : E) : ℝ :=
  Real.exp ((a / 2) * phi x)

/-- The negative exponential weight has derivative
`-(a/2) exp(-a phi/2) dphi`. -/
theorem hasFDerivAt_negativeEMDWeight
    {phi : E → ℝ} {v : E →L[ℝ] ℝ} {x : E} (a : ℝ)
    (hphi : HasFDerivAt phi v x) :
    HasFDerivAt (negativeEMDWeight a phi)
      (-(((a / 2) * negativeEMDWeight a phi x) • v)) x := by
  have h := (hphi.const_smul (-(a / 2))).exp
  change HasFDerivAt (fun y => Real.exp (-(a / 2) * phi y))
    (-(((a / 2) * Real.exp (-(a / 2) * phi x)) • v)) x
  simpa [Pi.smul_apply, smul_eq_mul, smul_smul, neg_smul,
    mul_comm] using h

/-- The positive exponential weight has derivative
`(a/2) exp(a phi/2) dphi`. -/
theorem hasFDerivAt_positiveEMDWeight
    {phi : E → ℝ} {v : E →L[ℝ] ℝ} {x : E} (a : ℝ)
    (hphi : HasFDerivAt phi v x) :
    HasFDerivAt (positiveEMDWeight a phi)
      (((a / 2) * positiveEMDWeight a phi x) • v) x := by
  have h := (hphi.const_smul (a / 2)).exp
  change HasFDerivAt (fun y => Real.exp ((a / 2) * phi y))
    (((a / 2) * Real.exp ((a / 2) * phi x)) • v) x
  simpa [Pi.smul_apply, smul_eq_mul, smul_smul,
    mul_comm] using h

end ScalarPotential

section KaluzaCoupling

/-- Orientation-independent test for the Kaluza value of the EMD coupling. -/
def IsKaluzaCoupling (a : ℝ) : Prop :=
  a ^ 2 = 3

/-- Reversing scalar orientation preserves the Kaluza coupling test. -/
theorem isKaluzaCoupling_neg_iff (a : ℝ) :
    IsKaluzaCoupling (-a) ↔ IsKaluzaCoupling a := by
  unfold IsKaluzaCoupling
  ring_nf

/-- If the orientation-independent coupling test returns `a²=3`, one of the
two scalar orientations has the convention-fixed positive coupling `sqrt 3`. -/
theorem kaluzaCoupling_has_positive_orientation
    (a : ℝ) (ha : IsKaluzaCoupling a) :
    a = Real.sqrt 3 ∨ -a = Real.sqrt 3 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : a ^ 2 = (Real.sqrt 3) ^ 2 := by
    rw [ha, hsqrt]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

end KaluzaCoupling

section MaxwellUnrescaling

variable {One Two Three : Type*}
  [AddCommGroup One] [Module ℝ One]
  [AddCommGroup Two] [Module ℝ Two]
  [AddCommGroup Three] [Module ℝ Three]

/-- First derivative of the negative EMD weight, expressed using only its
value and the scalar covector. -/
noncomputable def negativeEMDWeightDerivative
    (a r : ℝ) (v : One) : One :=
  (-(a / 2) * r) • v

/-- First derivative of the positive EMD weight. -/
noncomputable def positiveEMDWeightDerivative
    (a r : ℝ) (v : One) : One :=
  ((a / 2) * r) • v

/-- Product-rule exterior derivative of a scalar multiple `r F`, supplied
with the evaluated derivative one-form `dr`. -/
def scaledTwoFormExteriorDerivative
    (wedge : OneWedgeTwo One Two Three)
    (r : ℝ) (dr : One) (F : Two) (dF : Three) : Three :=
  wedge dr F + r • dF

/-- The rescaled Bianchi equation makes the unweighted physical Maxwell
two-form closed when `dr=-(a/2)r v`. -/
theorem closed_unscaledMaxwell_of_rescaled_bianchi
    (wedge : OneWedgeTwo One Two Three)
    (v dr : One) (F : Two) (dF : Three) (a r : ℝ)
    (hdr : dr = (-(a / 2) * r) • v)
    (hF : dF = (a / 2) • wedge v F) :
    scaledTwoFormExteriorDerivative wedge r dr F dF = 0 := by
  unfold scaledTwoFormExteriorDerivative
  rw [hdr, hF]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, ← add_smul]
  rw [show -(a / 2) * r + r * (a / 2) = 0 by ring, zero_smul]

/-- The rescaled Maxwell equation makes the oppositely weighted Hodge flux
closed when `dr=(a/2)r v`. -/
theorem closed_weightedHodgeFlux_of_rescaled_maxwell
    (wedge : OneWedgeTwo One Two Three)
    (v dr : One) (G : Two) (dG : Three) (a r : ℝ)
    (hdr : dr = ((a / 2) * r) • v)
    (hG : dG = -(a / 2) • wedge v G) :
    scaledTwoFormExteriorDerivative wedge r dr G dG = 0 := by
  unfold scaledTwoFormExteriorDerivative
  rw [hdr, hG]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, ← add_smul]
  rw [show a / 2 * r + r * -(a / 2) = 0 by ring, zero_smul]

/-- Both rescaled EMD equations give the closed physical Maxwell field and
closed weighted dual flux required at the start of the uplift construction. -/
theorem emdExteriorClosure_gives_closed_weighted_pair
    (wedge : OneWedgeTwo One Two Three)
    (v drMinus drPlus : One) (F G : Two) (dF dG : Three)
    (a rMinus rPlus : ℝ)
    (hclosure : EMDExteriorClosure wedge v a F G dF dG)
    (hdrMinus : drMinus = (-(a / 2) * rMinus) • v)
    (hdrPlus : drPlus = ((a / 2) * rPlus) • v) :
    scaledTwoFormExteriorDerivative wedge rMinus drMinus F dF = 0 ∧
      scaledTwoFormExteriorDerivative wedge rPlus drPlus G dG = 0 := by
  exact ⟨closed_unscaledMaxwell_of_rescaled_bianchi wedge v drMinus F dF
      a rMinus hdrMinus hclosure.1,
    closed_weightedHodgeFlux_of_rescaled_maxwell wedge v drPlus G dG
      a rPlus hdrPlus hclosure.2⟩

/-- Version with the two exponential-weight derivatives inserted
canonically. -/
theorem emdExteriorClosure_gives_closed_exponentialWeightJets
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F G : Two) (dF dG : Three)
    (a rMinus rPlus : ℝ)
    (hclosure : EMDExteriorClosure wedge v a F G dF dG) :
    scaledTwoFormExteriorDerivative wedge rMinus
        (negativeEMDWeightDerivative a rMinus v) F dF = 0 ∧
      scaledTwoFormExteriorDerivative wedge rPlus
        (positiveEMDWeightDerivative a rPlus v) G dG = 0 := by
  exact emdExteriorClosure_gives_closed_weighted_pair wedge v
    (negativeEMDWeightDerivative a rMinus v)
    (positiveEMDWeightDerivative a rPlus v)
    F G dF dG a rMinus rPlus hclosure rfl rfl

end MaxwellUnrescaling

/-- **Phase-III to Phase-IV handoff.** Vanishing of the two explicit local
curvature-seed obstructions implies closure of the unscaled physical Maxwell
two-form and of the oppositely weighted Hodge flux. -/
theorem localPositiveQ_obstructions_give_closed_weighted_pair
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq omega v drMinus drPlus : OneForm4)
    (c s a rMinus rPlus : ℝ) (dc ds : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hobs :
      let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
      localSeedEMDObstructionF J omega v a = 0 ∧
        localSeedEMDObstructionG J omega v a = 0)
    (hdrMinus : drMinus = (-(a / 2) * rMinus) • v)
    (hdrPlus : drPlus = ((a / 2) * rPlus) • v) :
    let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
    scaledTwoFormExteriorDerivative matrixOneWedgeTwo
        rMinus drMinus J.rotatedF (J.rotatedDF matrixOneWedgeTwo) = 0 ∧
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo
        rPlus drPlus J.rotatedG (J.rotatedDG matrixOneWedgeTwo) = 0 := by
  let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
  have hclosure :
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo) :=
    (localPositiveQ_emdClosure_iff_obstructions_zero L dL q dq omega v
      c s a dc ds hdc hds).mpr hobs
  exact emdExteriorClosure_gives_closed_weighted_pair matrixOneWedgeTwo
    v drMinus drPlus J.rotatedF J.rotatedG
    (J.rotatedDF matrixOneWedgeTwo) (J.rotatedDG matrixOneWedgeTwo)
    a rMinus rPlus hclosure hdrMinus hdrPlus

/-- Stronger handoff with the exponential-weight derivative jets inserted by
definition.  Once a scalar potential is supplied by
`exists_scalarPotential_of_closed`, the two weight-derivative theorems above
identify these jets with the derivatives of `exp(∓a phi/2)`. -/
theorem localPositiveQ_obstructions_give_closed_exponentialWeightJets
    (L : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq omega v : OneForm4)
    (c s a rMinus rPlus : ℝ) (dc ds : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hobs :
      let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
      localSeedEMDObstructionF J omega v a = 0 ∧
        localSeedEMDObstructionG J omega v a = 0) :
    let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
    scaledTwoFormExteriorDerivative matrixOneWedgeTwo rMinus
        (negativeEMDWeightDerivative a rMinus v)
        J.rotatedF (J.rotatedDF matrixOneWedgeTwo) = 0 ∧
      scaledTwoFormExteriorDerivative matrixOneWedgeTwo rPlus
        (positiveEMDWeightDerivative a rPlus v)
        J.rotatedG (J.rotatedDG matrixOneWedgeTwo) = 0 := by
  let J := localPositiveQExteriorDualityJet L dL q dq c s dc ds
  have hclosure :
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo) :=
    (localPositiveQ_emdClosure_iff_obstructions_zero L dL q dq omega v
      c s a dc ds hdc hds).mpr hobs
  exact emdExteriorClosure_gives_closed_exponentialWeightJets
    matrixOneWedgeTwo v J.rotatedF J.rotatedG
    (J.rotatedDF matrixOneWedgeTwo) (J.rotatedDG matrixOneWedgeTwo)
    a rMinus rPlus hclosure

end RainichKaluza
