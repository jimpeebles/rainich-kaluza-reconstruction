import RainichKaluza.CurvatureBranchObstruction
import RainichKaluza.PhaseIVReadiness
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Integrating the curvature branch classifier

This file connects the explicit coordinate jets of
`CurvatureScalarBranchJet4` to genuine differentiable continuous-linear
one-form fields.  It proves that vanishing of the matrix obstruction is
exactly Mathlib's local closedness predicate, then applies the Poincare lemma
to return the exhaustive zero/one/two scalar-potential classification.

The realization structure records the honest compatibility condition that
the displayed coordinate jets are the Frechet derivatives of the displayed
one-form fields.  No branch is assumed closed.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

/-- Standard four-dimensional coordinate vector space. -/
abbrev CurvatureCoordinateSpace4 := Fin 4 → ℝ

/-- Evaluation of a coordinate one-form on a coordinate vector. -/
def oneForm4Evaluate (v u : OneForm4) : ℝ :=
  ∑ i, v i * u i

/-- A coordinate one-form as an algebraic linear map. -/
def oneForm4LinearMap (v : OneForm4) :
    CurvatureCoordinateSpace4 →ₗ[ℝ] ℝ where
  toFun := oneForm4Evaluate v
  map_add' := by
    intro u w
    simp only [oneForm4Evaluate, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c u
    simp only [oneForm4Evaluate, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Finite dimensionality makes every coordinate one-form continuous. -/
noncomputable def oneForm4ContinuousLinearMap (v : OneForm4) :
    CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (oneForm4LinearMap v)

@[simp]
theorem oneForm4ContinuousLinearMap_apply
    (v u : OneForm4) :
    oneForm4ContinuousLinearMap v u = oneForm4Evaluate v u := by
  rfl

/-- Bilinear evaluation of a coordinate one-form first jet. -/
def oneFormJetEvaluate
    (D : Fin 4 → OneForm4) (u w : CurvatureCoordinateSpace4) : ℝ :=
  ∑ k, ∑ j, u k * D k j * w j

@[simp]
theorem oneFormJetEvaluate_add
    (D E : Fin 4 → OneForm4) (u w : CurvatureCoordinateSpace4) :
    oneFormJetEvaluate (D + E) u w =
      oneFormJetEvaluate D u w + oneFormJetEvaluate E u w := by
  simp only [oneFormJetEvaluate, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

@[simp]
theorem oneFormJetEvaluate_sub
    (D E : Fin 4 → OneForm4) (u w : CurvatureCoordinateSpace4) :
    oneFormJetEvaluate (D - E) u w =
      oneFormJetEvaluate D u w - oneFormJetEvaluate E u w := by
  simp only [oneFormJetEvaluate, Pi.sub_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

/-- Standard coordinate basis vector. -/
def curvatureCoordinateDirection (i : Fin 4) : CurvatureCoordinateSpace4 :=
  fun j => if j = i then 1 else 0

@[simp]
theorem oneFormJetEvaluate_coordinateDirections
    (D : Fin 4 → OneForm4) (k j : Fin 4) :
    oneFormJetEvaluate D (curvatureCoordinateDirection k)
        (curvatureCoordinateDirection j) = D k j := by
  simp [oneFormJetEvaluate, curvatureCoordinateDirection]

/-- A coordinate first jet is symmetric as a bilinear map exactly when its
exterior-derivative matrix vanishes. -/
theorem oneFormJetEvaluate_symmetric_iff
    (D : Fin 4 → OneForm4) :
    (∀ u w, oneFormJetEvaluate D u w = oneFormJetEvaluate D w u) ↔
      oneFormJetExteriorDerivative D = 0 := by
  constructor
  · intro h
    ext k j
    have hkj := h (curvatureCoordinateDirection k)
      (curvatureCoordinateDirection j)
    simp only [oneFormJetEvaluate_coordinateDirections] at hkj
    simp [oneFormJetExteriorDerivative, hkj]
  · intro hzero u w
    have hsymm (k j : Fin 4) : D k j = D j k := by
      have hentry := congrArg (fun M : Matrix4 => M k j) hzero
      simp only [oneFormJetExteriorDerivative, Matrix.zero_apply] at hentry
      linarith
    unfold oneFormJetEvaluate
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hsymm k j]
    ring

/-- A differentiable covector field together with its displayed coordinate
first jet has Mathlib closedness exactly when that jet exteriorizes to zero. -/
theorem isClosedScalarOneFormOn_iff_coordinateJet
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (D : CurvatureCoordinateSpace4 → Fin 4 → OneForm4)
    (U : Set CurvatureCoordinateSpace4)
    (hdiff : DifferentiableOn ℝ v U)
    (hfderiv : ∀ x ∈ U, ∀ u w,
      fderiv ℝ v x u w = oneFormJetEvaluate (D x) u w) :
    IsClosedScalarOneFormOn v U ↔
      ∀ x ∈ U, oneFormJetExteriorDerivative (D x) = 0 := by
  constructor
  · intro hclosed x hx
    apply (oneFormJetEvaluate_symmetric_iff (D x)).mp
    intro u w
    rw [← hfderiv x hx u w, ← hfderiv x hx w u]
    exact hclosed.2 x hx u w
  · intro hzero
    refine ⟨hdiff, ?_⟩
    intro x hx u w
    rw [hfderiv x hx u w, hfderiv x hx w u]
    exact (oneFormJetEvaluate_symmetric_iff (D x)).mpr
      (hzero x hx) u w

/-- On an open patch, a differentiable one-form admitting a genuine scalar
potential is necessarily closed.  This supplies the converse needed to make
the final zero/one/two potential count exact. -/
theorem isClosedScalarOneFormOn_of_scalarPotential
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (U : Set CurvatureCoordinateSpace4)
    (hopen : IsOpen U) (hdiff : DifferentiableOn ℝ v U)
    {phi : CurvatureCoordinateSpace4 → ℝ}
    (hphi : IsScalarPotentialOn phi v U) :
    IsClosedScalarOneFormOn v U := by
  refine ⟨hdiff, ?_⟩
  intro x hx u w
  apply second_derivative_symmetric_of_eventually
    (f := phi) (f' := v)
  · filter_upwards [hopen.mem_nhds hx] with y hy
    exact hphi y hy
  · exact ((hdiff x hx).differentiableAt
      (hopen.mem_nhds hx)).hasFDerivAt

/-- Genuine local field realization of the two curvature spectral
components.  The one-form values are those assembled by the curvature jet;
the last two fields state that its displayed first jets are their actual
Frechet derivatives. -/
structure RealizedCurvatureScalarBranchPatch4
    (U : Set CurvatureCoordinateSpace4) where
  jet : CurvatureCoordinateSpace4 → CurvatureScalarBranchJet4
  alphaDifferentiable : DifferentiableOn ℝ
    (fun x => oneForm4ContinuousLinearMap (jet x).alpha) U
  betaDifferentiable : DifferentiableOn ℝ
    (fun x => oneForm4ContinuousLinearMap (jet x).beta) U
  alphaFDeriv : ∀ x ∈ U, ∀ u w,
    fderiv ℝ (fun y => oneForm4ContinuousLinearMap (jet y).alpha) x u w =
      oneFormJetEvaluate (jet x).alphaJet u w
  betaFDeriv : ∀ x ∈ U, ∀ u w,
    fderiv ℝ (fun y => oneForm4ContinuousLinearMap (jet y).beta) x u w =
      oneFormJetEvaluate (jet x).betaJet u w

namespace RealizedCurvatureScalarBranchPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- Genuine first spectral one-form field. -/
noncomputable def alphaField
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
  fun x => oneForm4ContinuousLinearMap (B.jet x).alpha

/-- Genuine second spectral one-form field. -/
noncomputable def betaField
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
  fun x => oneForm4ContinuousLinearMap (B.jet x).beta

/-- Genuine relative-sign sum branch. -/
noncomputable def plusField
    (B : RealizedCurvatureScalarBranchPatch4 U) :=
  B.alphaField + B.betaField

/-- Genuine relative-sign difference branch. -/
noncomputable def minusField
    (B : RealizedCurvatureScalarBranchPatch4 U) :=
  B.alphaField - B.betaField

theorem alphaField_differentiable
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    DifferentiableOn ℝ B.alphaField U :=
  B.alphaDifferentiable

theorem betaField_differentiable
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    DifferentiableOn ℝ B.betaField U :=
  B.betaDifferentiable

theorem plusField_differentiable
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    DifferentiableOn ℝ B.plusField U :=
  B.alphaField_differentiable.add B.betaField_differentiable

theorem minusField_differentiable
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    DifferentiableOn ℝ B.minusField U :=
  B.alphaField_differentiable.sub B.betaField_differentiable

/-- The displayed sum jet is the actual Frechet derivative of the genuine
sum-branch one-form field. -/
theorem plusField_fderiv
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) (x : CurvatureCoordinateSpace4) (hx : x ∈ U)
    (u w : CurvatureCoordinateSpace4) :
    fderiv ℝ B.plusField x u w =
      oneFormJetEvaluate (B.jet x).vPlusJet u w := by
  have halpha : DifferentiableAt ℝ B.alphaField x :=
    (B.alphaField_differentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have hbeta : DifferentiableAt ℝ B.betaField x :=
    (B.betaField_differentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have halphaDeriv := B.alphaFDeriv x hx u w
  have hbetaDeriv := B.betaFDeriv x hx u w
  change fderiv ℝ B.alphaField x u w = _ at halphaDeriv
  change fderiv ℝ B.betaField x u w = _ at hbetaDeriv
  change fderiv ℝ (B.alphaField + B.betaField) x u w = _
  rw [fderiv_add halpha hbeta]
  simp only [add_apply, halphaDeriv, hbetaDeriv,
    CurvatureScalarBranchJet4.vPlusJet,
    oneFormJetEvaluate_add]

/-- The displayed difference jet is the actual Frechet derivative of the
genuine difference-branch one-form field. -/
theorem minusField_fderiv
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hopen : IsOpen U) (x : CurvatureCoordinateSpace4) (hx : x ∈ U)
    (u w : CurvatureCoordinateSpace4) :
    fderiv ℝ B.minusField x u w =
      oneFormJetEvaluate (B.jet x).vMinusJet u w := by
  have halpha : DifferentiableAt ℝ B.alphaField x :=
    (B.alphaField_differentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have hbeta : DifferentiableAt ℝ B.betaField x :=
    (B.betaField_differentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have halphaDeriv := B.alphaFDeriv x hx u w
  have hbetaDeriv := B.betaFDeriv x hx u w
  change fderiv ℝ B.alphaField x u w = _ at halphaDeriv
  change fderiv ℝ B.betaField x u w = _ at hbetaDeriv
  change fderiv ℝ (B.alphaField - B.betaField) x u w = _
  rw [fderiv_sub halpha hbeta]
  simp only [sub_apply, halphaDeriv, hbetaDeriv,
    CurvatureScalarBranchJet4.vMinusJet,
    oneFormJetEvaluate_sub]

/-- `dalpha=0` is exactly closedness of the genuine first spectral field. -/
theorem alphaField_closed_iff
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    IsClosedScalarOneFormOn B.alphaField U ↔
      ∀ x ∈ U, (B.jet x).dalpha = 0 := by
  exact isClosedScalarOneFormOn_iff_coordinateJet B.alphaField
    (fun x => (B.jet x).alphaJet) U B.alphaField_differentiable
    B.alphaFDeriv

/-- `dbeta=0` is exactly closedness of the genuine second spectral field. -/
theorem betaField_closed_iff
    (B : RealizedCurvatureScalarBranchPatch4 U) :
    IsClosedScalarOneFormOn B.betaField U ↔
      ∀ x ∈ U, (B.jet x).dbeta = 0 := by
  exact isClosedScalarOneFormOn_iff_coordinateJet B.betaField
    (fun x => (B.jet x).betaJet) U B.betaField_differentiable
    B.betaFDeriv

/-- The curvature sum obstruction vanishes on the patch exactly when the
genuine sum-branch one-form is closed there. -/
theorem plusField_closed_iff
    (B : RealizedCurvatureScalarBranchPatch4 U) (hopen : IsOpen U) :
    IsClosedScalarOneFormOn B.plusField U ↔
      CurvaturePlusBranchClosesOn B.jet U := by
  simpa only [CurvaturePlusBranchClosesOn,
    CurvatureScalarBranchJet4.PlusClosed] using
    (isClosedScalarOneFormOn_iff_coordinateJet B.plusField
      (fun x => (B.jet x).vPlusJet) U B.plusField_differentiable
      (B.plusField_fderiv hopen))

/-- The curvature difference obstruction vanishes on the patch exactly when
the genuine difference-branch one-form is closed there. -/
theorem minusField_closed_iff
    (B : RealizedCurvatureScalarBranchPatch4 U) (hopen : IsOpen U) :
    IsClosedScalarOneFormOn B.minusField U ↔
      CurvatureMinusBranchClosesOn B.jet U := by
  simpa only [CurvatureMinusBranchClosesOn,
    CurvatureScalarBranchJet4.MinusClosed] using
    (isClosedScalarOneFormOn_iff_coordinateJet B.minusField
      (fun x => (B.jet x).vMinusJet) U B.minusField_differentiable
      (B.minusField_fderiv hopen))

/-- Existence of a genuine local scalar potential for the sum branch. -/
def PlusScalarPotentialExists
    (B : RealizedCurvatureScalarBranchPatch4 U) : Prop :=
  ∃ phi : CurvatureCoordinateSpace4 → ℝ,
    IsScalarPotentialOn phi B.plusField U

/-- Existence of a genuine local scalar potential for the difference
branch. -/
def MinusScalarPotentialExists
    (B : RealizedCurvatureScalarBranchPatch4 U) : Prop :=
  ∃ phi : CurvatureCoordinateSpace4 → ℝ,
    IsScalarPotentialOn phi B.minusField U

/-- On an open convex patch, the sum candidate has a scalar potential
exactly when its curvature obstruction vanishes throughout the patch. -/
theorem plusScalarPotentialExists_iff_curvatureBranchCloses
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    B.PlusScalarPotentialExists ↔
      CurvaturePlusBranchClosesOn B.jet U := by
  rw [← B.plusField_closed_iff hopen]
  constructor
  · rintro ⟨phi, hphi⟩
    exact isClosedScalarOneFormOn_of_scalarPotential B.plusField U hopen
      B.plusField_differentiable hphi
  · intro hclosed
    exact exists_scalarPotential_of_closed hconvex hopen hclosed

/-- On an open convex patch, the difference candidate has a scalar potential
exactly when its curvature obstruction vanishes throughout the patch. -/
theorem minusScalarPotentialExists_iff_curvatureBranchCloses
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    B.MinusScalarPotentialExists ↔
      CurvatureMinusBranchClosesOn B.jet U := by
  rw [← B.minusField_closed_iff hopen]
  constructor
  · rintro ⟨phi, hphi⟩
    exact isClosedScalarOneFormOn_of_scalarPotential B.minusField U hopen
      B.minusField_differentiable hphi
  · intro hclosed
    exact exists_scalarPotential_of_closed hconvex hopen hclosed

/-- **Exact local scalar-branch integration theorem.** Every realized
curvature patch has exactly one of four outcomes: only the sum potential,
only the difference potential, both potentials, or no potential.  No
universal branch-existence assumption is used. -/
theorem exhaustive_local_scalarPotential_classification
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    (B.PlusScalarPotentialExists ∧
        ¬B.MinusScalarPotentialExists) ∨
      (¬B.PlusScalarPotentialExists ∧
        B.MinusScalarPotentialExists) ∨
      (B.PlusScalarPotentialExists ∧
        B.MinusScalarPotentialExists) ∨
      (¬B.PlusScalarPotentialExists ∧
        ¬B.MinusScalarPotentialExists) := by
  have hplus := B.plusScalarPotentialExists_iff_curvatureBranchCloses
    hconvex hopen
  have hminus := B.minusScalarPotentialExists_iff_curvatureBranchCloses
    hconvex hopen
  rcases exhaustive_patch_closure_classification B.jet U with
    h | h | h | h
  · exact Or.inl ⟨hplus.mpr h.1, fun hm => h.2 (hminus.mp hm)⟩
  · exact Or.inr <| Or.inl
      ⟨fun hp => h.1 (hplus.mp hp), hminus.mpr h.2⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨hplus.mpr h.1, hminus.mpr h.2⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨fun hp => h.1 (hplus.mp hp), fun hm => h.2 (hminus.mp hm)⟩

/-- **Sharp realized no-branch certificate.** Two finite curvature witnesses,
possibly at different points, rule out scalar potentials for both genuine
relative-sign fields on the entire patch. -/
theorem no_local_scalarPotentialBranch_of_witnesses
    (B : RealizedCurvatureScalarBranchPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    {zPlus zMinus : CurvatureCoordinateSpace4}
    (hzPlus : zPlus ∈ U) (hzMinus : zMinus ∈ U)
    (hplus : (B.jet zPlus).dalpha + (B.jet zPlus).dbeta ≠ 0)
    (hminus : (B.jet zMinus).dalpha - (B.jet zMinus).dbeta ≠ 0) :
    ¬B.PlusScalarPotentialExists ∧
      ¬B.MinusScalarPotentialExists := by
  have hnone := neither_curvatureBranch_closesOn_of_witnesses B.jet U
    hzPlus hzMinus hplus hminus
  exact
    ⟨fun hp => hnone.1
        ((B.plusScalarPotentialExists_iff_curvatureBranchCloses
          hconvex hopen).mp hp),
      fun hm => hnone.2
        ((B.minusScalarPotentialExists_iff_curvatureBranchCloses
          hconvex hopen).mp hm)⟩

end RealizedCurvatureScalarBranchPatch4

end RainichKaluza
