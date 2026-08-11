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

@[simp]
theorem oneForm4ContinuousLinearMap_smul
    (c : ℝ) (v : OneForm4) :
    oneForm4ContinuousLinearMap (c • v) =
      c • oneForm4ContinuousLinearMap v := by
  ext u
  change oneForm4Evaluate (c • v) u = c * oneForm4Evaluate v u
  simp only [oneForm4Evaluate, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

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

/-- The evaluated coordinate jet of a scalar times a one-form is the exact
Frechet product rule: amplitude derivative times the one-form plus amplitude
times the one-form derivative. -/
theorem oneFormJetEvaluate_spectralComponentOneFormJet
    (x : ℝ) (dx theta : OneForm4) (dtheta : Fin 4 → OneForm4)
    (u w : CurvatureCoordinateSpace4) :
    oneFormJetEvaluate
        (spectralComponentOneFormJet x dx theta dtheta) u w =
      x * oneFormJetEvaluate dtheta u w +
        oneForm4Evaluate dx u * oneForm4Evaluate theta w := by
  simp only [oneFormJetEvaluate, spectralComponentOneFormJet,
    oneForm4Evaluate, mul_add, add_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Standard coordinate basis vector. -/
def curvatureCoordinateDirection (i : Fin 4) : CurvatureCoordinateSpace4 :=
  fun j => if j = i then 1 else 0

/-- Every coordinate vector is the finite linear combination of the standard
coordinate directions with its displayed components. -/
theorem curvatureCoordinateDirection_expansion
    (u : CurvatureCoordinateSpace4) :
    (∑ i, u i • curvatureCoordinateDirection i) = u := by
  funext j
  simp [curvatureCoordinateDirection]

/-- Actual coordinate components of the Frechet derivative of a scalar
field. -/
noncomputable def scalarFieldCoordinateFDeriv
    (f : CurvatureCoordinateSpace4 → ℝ)
    (x : CurvatureCoordinateSpace4) : OneForm4 :=
  fun k => fderiv ℝ f x (curvatureCoordinateDirection k)

/-- Actual coordinate components of the Frechet derivative of a one-form
field. -/
noncomputable def oneFormFieldCoordinateFDeriv
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (x : CurvatureCoordinateSpace4) : Fin 4 → OneForm4 :=
  fun k j => fderiv ℝ v x (curvatureCoordinateDirection k)
    (curvatureCoordinateDirection j)

/-- A scalar Frechet derivative is recovered from its four coordinate
components. -/
theorem scalarField_fderiv_eq_coordinateEvaluation
    (f : CurvatureCoordinateSpace4 → ℝ)
    (x u : CurvatureCoordinateSpace4) :
    fderiv ℝ f x u =
      oneForm4Evaluate (scalarFieldCoordinateFDeriv f x) u := by
  conv_lhs => rw [← curvatureCoordinateDirection_expansion u]
  simp [scalarFieldCoordinateFDeriv, oneForm4Evaluate, mul_comm]

/-- A one-form-field Frechet derivative is recovered from its `4×4`
coordinate component jet. -/
theorem oneFormField_fderiv_eq_coordinateEvaluation
    (v : CurvatureCoordinateSpace4 →
      CurvatureCoordinateSpace4 →L[ℝ] ℝ)
    (x u w : CurvatureCoordinateSpace4) :
    fderiv ℝ v x u w =
      oneFormJetEvaluate (oneFormFieldCoordinateFDeriv v x) u w := by
  conv_lhs =>
    rw [← curvatureCoordinateDirection_expansion u]
    rw [← curvatureCoordinateDirection_expansion w]
  simp [oneFormFieldCoordinateFDeriv, oneFormJetEvaluate]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

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

namespace CurvatureScalarBranchJet4

/-- Curvature-reconstructed first derivative of the first scalar amplitude. -/
noncomputable def alphaAmplitudeJet
    (J : CurvatureScalarBranchJet4) : OneForm4 :=
  reconstructedAmplitudeAOneForm J.epsilonA J.x J.a J.b J.qSq
    J.da J.db J.dqSq

/-- Curvature-reconstructed first derivative of the second scalar amplitude. -/
noncomputable def betaAmplitudeJet
    (J : CurvatureScalarBranchJet4) : OneForm4 :=
  reconstructedAmplitudeBOneForm J.epsilonB J.y J.a J.b J.qSq
    J.da J.db J.dqSq

theorem alphaJet_eq_spectralComponent
    (J : CurvatureScalarBranchJet4) :
    J.alphaJet = spectralComponentOneFormJet J.x
      J.alphaAmplitudeJet J.thetaA J.dthetaA := by
  rfl

theorem betaJet_eq_spectralComponent
    (J : CurvatureScalarBranchJet4) :
    J.betaJet = spectralComponentOneFormJet J.y
      J.betaAmplitudeJet J.thetaB J.dthetaB := by
  rfl

/-- The differentiated first scalar-diagonal identity identifies the actual
coordinate derivative of the first amplitude with its curvature formula. -/
theorem alphaAmplitudeCoordinateFDeriv_eq_reconstructed
    (J : CurvatureCoordinateSpace4 → CurvatureScalarBranchJet4)
    (x : CurvatureCoordinateSpace4)
    (hepsilon : (J x).epsilonA ^ 2 = 1) (hx : (J x).x ≠ 0)
    (hdiff : ∀ k,
      (J x).epsilonA * (J x).x *
          scalarFieldCoordinateFDeriv (fun y => (J y).x) x k =
        reconstructedDiagonalADerivative (J x).a (J x).b (J x).qSq
          ((J x).da k) ((J x).db k) ((J x).dqSq k)) :
    scalarFieldCoordinateFDeriv (fun y => (J y).x) x =
      (J x).alphaAmplitudeJet := by
  exact amplitudeAOneForm_eq_reconstructed
    (J x).epsilonA (J x).x (J x).a (J x).b (J x).qSq
    (scalarFieldCoordinateFDeriv (fun y => (J y).x) x)
    (J x).da (J x).db (J x).dqSq hepsilon hx hdiff

/-- The differentiated second scalar-diagonal identity identifies the actual
coordinate derivative of the second amplitude with its curvature formula. -/
theorem betaAmplitudeCoordinateFDeriv_eq_reconstructed
    (J : CurvatureCoordinateSpace4 → CurvatureScalarBranchJet4)
    (x : CurvatureCoordinateSpace4)
    (hepsilon : (J x).epsilonB ^ 2 = 1) (hy : (J x).y ≠ 0)
    (hdiff : ∀ k,
      (J x).epsilonB * (J x).y *
          scalarFieldCoordinateFDeriv (fun z => (J z).y) x k =
        reconstructedDiagonalBDerivative (J x).a (J x).b (J x).qSq
          ((J x).da k) ((J x).db k) ((J x).dqSq k)) :
    scalarFieldCoordinateFDeriv (fun z => (J z).y) x =
      (J x).betaAmplitudeJet := by
  exact amplitudeBOneForm_eq_reconstructed
    (J x).epsilonB (J x).y (J x).a (J x).b (J x).qSq
    (scalarFieldCoordinateFDeriv (fun z => (J z).y) x)
    (J x).da (J x).db (J x).dqSq hepsilon hy hdiff

end CurvatureScalarBranchJet4

/-- Constituent-field realization of a curvature branch jet.  Unlike the
derived branch certificate below, this structure asks only for the actual
amplitude and eigen-one-form derivatives already computed in the smooth
projector construction.  The scalar-times-one-form product rule is not an
assumption. -/
structure CurvatureScalarBranchComponentPatch4
    (U : Set CurvatureCoordinateSpace4) where
  jet : CurvatureCoordinateSpace4 → CurvatureScalarBranchJet4
  alphaAmplitudeDifferentiable : DifferentiableOn ℝ (fun x => (jet x).x) U
  betaAmplitudeDifferentiable : DifferentiableOn ℝ (fun x => (jet x).y) U
  thetaADifferentiable : DifferentiableOn ℝ
    (fun x => oneForm4ContinuousLinearMap (jet x).thetaA) U
  thetaBDifferentiable : DifferentiableOn ℝ
    (fun x => oneForm4ContinuousLinearMap (jet x).thetaB) U
  alphaAmplitudeFDeriv : ∀ x ∈ U, ∀ u,
    fderiv ℝ (fun y => (jet y).x) x u =
      oneForm4Evaluate (jet x).alphaAmplitudeJet u
  betaAmplitudeFDeriv : ∀ x ∈ U, ∀ u,
    fderiv ℝ (fun y => (jet y).y) x u =
      oneForm4Evaluate (jet x).betaAmplitudeJet u
  thetaAFDeriv : ∀ x ∈ U, ∀ u w,
    fderiv ℝ
        (fun y => oneForm4ContinuousLinearMap (jet y).thetaA) x u w =
      oneFormJetEvaluate (jet x).dthetaA u w
  thetaBFDeriv : ∀ x ∈ U, ∀ u w,
    fderiv ℝ
        (fun y => oneForm4ContinuousLinearMap (jet y).thetaB) x u w =
      oneFormJetEvaluate (jet x).dthetaB u w

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

namespace CurvatureScalarBranchComponentPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- Build constituent curvature fields from equality of the displayed jets
with the coordinate components of the actual Frechet derivatives.  Arbitrary
directional derivative formulas then follow automatically by linearity. -/
noncomputable def ofCoordinateFDerivs
    (J : CurvatureCoordinateSpace4 → CurvatureScalarBranchJet4)
    (halphaAmplitude : DifferentiableOn ℝ (fun x => (J x).x) U)
    (hbetaAmplitude : DifferentiableOn ℝ (fun x => (J x).y) U)
    (hthetaA : DifferentiableOn ℝ
      (fun x => oneForm4ContinuousLinearMap (J x).thetaA) U)
    (hthetaB : DifferentiableOn ℝ
      (fun x => oneForm4ContinuousLinearMap (J x).thetaB) U)
    (halphaAmplitudeJet : ∀ x ∈ U,
      scalarFieldCoordinateFDeriv (fun y => (J y).x) x =
        (J x).alphaAmplitudeJet)
    (hbetaAmplitudeJet : ∀ x ∈ U,
      scalarFieldCoordinateFDeriv (fun y => (J y).y) x =
        (J x).betaAmplitudeJet)
    (hthetaAJet : ∀ x ∈ U,
      oneFormFieldCoordinateFDeriv
          (fun y => oneForm4ContinuousLinearMap (J y).thetaA) x =
        (J x).dthetaA)
    (hthetaBJet : ∀ x ∈ U,
      oneFormFieldCoordinateFDeriv
          (fun y => oneForm4ContinuousLinearMap (J y).thetaB) x =
        (J x).dthetaB) :
    CurvatureScalarBranchComponentPatch4 U where
  jet := J
  alphaAmplitudeDifferentiable := halphaAmplitude
  betaAmplitudeDifferentiable := hbetaAmplitude
  thetaADifferentiable := hthetaA
  thetaBDifferentiable := hthetaB
  alphaAmplitudeFDeriv := by
    intro x hx u
    rw [scalarField_fderiv_eq_coordinateEvaluation,
      halphaAmplitudeJet x hx]
  betaAmplitudeFDeriv := by
    intro x hx u
    rw [scalarField_fderiv_eq_coordinateEvaluation,
      hbetaAmplitudeJet x hx]
  thetaAFDeriv := by
    intro x hx u w
    rw [oneFormField_fderiv_eq_coordinateEvaluation,
      hthetaAJet x hx]
  thetaBFDeriv := by
    intro x hx u w
    rw [oneFormField_fderiv_eq_coordinateEvaluation,
      hthetaBJet x hx]

/-- The actual first spectral component is differentiable by the constituent
amplitude/eigen-one-form product rule. -/
theorem alphaDifferentiable
    (C : CurvatureScalarBranchComponentPatch4 U) :
    DifferentiableOn ℝ
      (fun x => oneForm4ContinuousLinearMap (C.jet x).alpha) U := by
  simp only [CurvatureScalarBranchJet4.alpha,
    oneForm4ContinuousLinearMap_smul]
  intro x hx
  have h := (C.alphaAmplitudeDifferentiable x hx).smul
    (C.thetaADifferentiable x hx)
  change DifferentiableWithinAt ℝ
    (fun y => (C.jet y).x •
      oneForm4ContinuousLinearMap (C.jet y).thetaA) U x at h
  exact h

/-- The actual second spectral component is differentiable by the constituent
amplitude/eigen-one-form product rule. -/
theorem betaDifferentiable
    (C : CurvatureScalarBranchComponentPatch4 U) :
    DifferentiableOn ℝ
      (fun x => oneForm4ContinuousLinearMap (C.jet x).beta) U := by
  simp only [CurvatureScalarBranchJet4.beta,
    oneForm4ContinuousLinearMap_smul]
  intro x hx
  have h := (C.betaAmplitudeDifferentiable x hx).smul
    (C.thetaBDifferentiable x hx)
  change DifferentiableWithinAt ℝ
    (fun y => (C.jet y).y •
      oneForm4ContinuousLinearMap (C.jet y).thetaB) U x at h
  exact h

/-- The curvature formula for the first spectral-component jet is its actual
Frechet derivative; this is derived, not assumed, from the two constituent
derivatives. -/
theorem alphaFDeriv
    (C : CurvatureScalarBranchComponentPatch4 U) (hopen : IsOpen U)
    (x : CurvatureCoordinateSpace4) (hx : x ∈ U)
    (u w : CurvatureCoordinateSpace4) :
    fderiv ℝ
        (fun y => oneForm4ContinuousLinearMap (C.jet y).alpha) x u w =
      oneFormJetEvaluate (C.jet x).alphaJet u w := by
  have hxDiff : DifferentiableAt ℝ (fun y => (C.jet y).x) x :=
    (C.alphaAmplitudeDifferentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have hthetaDiff : DifferentiableAt ℝ
      (fun y => oneForm4ContinuousLinearMap (C.jet y).thetaA) x :=
    (C.thetaADifferentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have hfield :
      (fun y => oneForm4ContinuousLinearMap (C.jet y).alpha) =
        (fun y => (C.jet y).x •
          oneForm4ContinuousLinearMap (C.jet y).thetaA) := by
    funext y
    simp only [CurvatureScalarBranchJet4.alpha,
      oneForm4ContinuousLinearMap_smul]
  rw [hfield, fderiv_fun_smul hxDiff hthetaDiff]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [C.thetaAFDeriv x hx u w, C.alphaAmplitudeFDeriv x hx u,
    oneForm4ContinuousLinearMap_apply,
    (C.jet x).alphaJet_eq_spectralComponent,
    oneFormJetEvaluate_spectralComponentOneFormJet]
  simp only [smul_eq_mul]

/-- The curvature formula for the second spectral-component jet is its actual
Frechet derivative; this is derived, not assumed, from the two constituent
derivatives. -/
theorem betaFDeriv
    (C : CurvatureScalarBranchComponentPatch4 U) (hopen : IsOpen U)
    (x : CurvatureCoordinateSpace4) (hx : x ∈ U)
    (u w : CurvatureCoordinateSpace4) :
    fderiv ℝ
        (fun y => oneForm4ContinuousLinearMap (C.jet y).beta) x u w =
      oneFormJetEvaluate (C.jet x).betaJet u w := by
  have hyDiff : DifferentiableAt ℝ (fun y => (C.jet y).y) x :=
    (C.betaAmplitudeDifferentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have hthetaDiff : DifferentiableAt ℝ
      (fun y => oneForm4ContinuousLinearMap (C.jet y).thetaB) x :=
    (C.thetaBDifferentiable x hx).differentiableAt
      (hopen.mem_nhds hx)
  have hfield :
      (fun y => oneForm4ContinuousLinearMap (C.jet y).beta) =
        (fun y => (C.jet y).y •
          oneForm4ContinuousLinearMap (C.jet y).thetaB) := by
    funext y
    simp only [CurvatureScalarBranchJet4.beta,
      oneForm4ContinuousLinearMap_smul]
  rw [hfield, fderiv_fun_smul hyDiff hthetaDiff]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [C.thetaBFDeriv x hx u w, C.betaAmplitudeFDeriv x hx u,
    oneForm4ContinuousLinearMap_apply,
    (C.jet x).betaJet_eq_spectralComponent,
    oneFormJetEvaluate_spectralComponentOneFormJet]
  simp only [smul_eq_mul]

/-- **Automatic branch realization.** Actual amplitude and eigen-one-form
derivatives generate the complete derived branch certificate by the Frechet
product rule. -/
noncomputable def toRealized
    (C : CurvatureScalarBranchComponentPatch4 U) (hopen : IsOpen U) :
    RealizedCurvatureScalarBranchPatch4 U where
  jet := C.jet
  alphaDifferentiable := C.alphaDifferentiable
  betaDifferentiable := C.betaDifferentiable
  alphaFDeriv := C.alphaFDeriv hopen
  betaFDeriv := C.betaFDeriv hopen

end CurvatureScalarBranchComponentPatch4

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

namespace CurvatureScalarBranchComponentPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- First actual spectral-component one-form field, before the derived
realization wrapper is constructed. -/
noncomputable def alphaField
    (C : CurvatureScalarBranchComponentPatch4 U) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
  fun x => oneForm4ContinuousLinearMap (C.jet x).alpha

/-- Second actual spectral-component one-form field. -/
noncomputable def betaField
    (C : CurvatureScalarBranchComponentPatch4 U) :
    CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
  fun x => oneForm4ContinuousLinearMap (C.jet x).beta

/-- Actual sum candidate assembled directly from the constituent fields. -/
noncomputable def plusField
    (C : CurvatureScalarBranchComponentPatch4 U) :=
  C.alphaField + C.betaField

/-- Actual difference candidate assembled directly from the constituent
fields. -/
noncomputable def minusField
    (C : CurvatureScalarBranchComponentPatch4 U) :=
  C.alphaField - C.betaField

/-- Direct component-field statement that the sum candidate has a local
scalar potential. -/
def PlusScalarPotentialExists
    (C : CurvatureScalarBranchComponentPatch4 U) : Prop :=
  ∃ phi : CurvatureCoordinateSpace4 → ℝ,
    IsScalarPotentialOn phi C.plusField U

/-- Direct component-field statement that the difference candidate has a
local scalar potential. -/
def MinusScalarPotentialExists
    (C : CurvatureScalarBranchComponentPatch4 U) : Prop :=
  ∃ phi : CurvatureCoordinateSpace4 → ℝ,
    IsScalarPotentialOn phi C.minusField U

/-- The directly assembled sum field is closed exactly when the curvature
sum obstruction vanishes. -/
theorem plusField_closed_iff
    (C : CurvatureScalarBranchComponentPatch4 U) (hopen : IsOpen U) :
    IsClosedScalarOneFormOn C.plusField U ↔
      CurvaturePlusBranchClosesOn C.jet U := by
  exact (C.toRealized hopen).plusField_closed_iff hopen

/-- The directly assembled difference field is closed exactly when the
curvature difference obstruction vanishes. -/
theorem minusField_closed_iff
    (C : CurvatureScalarBranchComponentPatch4 U) (hopen : IsOpen U) :
    IsClosedScalarOneFormOn C.minusField U ↔
      CurvatureMinusBranchClosesOn C.jet U := by
  exact (C.toRealized hopen).minusField_closed_iff hopen

/-- Direct smooth-component sum-branch potential criterion. -/
theorem plusScalarPotentialExists_iff_curvatureBranchCloses
    (C : CurvatureScalarBranchComponentPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    C.PlusScalarPotentialExists ↔
      CurvaturePlusBranchClosesOn C.jet U := by
  exact (C.toRealized hopen).plusScalarPotentialExists_iff_curvatureBranchCloses
    hconvex hopen

/-- Direct smooth-component difference-branch potential criterion. -/
theorem minusScalarPotentialExists_iff_curvatureBranchCloses
    (C : CurvatureScalarBranchComponentPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    C.MinusScalarPotentialExists ↔
      CurvatureMinusBranchClosesOn C.jet U := by
  exact (C.toRealized hopen).minusScalarPotentialExists_iff_curvatureBranchCloses
    hconvex hopen

/-- **Smooth-component scalar-branch composition theorem.** The actual
curvature amplitude and eigen-one-form fields, with only their constituent
first derivatives supplied, return the exhaustive zero/one/two local
potential list. -/
theorem exhaustive_local_scalarPotential_classification
    (C : CurvatureScalarBranchComponentPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U) :
    (C.PlusScalarPotentialExists ∧
        ¬C.MinusScalarPotentialExists) ∨
      (¬C.PlusScalarPotentialExists ∧
        C.MinusScalarPotentialExists) ∨
      (C.PlusScalarPotentialExists ∧
        C.MinusScalarPotentialExists) ∨
      (¬C.PlusScalarPotentialExists ∧
        ¬C.MinusScalarPotentialExists) := by
  exact (C.toRealized hopen).exhaustive_local_scalarPotential_classification
    hconvex hopen

/-- Direct smooth-component finite certificate ruling out both scalar
potentials. -/
theorem no_local_scalarPotentialBranch_of_witnesses
    (C : CurvatureScalarBranchComponentPatch4 U)
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    {zPlus zMinus : CurvatureCoordinateSpace4}
    (hzPlus : zPlus ∈ U) (hzMinus : zMinus ∈ U)
    (hplus : (C.jet zPlus).dalpha + (C.jet zPlus).dbeta ≠ 0)
    (hminus : (C.jet zMinus).dalpha - (C.jet zMinus).dbeta ≠ 0) :
    ¬C.PlusScalarPotentialExists ∧
      ¬C.MinusScalarPotentialExists := by
  exact (C.toRealized hopen).no_local_scalarPotentialBranch_of_witnesses
    hconvex hopen hzPlus hzMinus hplus hminus

end CurvatureScalarBranchComponentPatch4

end RainichKaluza
