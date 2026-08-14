import RainichKaluza.ActualCoordinateRicciFirstJet

/-!
# Coordinate Einstein curvature and its first jet

This file builds the Einstein tensor from the repository's literal coordinate
Ricci field.  It also isolates the algebraic first-jet evaluator needed by a
contracted-Bianchi proof and proves the normal-coordinate form of that
identity.  The remaining K1 step is to transport this cancellation to an
arbitrary coordinate metric jet (or prove it there directly), and then apply
the actual-field chain rule below.
-/

namespace RainichKaluza

section CoordinateEinstein

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Scalar curvature obtained by contracting the coordinate Ricci tensor. -/
noncomputable def coordinateScalarCurvature
    (gInv : Matrix I I ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) : ℝ :=
  ∑ i : I, ∑ j : I, gInv i j * coordinateRicci gInv dg ddg i j

/-- Product-rule first jet of `coordinateScalarCurvature`. -/
noncomputable def coordinateScalarCurvatureFirstJet
    (gInv : Matrix I I ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (dddg : CoordinateMetricJet3 I)
    (r : I) : ℝ :=
  ∑ i : I, ∑ j : I, (
    coordinateInverseMetricJet gInv dg r i j *
        coordinateRicci gInv dg ddg i j +
      gInv i j * coordinateRicciFirstJet gInv dg ddg dddg r i j)

/-- Covariant coordinate Einstein tensor
`G_ij = Ric_ij - (1/2) g_ij R`. -/
noncomputable def coordinateEinsteinCovariant
    (g : Matrix I I ℝ) (gInv : Matrix I I ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (i j : I) : ℝ :=
  coordinateRicci gInv dg ddg i j -
    g i j * coordinateScalarCurvature gInv dg ddg / 2

/-- Product-rule first jet of the covariant coordinate Einstein tensor. -/
noncomputable def coordinateEinsteinCovariantFirstJet
    (g : Matrix I I ℝ) (gInv : Matrix I I ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (dddg : CoordinateMetricJet3 I) (r i j : I) : ℝ :=
  coordinateRicciFirstJet gInv dg ddg dddg r i j -
    (dg r i j * coordinateScalarCurvature gInv dg ddg +
      g i j * coordinateScalarCurvatureFirstJet gInv dg ddg dddg r) / 2

/-- Contract the covariant derivative of a covariant rank-two tensor in its
first tensor slot: `g^{ir} nabla_r T_ij`. -/
noncomputable def coordinateCovariant2Divergence
    (gInv : Matrix I I ℝ) (dg : CoordinateMetricJet1 I)
    (T : Matrix I I ℝ) (dT : I → Matrix I I ℝ) (j : I) : ℝ :=
  ∑ r : I, ∑ i : I, gInv i r *
    (dT r i j -
      (∑ a : I, coordinateChristoffel gInv dg a r i * T a j) -
      (∑ a : I, coordinateChristoffel gInv dg a r j * T i a))

end CoordinateEinstein

/-! ## The normal-coordinate algebraic Bianchi cancellation -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- In a Minkowski normal frame, the first jet of the coordinate Einstein
tensor has zero contracted divergence.  The hypotheses are precisely the
commuting derivative slots and symmetric metric slots of a genuine metric
three-jet.

This is the tensorial core of K1 at a normal-coordinate point; unlike the
eventual actual-field theorem, it is a statement about a formal metric jet. -/
theorem coordinateEinsteinCovariantFirstJet_minkowski_zero_contractedBianchi
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h31 : ∀ a b c i j, g3 a b c i j = g3 b a c i j)
    (h32 : ∀ a b c i j, g3 a b c i j = g3 a c b i j)
    (h3g : ∀ a b c i j, g3 a b c i j = g3 a b c j i)
    (j : Fin 4) :
    coordinateCovariant2Divergence minkowskiMetric 0
        (fun i k ↦ coordinateEinsteinCovariant
          minkowskiMetric minkowskiMetric 0 g2 i k)
        (fun r i k ↦ coordinateEinsteinCovariantFirstJet
          minkowskiMetric minkowskiMetric 0 g2 g3 r i k) j = 0 := by
  fin_cases j <;>
    unfold coordinateCovariant2Divergence
      coordinateEinsteinCovariantFirstJet
      coordinateScalarCurvatureFirstJet <;>
    simp only [coordinateRicciFirstJet_minkowski_zero] <;>
    simp [
      coordinateInverseMetricJet,
      coordinateChristoffel,
      coordinateChristoffelFirstKind,
      normalFrameBaseRicci,
      minkowskiMetric, minkowskiSign, Fin.sum_univ_succ,
      h31, h32, h3g] <;>
    ring_nf
  · rw [h31 2 1 0 2 0,
      h3g 1 2 1 2 1, h31 1 2 1 1 2,
      h3g 2 1 1 2 1,
      h31 1 2 2 0 0, h32 2 1 2 0 0,
      h31 1 2 3 2 3,
      h31 1 2 2 3 3, h32 2 1 2 3 3]
    ring
  · rw [h32 1 0 2 1 0, h31 1 2 0 1 0,
      h32 0 0 2 1 1, h31 0 2 0 1 1,
      h31 0 2 3 0 3,
      h32 0 0 2 3 3, h31 0 2 0 3 3,
      h32 1 1 2 0 0, h31 1 2 1 0 0,
      h31 1 2 3 1 3,
      h32 1 1 2 3 3, h31 1 2 1 3 3,
      h3g 2 2 0 0 2,
      h32 2 0 2 2 0,
      h3g 2 2 1 1 2,
      h32 2 1 2 2 1]
    ring

/-! ## Literal actual fields -/

/-- Scalar curvature of the literal coordinate metric field. -/
noncomputable def actualCoordinateScalarCurvatureField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    (coordinateMetricMatrixField4 g z)⁻¹ i j *
      actualCoordinateRicciCovariantField4 g z i j

/-- The literal covariant coordinate Einstein tensor built from
`actualCoordinateRicciCovariantField4`. -/
noncomputable def actualCoordinateEinsteinField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Matrix4 :=
  fun i j ↦ actualCoordinateRicciCovariantField4 g z i j -
    coordinateMetricMatrixField4 g z i j *
      actualCoordinateScalarCurvatureField4 g z / 2

private theorem scalarFieldCoordinateFDeriv_mul_of_differentiableAt
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

private theorem scalarFieldCoordinateFDeriv_sub_of_differentiableAt
    (f h : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y - h y) z r =
      scalarFieldCoordinateFDeriv f z r -
        scalarFieldCoordinateFDeriv h z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f - h) z) _ = _
  rw [fderiv_sub hf hh]
  rfl

private theorem scalarFieldCoordinateFDeriv_sum_of_differentiableAt
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
  simp
  exact fun i _ ↦ hf i

/-- The derivative of the literal scalar-curvature field is the algebraic
product-rule evaluator on the genuine metric three-jet.  Componentwise
differentiability of the composed Ricci field is kept explicit here: the
existing Ricci theorem identifies its derivative but does not package this
regularity fact. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateScalarCurvatureField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (hRic : ∀ i j, DifferentiableAt ℝ
      (fun y ↦ actualCoordinateRicciCovariantField4 g y i j) z)
    (r : Fin 4) :
    scalarFieldCoordinateFDeriv
        (actualCoordinateScalarCurvatureField4 g) z r =
      coordinateScalarCurvatureFirstJet
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (actualCoordinateMetricJet2Field4 g z)
        (actualCoordinateMetricJet3Field4 g z) r := by
  have hInv (i j : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹ i j) z :=
    differentiableAt_matrixNonsingInv_apply4
      (coordinateMetricMatrixField4 g) z hreg.metric hdet i j
  unfold actualCoordinateScalarCurvatureField4
    coordinateScalarCurvatureFirstJet
  rw [scalarFieldCoordinateFDeriv_sum_of_differentiableAt _ z r (by
    intro i
    rw [show (fun y ↦ ∑ j : Fin 4,
        (coordinateMetricMatrixField4 g y)⁻¹ i j *
          actualCoordinateRicciCovariantField4 g y i j) =
      ∑ j : Fin 4, fun y ↦
        (coordinateMetricMatrixField4 g y)⁻¹ i j *
          actualCoordinateRicciCovariantField4 g y i j by rfl]
    apply DifferentiableAt.sum
    intro j _
    exact (hInv i j).mul (hRic i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarFieldCoordinateFDeriv_sum_of_differentiableAt _ z r (by
    intro j
    exact (hInv i j).mul (hRic i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarFieldCoordinateFDeriv_mul_of_differentiableAt _ _ z r
      (hInv i j) (hRic i j),
    scalarFieldCoordinateFDeriv_matrixNonsingInv_apply4
      (coordinateMetricMatrixField4 g) z hreg.metric hdet r i j,
    scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4
      g z hreg hdet r i j]
  rfl

/-- **Actual Einstein first-jet factorization.**  Differentiating the literal
Einstein field consumes exactly the actual metric three-jet and agrees with
`coordinateEinsteinCovariantFirstJet`. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateEinsteinField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (hRic : ∀ i j, DifferentiableAt ℝ
      (fun y ↦ actualCoordinateRicciCovariantField4 g y i j) z)
    (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateEinsteinField4 g y i j) z r =
      coordinateEinsteinCovariantFirstJet
        (coordinateMetricMatrixField4 g z)
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (actualCoordinateMetricJet2Field4 g z)
        (actualCoordinateMetricJet3Field4 g z) r i j := by
  have hInv (a b : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ (coordinateMetricMatrixField4 g y)⁻¹ a b) z :=
    differentiableAt_matrixNonsingInv_apply4
      (coordinateMetricMatrixField4 g) z hreg.metric hdet a b
  have hScalar : DifferentiableAt ℝ
      (actualCoordinateScalarCurvatureField4 g) z := by
    unfold actualCoordinateScalarCurvatureField4
    rw [show (fun y ↦ ∑ i : Fin 4, ∑ j : Fin 4,
        (coordinateMetricMatrixField4 g y)⁻¹ i j *
          actualCoordinateRicciCovariantField4 g y i j) =
      ∑ i : Fin 4, fun y ↦ ∑ j : Fin 4,
        (coordinateMetricMatrixField4 g y)⁻¹ i j *
          actualCoordinateRicciCovariantField4 g y i j by rfl]
    apply DifferentiableAt.sum
    intro a _
    rw [show (fun y ↦ ∑ b : Fin 4,
        (coordinateMetricMatrixField4 g y)⁻¹ a b *
          actualCoordinateRicciCovariantField4 g y a b) =
      ∑ b : Fin 4, fun y ↦
        (coordinateMetricMatrixField4 g y)⁻¹ a b *
          actualCoordinateRicciCovariantField4 g y a b by rfl]
    apply DifferentiableAt.sum
    intro b _
    exact (hInv a b).mul (hRic a b)
  have hScalarJet :=
    scalarFieldCoordinateFDeriv_actualCoordinateScalarCurvatureField4
      g z hreg hdet hRic r
  have hProduct : DifferentiableAt ℝ
      (fun y ↦ coordinateMetricMatrixField4 g y i j *
        actualCoordinateScalarCurvatureField4 g y) z :=
    (hreg.metric i j).mul hScalar
  have hHalf : DifferentiableAt ℝ
      (fun y ↦ coordinateMetricMatrixField4 g y i j *
        actualCoordinateScalarCurvatureField4 g y / 2) z := by
    simpa [div_eq_mul_inv, mul_comm] using
      hProduct.const_mul (1 / 2 : ℝ)
  have hHalfJet : scalarFieldCoordinateFDeriv
      (fun y ↦ coordinateMetricMatrixField4 g y i j *
        actualCoordinateScalarCurvatureField4 g y / 2) z r =
      (actualCoordinateMetricJet1Field4 g z r i j *
          actualCoordinateScalarCurvatureField4 g z +
        coordinateMetricMatrixField4 g z i j *
          coordinateScalarCurvatureFirstJet
            ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
            (actualCoordinateMetricJet1Field4 g z)
            (actualCoordinateMetricJet2Field4 g z)
            (actualCoordinateMetricJet3Field4 g z) r) / 2 := by
    rw [show (fun y ↦ coordinateMetricMatrixField4 g y i j *
        actualCoordinateScalarCurvatureField4 g y / 2) =
      fun y ↦ (coordinateMetricMatrixField4 g y i j *
        actualCoordinateScalarCurvatureField4 g y) * (1 / 2 : ℝ) by
      funext y
      ring]
    rw [scalarFieldCoordinateFDeriv_mul_of_differentiableAt _ _ z r
        hProduct (by fun_prop),
      scalarFieldCoordinateFDeriv_mul_of_differentiableAt _ _ z r
        (hreg.metric i j) hScalar,
      hScalarJet]
    rw [show scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateMetricMatrixField4 g y i j) z r =
      actualCoordinateMetricJet1Field4 g z r i j by rfl]
    rw [show scalarFieldCoordinateFDeriv
        (fun _ : CurvatureCoordinateSpace4 ↦ (1 / 2 : ℝ)) z r = 0 by
      simp [scalarFieldCoordinateFDeriv]]
    ring
  change scalarFieldCoordinateFDeriv
      (fun y ↦ actualCoordinateRicciCovariantField4 g y i j -
        coordinateMetricMatrixField4 g y i j *
          actualCoordinateScalarCurvatureField4 g y / 2) z r = _
  rw [scalarFieldCoordinateFDeriv_sub_of_differentiableAt _ _ z r
      (hRic i j) hHalf,
    scalarFieldCoordinateFDeriv_actualCoordinateRicciCovariantField4
      g z hreg hdet r i j,
    hHalfJet]
  unfold coordinateEinsteinCovariantFirstJet
    actualCoordinateScalarCurvatureField4 coordinateScalarCurvature
  rfl

/-- Literal contracted divergence of the actual coordinate Einstein field at
one point.  This definition deliberately exposes the partial first jet used
inside the covariant derivative. -/
noncomputable def actualCoordinateEinsteinContractedDivergenceAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) (j : Fin 4) : ℝ :=
  coordinateCovariant2Divergence
    ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
    (actualCoordinateMetricJet1Field4 g z)
    (actualCoordinateEinsteinField4 g z)
    (fun r i k ↦ scalarFieldCoordinateFDeriv
      (fun y ↦ actualCoordinateEinsteinField4 g y i k) z r) j

/-- The actual contracted divergence factors through the finite algebraic
metric three-jet.  Thus the remaining arbitrary-coordinate K1 obligation is
entirely the algebraic cancellation on the right. -/
theorem actualCoordinateEinsteinContractedDivergenceAt4_eq_coordinate
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0)
    (hRic : ∀ i j, DifferentiableAt ℝ
      (fun y ↦ actualCoordinateRicciCovariantField4 g y i j) z)
    (j : Fin 4) :
    actualCoordinateEinsteinContractedDivergenceAt4 g z j =
      coordinateCovariant2Divergence
        ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
        (actualCoordinateMetricJet1Field4 g z)
        (fun i k ↦ coordinateEinsteinCovariant
          (coordinateMetricMatrixField4 g z)
          ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
          (actualCoordinateMetricJet1Field4 g z)
          (actualCoordinateMetricJet2Field4 g z) i k)
        (fun r i k ↦ coordinateEinsteinCovariantFirstJet
          (coordinateMetricMatrixField4 g z)
          ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4)
          (actualCoordinateMetricJet1Field4 g z)
          (actualCoordinateMetricJet2Field4 g z)
          (actualCoordinateMetricJet3Field4 g z) r i k) j := by
  unfold actualCoordinateEinsteinContractedDivergenceAt4
  simp_rw [scalarFieldCoordinateFDeriv_actualCoordinateEinsteinField4
    g z hreg hdet hRic]
  congr 1

/-- Contracted Bianchi for an actual field at a Minkowski normal-coordinate
point.  This is not yet the arbitrary-coordinate K1 theorem: no theorem in
the current repository transports the three-jet divergence identity from a
normal frame to a general nonlinear chart. -/
theorem actualCoordinateEinsteinField4_contractedBianchi_of_minkowskiNormal
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hreg : CoordinateMetricThreeJetDifferentiableAt4 g z)
    (hRic : ∀ i j, DifferentiableAt ℝ
      (fun y ↦ actualCoordinateRicciCovariantField4 g y i j) z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (h31 : ∀ a b c i j,
      actualCoordinateMetricJet3Field4 g z a b c i j =
        actualCoordinateMetricJet3Field4 g z b a c i j)
    (h32 : ∀ a b c i j,
      actualCoordinateMetricJet3Field4 g z a b c i j =
        actualCoordinateMetricJet3Field4 g z a c b i j)
    (h3g : ∀ a b c i j,
      actualCoordinateMetricJet3Field4 g z a b c i j =
        actualCoordinateMetricJet3Field4 g z a b c j i)
    (j : Fin 4) :
    actualCoordinateEinsteinContractedDivergenceAt4 g z j = 0 := by
  have hdet : Matrix.det (coordinateMetricMatrixField4 g z) ≠ 0 := by
    rw [hmetric, minkowskiMetric_det]
    norm_num
  rw [actualCoordinateEinsteinContractedDivergenceAt4_eq_coordinate
    g z hreg hdet hRic j, hmetric, hfirst]
  have hinv : (minkowskiMetric⁻¹ : Matrix4) = minkowskiMetric :=
    Matrix.inv_eq_right_inv minkowskiMetric_sq
  rw [hinv]
  exact
    coordinateEinsteinCovariantFirstJet_minkowski_zero_contractedBianchi
      (actualCoordinateMetricJet2Field4 g z)
      (actualCoordinateMetricJet3Field4 g z) h31 h32 h3g j

end RainichKaluza
