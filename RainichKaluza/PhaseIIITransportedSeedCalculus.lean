import RainichKaluza.PhaseIIIRescaledSeedRealization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option maxSynthPendingDepth 2

/-!
# Calculus realization of the transported Phase-III seed

This file discharges the two coordinate-jet hypotheses isolated by
`PositiveQPhaseIIISeedPairC1Realization.ofSmoothCoordinateJets`.  The proof is
entrywise, so it does not require a noncanonical norm on `Matrix4`:

* `sqrt (2q)` has the displayed positive-branch derivative;
* finite scalar product rules differentiate `Lᵀ F L`;
* the resulting coordinate derivative is exactly the algebraic transported
  seed jet already used by the Phase-III exterior obstruction;
* `C²` regularity makes these actual first jets continuous.

Thus actual coordinate derivatives of `L` and `q` now suffice to construct the
constituent seed-pair realization consumed by the physical Maxwell-field
theorem.
-/

namespace RainichKaluza

open Set
open scoped Matrix Topology

@[simp]
theorem oneForm4ContinuousLinearMap_curvatureCoordinateDirection
    (v : OneForm4) (i : Fin 4) :
    oneForm4ContinuousLinearMap v (curvatureCoordinateDirection i) = v i := by
  simp [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
    curvatureCoordinateDirection, eq_comm]

/-- Continuous linear maps on four-space are equal when they agree on the
four coordinate directions.  Using the explicit basis expansion avoids
instance-coherence problems caused by unfolding the reducible coordinate
space abbreviation. -/
theorem continuousLinearMap_ext_curvatureCoordinateDirection
    {A B : CurvatureCoordinateSpace4 →L[ℝ] ℝ}
    (h : ∀ k, A (curvatureCoordinateDirection k) =
      B (curvatureCoordinateDirection k)) : A = B := by
  apply ContinuousLinearMap.ext
  intro u
  conv_lhs => rw [← curvatureCoordinateDirection_expansion u]
  conv_rhs => rw [← curvatureCoordinateDirection_expansion u]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k]

/-- A differentiable scalar field has the continuous-linear derivative
specified by its four coordinate components. -/
theorem hasFDerivAt_of_coordinateFDeriv
    (f : CurvatureCoordinateSpace4 → ℝ) (D : OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hf : DifferentiableAt ℝ f z)
    (hD : scalarFieldCoordinateFDeriv f z = D) :
    HasFDerivAt f (oneForm4ContinuousLinearMap D) z := by
  apply hf.hasFDerivAt.congr_fderiv
  ext u
  rw [scalarField_fderiv_eq_coordinateEvaluation, hD]
  rfl

/-- The positive amplitude `sqrt (2q)` has the exact derivative used in the
canonical Phase-III seed jet. -/
theorem hasFDerivAt_sqrt_two_mul
    (q : CurvatureCoordinateSpace4 → ℝ)
    (dq : OneForm4) (z : CurvatureCoordinateSpace4)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) :
    HasFDerivAt (fun y => Real.sqrt (2 * q y))
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k))) z := by
  have hsqrt := (hq.const_mul 2).sqrt (by positivity)
  have hderiv :
      (1 / (2 * Real.sqrt (2 * q z))) •
          ((2 : ℝ) • oneForm4ContinuousLinearMap dq) =
        oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k)) := by
    apply continuousLinearMap_ext_curvatureCoordinateDirection
    intro k
    simp only [smul_apply,
      oneForm4ContinuousLinearMap_curvatureCoordinateDirection, smul_eq_mul]
    unfold canonicalPositiveQAmplitudeDerivative
    have hsqrt0 : Real.sqrt (2 * q z) ≠ 0 := by positivity
    field_simp [hsqrt0]
  exact hsqrt.congr_fderiv hderiv

/-- Entrywise derivative of the canonical positive-`q` electric seed. -/
theorem hasFDerivAt_smoothCanonicalPositiveQSeed_entry
    (q : CurvatureCoordinateSpace4 → ℝ)
    (dq : OneForm4) (z : CurvatureCoordinateSpace4)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    HasFDerivAt (fun y => smoothCanonicalPositiveQSeed q y i j)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQSeedDerivative (q z) (dq k) i j)) z := by
  have hamp := hasFDerivAt_sqrt_two_mul q dq z hq hqPos
  let eij := canonicalMaxwellTwoForm 1 0 i j
  have hfun : (fun y => smoothCanonicalPositiveQSeed q y i j) =
      fun y => Real.sqrt (2 * q y) * eij := by
    funext y
    dsimp only [eij]
    fin_cases i <;> fin_cases j <;>
      simp [smoothCanonicalPositiveQSeed, canonicalMaxwellTwoForm]
  have hderiv :
      oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQSeedDerivative (q z) (dq k) i j) =
        eij • oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k)) := by
    have hentry (k : Fin 4) :
        canonicalPositiveQSeedDerivative (q z) (dq k) i j =
          canonicalPositiveQAmplitudeDerivative (q z) (dq k) * eij := by
      dsimp only [eij]
      fin_cases i <;> fin_cases j <;>
        simp [canonicalPositiveQSeedDerivative, canonicalMaxwellTwoForm]
    ext u
    simp only [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
      smul_apply, smul_eq_mul]
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun, hderiv]
  exact hamp.mul_const eij

/-- Entrywise derivative of the canonical positive-`q` Hodge seed. -/
theorem hasFDerivAt_smoothCanonicalPositiveQHodgeSeed_entry
    (q : CurvatureCoordinateSpace4 → ℝ)
    (dq : OneForm4) (z : CurvatureCoordinateSpace4)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    HasFDerivAt (fun y => smoothCanonicalPositiveQHodgeSeed q y i j)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQHodgeSeedDerivative (q z) (dq k) i j)) z := by
  have hamp := hasFDerivAt_sqrt_two_mul q dq z hq hqPos
  let eij := canonicalHodgeStar 1 0 i j
  have hfun : (fun y => smoothCanonicalPositiveQHodgeSeed q y i j) =
      fun y => Real.sqrt (2 * q y) * eij := by
    funext y
    dsimp only [eij]
    fin_cases i <;> fin_cases j <;>
      simp [smoothCanonicalPositiveQHodgeSeed, canonicalHodgeStar,
        canonicalMaxwellTwoForm]
  have hderiv :
      oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQHodgeSeedDerivative (q z) (dq k) i j) =
        eij • oneForm4ContinuousLinearMap
          (fun k => canonicalPositiveQAmplitudeDerivative (q z) (dq k)) := by
    have hentry (k : Fin 4) :
        canonicalPositiveQHodgeSeedDerivative (q z) (dq k) i j =
          canonicalPositiveQAmplitudeDerivative (q z) (dq k) * eij := by
      dsimp only [eij]
      fin_cases i <;> fin_cases j <;>
        simp [canonicalPositiveQHodgeSeedDerivative, canonicalHodgeStar,
          canonicalMaxwellTwoForm]
    ext u
    simp only [oneForm4ContinuousLinearMap_apply, oneForm4Evaluate,
      smul_apply, smul_eq_mul]
    simp_rw [hentry]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hfun, hderiv]
  exact hamp.mul_const eij

/-- The scalar-entry product rule for a transported two-form.  This is the
calculus counterpart of `transportedTwoFormDerivative`. -/
theorem hasFDerivAt_transportTwoForm_entry
    (L F : CurvatureCoordinateSpace4 → Matrix4)
    (dL dF : Fin 4 → Matrix4) (z : CurvatureCoordinateSpace4)
    (hL : ∀ i j, HasFDerivAt (fun y => L y i j)
      (oneForm4ContinuousLinearMap (fun k => dL k i j)) z)
    (hF : ∀ i j, HasFDerivAt (fun y => F y i j)
      (oneForm4ContinuousLinearMap (fun k => dF k i j)) z)
    (i j : Fin 4) :
    HasFDerivAt (fun y => transportTwoForm (L y) (F y) i j)
      (oneForm4ContinuousLinearMap
        (fun k => transportedTwoFormDerivative (L z) (dL k)
          (F z) (dF k) i j)) z := by
  let Dsum : CurvatureCoordinateSpace4 →L[ℝ] ℝ :=
    ∑ b, ∑ a, (
      (L z a i * F z a b) •
          oneForm4ContinuousLinearMap (fun k => dL k b j) +
        L z b j •
          (L z a i • oneForm4ContinuousLinearMap (fun k => dF k a b) +
            F z a b • oneForm4ContinuousLinearMap (fun k => dL k a i)))
  have hsum : HasFDerivAt
      (fun y => ∑ b, ∑ a, (L y a i * F y a b) * L y b j)
      Dsum z := by
    dsimp only [Dsum]
    exact HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
        ((hL a i).mul (hF a b)).mul (hL b j)))
  have hfun : (fun y => transportTwoForm (L y) (F y) i j) =
      fun y => ∑ b, ∑ a, (L y a i * F y a b) * L y b j := by
    funext y
    simp only [transportTwoForm, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul]
  have hderiv : oneForm4ContinuousLinearMap
        (fun k => transportedTwoFormDerivative (L z) (dL k)
          (F z) (dF k) i j) = Dsum := by
    have hentry (k : Fin 4) :
        transportedTwoFormDerivative (L z) (dL k) (F z) (dF k) i j =
          ∑ b, ∑ a,
            ((L z a i * F z a b) * dL k b j +
              L z b j * (L z a i * dF k a b + F z a b * dL k a i)) := by
      calc
        transportedTwoFormDerivative (L z) (dL k) (F z) (dF k) i j =
            (∑ b, ∑ a, dL k a i * F z a b * L z b j) +
            (∑ b, ∑ a, L z a i * dF k a b * L z b j) +
            (∑ b, ∑ a, L z a i * F z a b * dL k b j) := by
          simp only [transportedTwoFormDerivative, Matrix.add_apply,
            Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        _ = ∑ b, ∑ a,
            ((L z a i * F z a b) * dL k b j +
              L z b j *
                (L z a i * dF k a b + F z a b * dL k a i)) := by
          simp only [mul_add, Finset.sum_add_distrib]
          have hframe :
              (∑ b, ∑ a, dL k a i * F z a b * L z b j) =
                ∑ b, ∑ a, L z b j * F z a b * dL k a i := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            ring
          have hamplitude :
              (∑ b, ∑ a, L z a i * dF k a b * L z b j) =
                ∑ b, ∑ a, L z b j * L z a i * dF k a b := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            ring
          rw [hframe, hamplitude]
          simp only [mul_assoc]
          abel
    apply continuousLinearMap_ext_curvatureCoordinateDirection
    intro k
    rw [oneForm4ContinuousLinearMap_curvatureCoordinateDirection]
    dsimp only [Dsum]
    simp only [sum_apply, add_apply, smul_apply,
      oneForm4ContinuousLinearMap_curvatureCoordinateDirection, smul_eq_mul]
    rw [hentry]
  rw [hfun, hderiv]
  exact hsum

/-- The displayed electric transported-seed jet is the actual coordinate
Fréchet derivative once `dL,dq` are the actual coordinate derivatives. -/
theorem smoothTransportedPositiveQSeed_coordinateFDeriv_eq
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (dL : Fin 4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ) (dq : OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hL : ∀ i j, HasFDerivAt (fun y => L y i j)
      (oneForm4ContinuousLinearMap (fun k => dL k i j)) z)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => smoothTransportedPositiveQSeed L q y i j) z =
      fun k => localPositiveQSeedFirstDerivative (L z) dL (q z) dq k i j := by
  have hcanonical : ∀ a b, HasFDerivAt
      (fun y => smoothCanonicalPositiveQSeed q y a b)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQSeedDerivative (q z) (dq k) a b)) z :=
    fun a b => hasFDerivAt_smoothCanonicalPositiveQSeed_entry
      q dq z hq hqPos a b
  have htransport := hasFDerivAt_transportTwoForm_entry
    L (smoothCanonicalPositiveQSeed q) dL
      (fun k => canonicalPositiveQSeedDerivative (q z) (dq k))
    z hL hcanonical i j
  change scalarFieldCoordinateFDeriv
      (fun y => transportTwoForm (L y)
        (smoothCanonicalPositiveQSeed q y) i j) z = _
  funext k
  have happly := congrArg
    (fun A : CurvatureCoordinateSpace4 →L[ℝ] ℝ =>
      A (curvatureCoordinateDirection k)) htransport.fderiv
  simpa only [scalarFieldCoordinateFDeriv,
    oneForm4ContinuousLinearMap_curvatureCoordinateDirection,
    localPositiveQSeedFirstDerivative,
    transportedPositiveQSeedDerivative,
    smoothCanonicalPositiveQSeed] using happly

/-- The displayed Hodge transported-seed jet is likewise the actual
coordinate Fréchet derivative. -/
theorem smoothTransportedPositiveQHodgeSeed_coordinateFDeriv_eq
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (dL : Fin 4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ) (dq : OneForm4)
    (z : CurvatureCoordinateSpace4)
    (hL : ∀ i j, HasFDerivAt (fun y => L y i j)
      (oneForm4ContinuousLinearMap (fun k => dL k i j)) z)
    (hq : HasFDerivAt q (oneForm4ContinuousLinearMap dq) z)
    (hqPos : 0 < q z) (i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => transportedPositiveQHodgeSeed (L y) (q y) i j) z =
      fun k => localPositiveQHodgeSeedFirstDerivative
        (L z) dL (q z) dq k i j := by
  have hcanonical : ∀ a b, HasFDerivAt
      (fun y => smoothCanonicalPositiveQHodgeSeed q y a b)
      (oneForm4ContinuousLinearMap
        (fun k => canonicalPositiveQHodgeSeedDerivative
          (q z) (dq k) a b)) z :=
    fun a b => hasFDerivAt_smoothCanonicalPositiveQHodgeSeed_entry
      q dq z hq hqPos a b
  have htransport := hasFDerivAt_transportTwoForm_entry
    L (smoothCanonicalPositiveQHodgeSeed q) dL
      (fun k => canonicalPositiveQHodgeSeedDerivative (q z) (dq k))
    z hL hcanonical i j
  change scalarFieldCoordinateFDeriv
      (fun y => transportTwoForm (L y)
        (smoothCanonicalPositiveQHodgeSeed q y) i j) z = _
  funext k
  have happly := congrArg
    (fun A : CurvatureCoordinateSpace4 →L[ℝ] ℝ =>
      A (curvatureCoordinateDirection k)) htransport.fderiv
  simpa only [scalarFieldCoordinateFDeriv,
    oneForm4ContinuousLinearMap_curvatureCoordinateDirection,
    localPositiveQHodgeSeedFirstDerivative,
    transportedPositiveQHodgeSeedDerivative,
    smoothCanonicalPositiveQHodgeSeed] using happly

/-- Full principal tetrad obtained from two fixed probes in each varying
matrix-projector range.  This is the matrix-field version needed by the
curvature Lagrange projectors. -/
noncomputable def smoothMatrixProjectedPrincipalTetrad
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P Q : CurvatureCoordinateSpace4 → Matrix4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    (CurvatureCoordinateSpace4 × CurvatureCoordinateSpace4) ×
      (CurvatureCoordinateSpace4 × CurvatureCoordinateSpace4) :=
  (smoothLorentzianPlaneFrame g
      (smoothMatrixProjectedVector P u0)
      (smoothMatrixProjectedVector P u1) z,
    smoothSpacelikePlaneFrame g
      (smoothMatrixProjectedVector Q v0)
      (smoothMatrixProjectedVector Q v1) z)

/-- Componentwise smooth curvature projectors and one admissible fixed probe
quadruple produce the smooth principal tetrad used by the Maxwell seed. -/
theorem contDiffOn_smoothMatrixProjectedPrincipalTetrad
    {n : WithTop ℕ∞} {U : Set CurvatureCoordinateSpace4}
    {g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {P Q : CurvatureCoordinateSpace4 → Matrix4}
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (hg : ContDiffOn ℝ n g U)
    (hP : MatrixFieldContDiffOn n U P)
    (hQ : MatrixFieldContDiffOn n U Q)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector P u0)
      (smoothMatrixProjectedVector P u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector P u0)
        (smoothMatrixProjectedVector P u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector P u0)
        (smoothMatrixProjectedVector P u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector Q v0)
      (smoothMatrixProjectedVector Q v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector Q v0)
        (smoothMatrixProjectedVector Q v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector Q v0)
        (smoothMatrixProjectedVector Q v1)) z) :
    ContDiffOn ℝ n
      (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1) U := by
  have hPu0 := contDiffOn_smoothMatrixProjectedVector hP u0
  have hPu1 := contDiffOn_smoothMatrixProjectedVector hP u1
  have hQv0 := contDiffOn_smoothMatrixProjectedVector hQ v0
  have hQv1 := contDiffOn_smoothMatrixProjectedVector hQ v1
  exact (contDiffOn_smoothLorentzianPlaneFrame
    hg hPu0 hPu1 hL0 hL1).prodMk
      (contDiffOn_smoothSpacelikePlaneFrame
        hg hQv0 hQv1 hS0 hS1)

namespace PositiveQPhaseIIIPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- Build the Phase-III patch with all four displayed derivative arrays equal
to the actual coordinate Fréchet derivatives by definition.  The only
non-calculus inputs are the geometric complexion tangent equations. -/
noncomputable def ofActualCoordinateFDerivs
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdc : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hds : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z) :
    PositiveQPhaseIIIPatch4 U where
  L := L
  dL := fun z k i j =>
    scalarFieldCoordinateFDeriv (fun y => L y i j) z k
  q := q
  dq := scalarFieldCoordinateFDeriv q
  omega := omega
  c := c
  s := s
  coupling := coupling
  dc := scalarFieldCoordinateFDeriv c
  ds := scalarFieldCoordinateFDeriv s
  dc_eq := hdc
  ds_eq := hds

end PositiveQPhaseIIIPatch4

/-- A `C¹` scalar field has a continuous field of actual coordinate Fréchet
derivatives on an open patch. -/
theorem continuousOn_scalarFieldCoordinateFDeriv
    {U : Set CurvatureCoordinateSpace4}
    (f : CurvatureCoordinateSpace4 → ℝ)
    (hopen : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (scalarFieldCoordinateFDeriv f) U := by
  rw [continuousOn_pi]
  intro k
  have hderiv : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  simpa only [scalarFieldCoordinateFDeriv] using
    (continuousOn_clm_apply.mp hderiv (curvatureCoordinateDirection k))

/-- Coordinate Fréchet derivative of a cosine complexion coefficient. -/
theorem scalarFieldCoordinateFDeriv_cos
    (theta : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (htheta : DifferentiableAt ℝ theta z) :
    scalarFieldCoordinateFDeriv (fun y => Real.cos (theta y)) z =
      (-(Real.sin (theta z))) • scalarFieldCoordinateFDeriv theta z := by
  funext k
  unfold scalarFieldCoordinateFDeriv
  rw [fderiv_cos htheta]
  rfl

/-- Coordinate Fréchet derivative of a sine complexion coefficient. -/
theorem scalarFieldCoordinateFDeriv_sin
    (theta : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (htheta : DifferentiableAt ℝ theta z) :
    scalarFieldCoordinateFDeriv (fun y => Real.sin (theta y)) z =
      Real.cos (theta z) • scalarFieldCoordinateFDeriv theta z := by
  funext k
  unfold scalarFieldCoordinateFDeriv
  rw [fderiv_sin htheta]
  rfl

namespace PositiveQPhaseIIIPatch4

variable {U : Set CurvatureCoordinateSpace4}

/-- An actual smooth angle field gives the unit complexion pair and its
infinitesimal rate with both tangent equations satisfied automatically. -/
noncomputable def ofActualComplexionAngle
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q theta : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hopen : IsOpen U) (htheta : ContDiffOn ℝ 1 theta U) :
    PositiveQPhaseIIIPatch4 U :=
  ofActualCoordinateFDerivs L q (scalarFieldCoordinateFDeriv theta)
    (fun z => Real.cos (theta z)) (fun z => Real.sin (theta z)) coupling
    (fun z hz => scalarFieldCoordinateFDeriv_cos theta z
      ((htheta.differentiableOn_one z hz).differentiableAt
        (hopen.mem_nhds hz)))
    (fun z hz => scalarFieldCoordinateFDeriv_sin theta z
      ((htheta.differentiableOn_one z hz).differentiableAt
        (hopen.mem_nhds hz)))

/-- The angle-generated complexion coefficients lie on the unit circle. -/
theorem ofActualComplexionAngle_unit
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q theta : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hopen : IsOpen U) (htheta : ContDiffOn ℝ 1 theta U)
    (z : CurvatureCoordinateSpace4) :
    let M := ofActualComplexionAngle L q theta coupling hopen htheta
    M.c z ^ 2 + M.s z ^ 2 = 1 := by
  simp [ofActualComplexionAngle, ofActualCoordinateFDerivs,
    Real.cos_sq_add_sin_sq]

end PositiveQPhaseIIIPatch4

namespace PositiveQPhaseIIISeedPairC1Realization

variable {U : Set CurvatureCoordinateSpace4}

/-- **Concrete transported-seed realization.**  If `L,q` are `C²` and the
stored arrays `dL,dq` are their actual coordinate derivatives, then both
transported seeds have exactly the first jets used by the Phase-III
obstruction.  Their jet continuity follows from the continuity of the actual
Fréchet derivative, eliminating all independent seed-jet hypotheses. -/
noncomputable def ofSmoothFrameMagnitude
    (M : PositiveQPhaseIIIPatch4 U)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIISeedPairC1Realization M := by
  have hseedSmooth : MatrixFieldContDiffOn 2 U
      (fun z => (M.exteriorJet z).F0) := by
    change MatrixFieldContDiffOn 2 U
      (smoothTransportedPositiveQSeed M.L M.q)
    exact contDiffOn_smoothTransportedPositiveQSeed hL hq hqPos
  have hhodgeSmooth : MatrixFieldContDiffOn 2 U
      (fun z => (M.exteriorJet z).G0) := by
    simpa only [PositiveQPhaseIIIPatch4.exteriorJet,
      localPositiveQExteriorDualityJet] using
      (contDiffOn_transportedPositiveQHodgeSeed hL hq hqPos)
  have hseedJet : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => (M.exteriorJet y).F0 i j) z =
        fun k => M.seedFirstJet z k i j := by
    intro z hz i j
    have hLz : ∀ a b, HasFDerivAt (fun y => M.L y a b)
        (oneForm4ContinuousLinearMap (fun k => M.dL z k a b)) z := by
      intro a b
      exact hasFDerivAt_of_coordinateFDeriv _ _ z
        ((((hL a b).of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdL z hz a b)
    have hqz : HasFDerivAt M.q
        (oneForm4ContinuousLinearMap (M.dq z)) z :=
      hasFDerivAt_of_coordinateFDeriv _ _ z
        (((hq.of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdq z hz)
    change scalarFieldCoordinateFDeriv
        (fun y => smoothTransportedPositiveQSeed M.L M.q y i j) z = _
    exact smoothTransportedPositiveQSeed_coordinateFDeriv_eq
      M.L (M.dL z) M.q (M.dq z) z hLz hqz (hqPos z hz) i j
  have hhodgeSeedJet : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => (M.exteriorJet y).G0 i j) z =
        fun k => M.hodgeSeedFirstJet z k i j := by
    intro z hz i j
    have hLz : ∀ a b, HasFDerivAt (fun y => M.L y a b)
        (oneForm4ContinuousLinearMap (fun k => M.dL z k a b)) z := by
      intro a b
      exact hasFDerivAt_of_coordinateFDeriv _ _ z
        ((((hL a b).of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdL z hz a b)
    have hqz : HasFDerivAt M.q
        (oneForm4ContinuousLinearMap (M.dq z)) z :=
      hasFDerivAt_of_coordinateFDeriv _ _ z
        (((hq.of_le (by norm_num)).differentiableOn_one z hz).differentiableAt
          (hopen.mem_nhds hz)) (hdq z hz)
    change scalarFieldCoordinateFDeriv
        (fun y => transportedPositiveQHodgeSeed (M.L y) (M.q y) i j) z = _
    exact smoothTransportedPositiveQHodgeSeed_coordinateFDeriv_eq
      M.L (M.dL z) M.q (M.dq z) z hLz hqz (hqPos z hz) i j
  have hseedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.seedFirstJet z k i j) U := by
    intro k i j
    have hderiv : ContinuousOn
        (fderiv ℝ (fun z => (M.exteriorJet z).F0 i j)) U :=
      (hseedSmooth i j).continuousOn_fderiv_of_isOpen hopen (by norm_num)
    have happly := continuousOn_clm_apply.mp hderiv (coordinateDirection k)
    exact happly.congr (fun z hz => (congrFun (hseedJet z hz i j) k).symm)
  have hhodgeSeedJetContinuous : ∀ k i j,
      ContinuousOn (fun z => M.hodgeSeedFirstJet z k i j) U := by
    intro k i j
    have hderiv : ContinuousOn
        (fderiv ℝ (fun z => (M.exteriorJet z).G0 i j)) U :=
      (hhodgeSmooth i j).continuousOn_fderiv_of_isOpen hopen (by norm_num)
    have happly := continuousOn_clm_apply.mp hderiv (coordinateDirection k)
    exact happly.congr
      (fun z hz => (congrFun (hhodgeSeedJet z hz i j) k).symm)
  exact ofSmoothCoordinateJets M hopen (fun i j => (hL i j).of_le (by norm_num))
    (hq.of_le (by norm_num)) hqPos hseedJet hhodgeSeedJet
    hseedJetContinuous hhodgeSeedJetContinuous hc hs hdc hds

/-- The concrete calculus realization immediately supplies the precise
rescaled Maxwell realization consumed by the accepted-branch theorem. -/
noncomputable def rescaledOfSmoothFrameMagnitude
    (M : PositiveQPhaseIIIPatch4 U)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIIRescaledMaxwellC1Realization M :=
  (ofSmoothFrameMagnitude M hopen hL hq hqPos hdL hdq
    hc hs hdc hds).toRescaledMaxwellC1Realization

/-- The same concrete calculus retains both rescaled `C¹` channels. -/
noncomputable def rescaledPairOfSmoothFrameMagnitude
    (M : PositiveQPhaseIIIPatch4 U)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PositiveQPhaseIIIRescaledMaxwellC1PairRealization M :=
  (ofSmoothFrameMagnitude M hopen hL hq hqPos hdL hdq
    hc hs hdc hds).toRescaledMaxwellC1PairRealization

/-- Actual smooth fields instantiate the entire constituent seed-pair
realization automatically.  Only the complexion tangent equations used to
build the patch remain as geometric hypotheses. -/
noncomputable def ofActualSmoothFields
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdcEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hdsEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U L)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U) :
    PositiveQPhaseIIISeedPairC1Realization
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) := by
  let M := PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
    L q omega c s coupling hdcEq hdsEq
  apply ofSmoothFrameMagnitude M hopen hL hq hqPos
  · intro z _ i j
    rfl
  · intro z _
    rfl
  · intro z hz
    apply hasFDerivAt_of_coordinateFDeriv c
      (scalarFieldCoordinateFDeriv c z) z
    · exact ((hc.differentiableOn_one z hz).differentiableAt
        (hopen.mem_nhds hz))
    · rfl
  · intro z hz
    apply hasFDerivAt_of_coordinateFDeriv s
      (scalarFieldCoordinateFDeriv s z) z
    · exact ((hs.differentiableOn_one z hz).differentiableAt
        (hopen.mem_nhds hz))
    · rfl
  · exact continuousOn_scalarFieldCoordinateFDeriv c hopen hc
  · exact continuousOn_scalarFieldCoordinateFDeriv s hopen hs

/-- A `C¹` complexion angle eliminates the two remaining tangent-equation
hypotheses as well: cosine, sine, and the actual coordinate derivative of the
angle generate the complete smooth Phase-III seed realization. -/
noncomputable def ofActualSmoothComplexionAngle
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q theta : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U L)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (htheta : ContDiffOn ℝ 1 theta U) :
    PositiveQPhaseIIISeedPairC1Realization
      (PositiveQPhaseIIIPatch4.ofActualComplexionAngle
        L q theta coupling hopen htheta) := by
  unfold PositiveQPhaseIIIPatch4.ofActualComplexionAngle
  exact ofActualSmoothFields
    L q (scalarFieldCoordinateFDeriv theta)
      (fun z => Real.cos (theta z)) (fun z => Real.sin (theta z)) coupling
    (fun z hz => scalarFieldCoordinateFDeriv_cos theta z
      ((htheta.differentiableOn_one z hz).differentiableAt
        (hopen.mem_nhds hz)))
    (fun z hz => scalarFieldCoordinateFDeriv_sin theta z
      ((htheta.differentiableOn_one z hz).differentiableAt
        (hopen.mem_nhds hz)))
    hopen hL hq hqPos htheta.cos htheta.sin

/-- A smooth principal tetrad and a smooth complexion angle now form the
short, derivative-free entrance to the constituent Maxwell realization. -/
noncomputable def ofActualSmoothPrincipalTetradComplexionAngle
    (T : CurvatureCoordinateSpace4 →
      ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ×
        ((Fin 4 → ℝ) × (Fin 4 → ℝ)))
    (q theta : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hopen : IsOpen U)
    (hT : ContDiffOn ℝ 2 T U)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (htheta : ContDiffOn ℝ 1 theta U) :
    PositiveQPhaseIIISeedPairC1Realization
      (PositiveQPhaseIIIPatch4.ofActualComplexionAngle
        (smoothPrincipalCoframeMatrix T) q theta coupling hopen htheta) :=
  ofActualSmoothComplexionAngle (smoothPrincipalCoframeMatrix T)
    q theta coupling hopen (contDiffOn_smoothPrincipalCoframeMatrix hT)
      hq hqPos htheta

/-- The concrete fixed-probe projector construction supplies the `C²` coframe
required by `ofActualSmoothFields`.  This closes the frame part of the
curvature-to-Maxwell realization seam. -/
noncomputable def ofFixedProbeActualSmoothFields
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P Q : CurvatureCoordinateSpace4 → Matrix4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdcEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hdsEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z)
    (hopen : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U)
    (hP : MatrixFieldContDiffOn 2 U P)
    (hQ : MatrixFieldContDiffOn 2 U Q)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector P u0)
      (smoothMatrixProjectedVector P u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector P u0)
        (smoothMatrixProjectedVector P u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector P u0)
        (smoothMatrixProjectedVector P u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector Q v0)
      (smoothMatrixProjectedVector Q v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector Q v0)
        (smoothMatrixProjectedVector Q v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector Q v0)
        (smoothMatrixProjectedVector Q v1)) z)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U) :
    PositiveQPhaseIIISeedPairC1Realization
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        (smoothPrincipalCoframeMatrix
          (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1))
        q omega c s coupling hdcEq hdsEq) := by
  have hT : ContDiffOn ℝ 2
      (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1) U :=
    contDiffOn_smoothMatrixProjectedPrincipalTetrad u0 u1 v0 v1
      hg hP hQ hL0 hL1 hS0 hS1
  have hcoframe : MatrixFieldContDiffOn 2 U
      (smoothPrincipalCoframeMatrix
        (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1)) :=
    contDiffOn_smoothPrincipalCoframeMatrix hT
  exact ofActualSmoothFields
    (smoothPrincipalCoframeMatrix
      (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1))
    q omega c s coupling hdcEq hdsEq hopen hcoframe hq hqPos hc hs

/-- The actual-field constructor followed by the duality product rule gives
the accepted-branch rescaled Maxwell realization directly. -/
noncomputable def rescaledOfActualSmoothFields
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdcEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hdsEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U L)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U) :
    PositiveQPhaseIIIRescaledMaxwellC1Realization
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) :=
  (ofActualSmoothFields L q omega c s coupling hdcEq hdsEq
    hopen hL hq hqPos hc hs).toRescaledMaxwellC1Realization

/-- Actual smooth fields directly produce the paired rescaled realization. -/
noncomputable def rescaledPairOfActualSmoothFields
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdcEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hdsEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z)
    (hopen : IsOpen U)
    (hL : MatrixFieldContDiffOn 2 U L)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U) :
    PositiveQPhaseIIIRescaledMaxwellC1PairRealization
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) :=
  (ofActualSmoothFields L q omega c s coupling hdcEq hdsEq
    hopen hL hq hqPos hc hs).toRescaledMaxwellC1PairRealization

end PositiveQPhaseIIISeedPairC1Realization

namespace PhaseIIIAcceptedBranch

variable {U : Set CurvatureCoordinateSpace4}
  {C : CurvatureScalarBranchComponentPatch4 U}
  {M : PositiveQPhaseIIIPatch4 U}
  {branch : RelativeSignScalarBranch4}

/-- **Smooth seed to closed physical Maxwell field.**  An accepted Phase-III
branch, actual `C²` frame/magnitude fields, their displayed coordinate jets,
and actual `C¹` complexion coefficients canonically produce the matching
closed physical Maxwell field.  This composes the transported-seed calculus,
duality product rule, and exponential unweighting with no residual Maxwell
field-realization hypothesis. -/
noncomputable def toPhysicalMaxwellC1Realization_ofSmoothFrameMagnitude
    (A : PhaseIIIAcceptedBranch C M branch)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PhaseIIIPhysicalMaxwellC1Realization C M branch :=
  A.toPhysicalMaxwellC1Realization
    (PositiveQPhaseIIISeedPairC1Realization.rescaledOfSmoothFrameMagnitude
      M hopen hL hq hqPos hdL hdq hc hs hdc hds)
    hopen hstar

/-- **Smooth paired Phase-III handoff.** The same actual `C²` frame and
magnitude data now produce both the closed physical Maxwell field and the
closed weighted Hodge flux. -/
noncomputable def toPhysicalMaxwellC1PairRealization_ofSmoothFrameMagnitude
    (A : PhaseIIIAcceptedBranch C M branch)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hL : MatrixFieldContDiffOn 2 U M.L)
    (hq : ContDiffOn ℝ 2 M.q U) (hqPos : ∀ z ∈ U, 0 < M.q z)
    (hdL : ∀ z ∈ U, ∀ i j,
      scalarFieldCoordinateFDeriv (fun y => M.L y i j) z =
        fun k => M.dL z k i j)
    (hdq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv M.q z = M.dq z)
    (hc : ∀ z ∈ U,
      HasFDerivAt M.c (oneForm4ContinuousLinearMap (M.dc z)) z)
    (hs : ∀ z ∈ U,
      HasFDerivAt M.s (oneForm4ContinuousLinearMap (M.ds z)) z)
    (hdc : ContinuousOn M.dc U) (hds : ContinuousOn M.ds U) :
    PhaseIIIPhysicalMaxwellC1PairRealization C M branch :=
  A.toPhysicalMaxwellC1PairRealization
    (PositiveQPhaseIIISeedPairC1Realization.rescaledPairOfSmoothFrameMagnitude
      M hopen hL hq hqPos hdL hdq hc hs hdc hds)
    hopen hstar

/-- For an actual-derivative Phase-III patch, ordinary smoothness of the
frame, magnitude, and complexion coefficients plus the two tangent equations
already suffice to produce the accepted branch's closed physical Maxwell
field. -/
noncomputable def toPhysicalMaxwellC1Realization_ofActualSmoothFields
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdcEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hdsEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z)
    (A : PhaseIIIAcceptedBranch C
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) branch)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hL : MatrixFieldContDiffOn 2 U L)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U) :
    PhaseIIIPhysicalMaxwellC1Realization C
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) branch :=
  A.toPhysicalMaxwellC1Realization
    (PositiveQPhaseIIISeedPairC1Realization.rescaledOfActualSmoothFields
      L q omega c s coupling hdcEq hdsEq hopen hL hq hqPos hc hs)
    hopen hstar

/-- Actual smooth fields give the full paired physical handoff without an
independent field-realization hypothesis in either exterior channel. -/
noncomputable def toPhysicalMaxwellC1PairRealization_ofActualSmoothFields
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (omega : CurvatureCoordinateSpace4 → OneForm4)
    (c s : CurvatureCoordinateSpace4 → ℝ) (coupling : ℝ)
    (hdcEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv c z = (-(s z)) • omega z)
    (hdsEq : ∀ z ∈ U,
      scalarFieldCoordinateFDeriv s z = c z • omega z)
    (A : PhaseIIIAcceptedBranch C
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) branch)
    (hopen : IsOpen U) (hstar : StarConvex ℝ 0 U)
    (hL : MatrixFieldContDiffOn 2 U L)
    (hq : ContDiffOn ℝ 2 q U) (hqPos : ∀ z ∈ U, 0 < q z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U) :
    PhaseIIIPhysicalMaxwellC1PairRealization C
      (PositiveQPhaseIIIPatch4.ofActualCoordinateFDerivs
        L q omega c s coupling hdcEq hdsEq) branch :=
  A.toPhysicalMaxwellC1PairRealization
    (PositiveQPhaseIIISeedPairC1Realization.rescaledPairOfActualSmoothFields
      L q omega c s coupling hdcEq hdsEq hopen hL hq hqPos hc hs)
    hopen hstar

end PhaseIIIAcceptedBranch

end RainichKaluza
