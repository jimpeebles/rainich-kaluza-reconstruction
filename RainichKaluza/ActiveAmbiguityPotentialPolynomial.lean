import RainichKaluza.ActiveAmbiguityPotentialTwoJet

/-!
# Polynomial realization of the active Maxwell potential two-jet

The radial-gauge construction in `ActiveAmbiguityPotentialTwoJet` produces
compatible first- and second-derivative coefficient arrays.  This file
realizes those arrays by one explicit quadratic coordinate one-form field and
proves the realization using the repository's genuine nested Mathlib
`fderiv` convention.

This closes a finite holonomicity gap in the analytic EMD entrance data.  It
does not assert that the polynomial potential, together with the polynomial
metric, solves EMD away from the marked point.
-/

namespace RainichKaluza

open scoped Matrix

/-- Quadratic Taylor one-form with zero value, first jet `A1`, and symmetric
second jet `A2`.  The last index is the one-form component. -/
noncomputable def quadraticPotentialCoordinateField4
    (A1 : Matrix4) (A2 : OneFormSecondDerivative4)
    (x : CurvatureCoordinateSpace4) : OneForm4 :=
  fun j =>
    (∑ i : Fin 4, A1 i j * x i) +
      (1 / 2 : ℝ) *
        (∑ k : Fin 4, ∑ i : Fin 4, A2 k i j * x k * x i)

/-- The quadratic Taylor potential vanishes at the marked point. -/
@[simp] theorem quadraticPotentialCoordinateField4_zero
    (A1 : Matrix4) (A2 : OneFormSecondDerivative4) :
    quadraticPotentialCoordinateField4 A1 A2 0 = 0 := by
  funext j
  simp [quadraticPotentialCoordinateField4]

/-- The realizing potential is polynomial, hence smooth (indeed analytic). -/
theorem contDiff_quadraticPotentialCoordinateField4
    (A1 : Matrix4) (A2 : OneFormSecondDerivative4) (n : WithTop ℕ∞) :
    ContDiff ℝ n (quadraticPotentialCoordinateField4 A1 A2) := by
  unfold quadraticPotentialCoordinateField4
  fun_prop

private theorem scalarFieldCoordinateFDeriv_linearPotentialSum
    (A1 : Matrix4) (x : CurvatureCoordinateSpace4) (r j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => ∑ i : Fin 4, A1 i j * y i) x r = A1 r j := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      ∑ i : Fin 4, A1 i j * y i) =
    ∑ i : Fin 4, fun y => A1 i j * y i by rfl]
  rw [fderiv_sum]
  · simp only [sum_apply]
    have hterm (i : Fin 4) :
        (fderiv ℝ (fun y : CurvatureCoordinateSpace4 => A1 i j * y i) x)
            (curvatureCoordinateDirection r) =
          A1 i j * (if r = i then 1 else 0) := by
      rw [show (fderiv ℝ (fun y : CurvatureCoordinateSpace4 =>
          A1 i j * y i) x) = A1 i j • ContinuousLinearMap.proj i by
        simpa using ((hasFDerivAt_apply i x).const_mul (A1 i j)).fderiv]
      simp [curvatureCoordinateDirection, eq_comm]
    simp_rw [hterm]
    simp
  · intro i _
    fun_prop

private theorem scalarFieldCoordinateFDeriv_quadraticPotentialSum
    (A2 : OneFormSecondDerivative4)
    (x : CurvatureCoordinateSpace4) (r j : Fin 4) :
    scalarFieldCoordinateFDeriv
      (fun y => ∑ k : Fin 4, ∑ i : Fin 4,
        A2 k i j * y k * y i) x r =
      ∑ k : Fin 4, ∑ i : Fin 4, A2 k i j *
        ((if r = k then 1 else 0) * x i +
          x k * (if r = i then 1 else 0)) := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      ∑ k : Fin 4, ∑ i : Fin 4, A2 k i j * y k * y i) =
    ∑ k : Fin 4, ∑ i : Fin 4,
      fun y => A2 k i j * y k * y i by rfl]
  rw [fderiv_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [fderiv_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (fun y : CurvatureCoordinateSpace4 =>
          A2 k i j * y k * y i) =
        (fun _ => A2 k i j) * (fun y => y k) * (fun y => y i) by rfl]
      rw [fderiv_mul, fderiv_mul]
      rw [(hasFDerivAt_apply k x).fderiv,
        (hasFDerivAt_apply i x).fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul,
        ContinuousLinearMap.proj_apply]
      by_cases hrk : r = k <;> by_cases hri : r = i <;>
        by_cases hki : k = i <;>
        simp [curvatureCoordinateDirection, eq_comm, hrk, hri, hki] <;>
          ring_nf
      all_goals fun_prop
    · intro i _
      fun_prop
  · intro k _
    apply DifferentiableAt.sum
    intro i _
    fun_prop

private theorem half_quadraticPotentialDerivative_of_symm
    (A2 : OneFormSecondDerivative4)
    (hA2 : ∀ k i j, A2 k i j = A2 i k j)
    (x : CurvatureCoordinateSpace4) (r j : Fin 4) :
    (1 / 2 : ℝ) *
      (∑ k : Fin 4, ∑ i : Fin 4, A2 k i j *
        ((if r = k then 1 else 0) * x i +
          x k * (if r = i then 1 else 0))) =
      ∑ i : Fin 4, A2 r i j * x i := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [eq_comm]
  rw [show (∑ k : Fin 4, A2 k r j * x k) =
      ∑ k : Fin 4, A2 r k j * x k by
    apply Finset.sum_congr rfl
    intro k _
    rw [hA2]]
  ring_nf

/-- Exact first derivative of the quadratic one-form field. -/
theorem scalarFieldCoordinateFDeriv_quadraticPotentialCoordinateField4
    (A1 : Matrix4) (A2 : OneFormSecondDerivative4)
    (hA2 : ∀ k i j, A2 k i j = A2 i k j)
    (x : CurvatureCoordinateSpace4) (r j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => quadraticPotentialCoordinateField4 A1 A2 y j) x r =
      A1 r j + ∑ i : Fin 4, A2 r i j * x i := by
  unfold quadraticPotentialCoordinateField4 scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      (∑ i : Fin 4, A1 i j * y i) +
        (1 / 2 : ℝ) *
          (∑ k : Fin 4, ∑ i : Fin 4, A2 k i j * y k * y i)) =
    (fun y => ∑ i : Fin 4, A1 i j * y i) +
      (fun y => (1 / 2 : ℝ) *
        (∑ k : Fin 4, ∑ i : Fin 4,
          A2 k i j * y k * y i)) by rfl]
  rw [fderiv_add]
  simp only [add_apply]
  change scalarFieldCoordinateFDeriv
      (fun y => ∑ i : Fin 4, A1 i j * y i) x r +
    scalarFieldCoordinateFDeriv
      (fun y => (1 / 2 : ℝ) *
        (∑ k : Fin 4, ∑ i : Fin 4,
          A2 k i j * y k * y i)) x r = _
  rw [scalarFieldCoordinateFDeriv_linearPotentialSum]
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      (1 / 2 : ℝ) *
        (∑ k : Fin 4, ∑ i : Fin 4, A2 k i j * y k * y i)) =
    (fun _ => (1 / 2 : ℝ)) *
      (fun y => ∑ k : Fin 4, ∑ i : Fin 4,
        A2 k i j * y k * y i) by rfl]
  rw [fderiv_mul]
  rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 =>
      (1 / 2 : ℝ)) x = 0 by simp]
  simp only [smul_apply, smul_eq_mul, smul_zero, add_zero]
  change A1 r j + (1 / 2 : ℝ) *
      scalarFieldCoordinateFDeriv
        (fun y => ∑ k : Fin 4, ∑ i : Fin 4,
          A2 k i j * y k * y i) x r = _
  rw [scalarFieldCoordinateFDeriv_quadraticPotentialSum,
    half_quadraticPotentialDerivative_of_symm A2 hA2]
  all_goals fun_prop

/-- The genuine first derivative at the origin is the prescribed first
potential jet. -/
theorem quadraticPotentialCoordinateField4_firstJet_zero
    (A1 : Matrix4) (A2 : OneFormSecondDerivative4)
    (hA2 : ∀ k i j, A2 k i j = A2 i k j) (r j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => quadraticPotentialCoordinateField4 A1 A2 y j) 0 r =
      A1 r j := by
  rw [scalarFieldCoordinateFDeriv_quadraticPotentialCoordinateField4
    A1 A2 hA2]
  simp

/-- The genuine nested second derivative at the origin is the prescribed
symmetric second potential jet. -/
theorem quadraticPotentialCoordinateField4_secondJet_zero
    (A1 : Matrix4) (A2 : OneFormSecondDerivative4)
    (hA2 : ∀ k i j, A2 k i j = A2 i k j) (r s j : Fin 4) :
    scalarFieldCoordinateFDeriv
      (fun y => scalarFieldCoordinateFDeriv
        (fun x => quadraticPotentialCoordinateField4 A1 A2 x j) y s)
      0 r = A2 r s j := by
  rw [show (fun y => scalarFieldCoordinateFDeriv
      (fun x => quadraticPotentialCoordinateField4 A1 A2 x j) y s) =
    fun y => A1 s j + ∑ i : Fin 4, A2 s i j * y i by
      funext y
      exact scalarFieldCoordinateFDeriv_quadraticPotentialCoordinateField4
        A1 A2 hA2 y s j]
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      A1 s j + ∑ i : Fin 4, A2 s i j * y i) =
    (fun _ => A1 s j) +
      (fun y => ∑ i : Fin 4, A2 s i j * y i) by rfl]
  rw [fderiv_add]
  simp only [add_apply]
  rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 => A1 s j) 0 = 0 by
    simp]
  simp only [zero_apply, zero_add]
  change scalarFieldCoordinateFDeriv
      (fun y => ∑ i : Fin 4, A2 s i j * y i) 0 r = A2 r s j
  rw [scalarFieldCoordinateFDeriv_linearPotentialSum]
  exact hA2 s r j
  all_goals fun_prop

/-- Actual quadratic physical potential for the active ambiguity family. -/
noncomputable def activeAmbiguityPhysicalRadialPotentialPolynomial
    (a : ℝ) : CurvatureCoordinateSpace4 → OneForm4 :=
  quadraticPotentialCoordinateField4
    activeAmbiguityPhysicalRadialPotentialFirstJet
    (activeAmbiguityPhysicalRadialPotentialSecondJet a)

/-- Every active-family realizing potential is smooth. -/
theorem contDiff_activeAmbiguityPhysicalRadialPotentialPolynomial
    (a : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (activeAmbiguityPhysicalRadialPotentialPolynomial a) := by
  exact contDiff_quadraticPotentialCoordinateField4 _ _ n

/-- **Actual active-family potential two-jet realization.**  The displayed
quadratic one-form is an actual field whose value and genuine first/second
coordinate derivatives at the marked point are exactly the compatible
radial-gauge coefficient jets. -/
theorem activeAmbiguityPhysicalRadialPotentialPolynomial_realizes
    (a : ℝ) :
    activeAmbiguityPhysicalRadialPotentialPolynomial a 0 = 0 ∧
    (∀ r j,
      scalarFieldCoordinateFDeriv
          (fun y => activeAmbiguityPhysicalRadialPotentialPolynomial a y j)
          0 r =
        activeAmbiguityPhysicalRadialPotentialFirstJet r j) ∧
    (∀ r s j,
      scalarFieldCoordinateFDeriv
        (fun y => scalarFieldCoordinateFDeriv
          (fun x => activeAmbiguityPhysicalRadialPotentialPolynomial a x j)
          y s) 0 r =
        activeAmbiguityPhysicalRadialPotentialSecondJet a r s j) := by
  have hsymm : ∀ k i j,
      activeAmbiguityPhysicalRadialPotentialSecondJet a k i j =
        activeAmbiguityPhysicalRadialPotentialSecondJet a i k j :=
    radialGaugePotentialSecondJet4_derivative_symm _
  refine ⟨quadraticPotentialCoordinateField4_zero _ _, ?_, ?_⟩
  · intro r j
    exact quadraticPotentialCoordinateField4_firstJet_zero _ _ hsymm r j
  · intro r s j
    exact quadraticPotentialCoordinateField4_secondJet_zero _ _ hsymm r s j

/-- The actual polynomial potential realizes the physical Maxwell value and
first jet through its literal curl and differentiated curl at the origin.
This is the function-level counterpart of
`activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes`. -/
theorem activeAmbiguityPhysicalRadialPotentialPolynomial_curl_realizes
    (a : ℝ) :
    (∀ i j,
      scalarFieldCoordinateFDeriv
          (fun y => activeAmbiguityPhysicalRadialPotentialPolynomial a y j)
          0 i -
        scalarFieldCoordinateFDeriv
          (fun y => activeAmbiguityPhysicalRadialPotentialPolynomial a y i)
          0 j =
        activeAmbiguityPhysicalMaxwellField i j) ∧
    (∀ k i j,
      scalarFieldCoordinateFDeriv
          (fun y => scalarFieldCoordinateFDeriv
            (fun x => activeAmbiguityPhysicalRadialPotentialPolynomial a x j)
            y i) 0 k -
        scalarFieldCoordinateFDeriv
          (fun y => scalarFieldCoordinateFDeriv
            (fun x => activeAmbiguityPhysicalRadialPotentialPolynomial a x i)
            y j) 0 k =
        activeAmbiguityPhysicalMaxwellFirstJet a k i j) := by
  rcases activeAmbiguityPhysicalRadialPotentialPolynomial_realizes a with
    ⟨_, hfirst, hsecond⟩
  rcases activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes a with
    ⟨hcurl, _, hcurlFirst⟩
  constructor
  · intro i j
    rw [hfirst i j, hfirst j i]
    exact hcurl i j
  · intro k i j
    rw [hsecond k i j, hsecond k j i]
    exact hcurlFirst k i j

end RainichKaluza
