import RainichKaluza.ThirdOrderMatterJetAmbiguity
import RainichKaluza.PhaseIIIRescaledSeedRealization

/-!
# Smooth polynomial realization of formal metric three-jets

Every symmetric coordinate metric two/three-jet used by the active
ambiguity is realized here by one explicit cubic polynomial matrix field.
After conversion to a continuous bilinear form this is a genuine smooth
metric germ.  The construction recovers the prescribed value and first
three coordinate derivatives at the origin.  It therefore removes the
purely formal/Borel-realization gap for the metric itself.

This does not assert that the polynomial germ satisfies the EMD equations
away from the origin, nor does it provide local EMD solution germs.  What it
does prove is that the already-verified point Einstein equation and first
prolongation are attached to the actual derivatives of a smooth Lorentzian
metric germ, rather than to unrelated arrays.
-/

namespace RainichKaluza

open scoped Matrix Topology ContDiff

/-- Cubic Taylor polynomial with prescribed value `g0`, vanishing first
jet, second jet `g2`, and third jet `g3`. -/
noncomputable def cubicMetricTaylorMatrixField4
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (x : CurvatureCoordinateSpace4) : Matrix4 :=
  fun i j => g0 i j +
    (1 / 2 : ℝ) *
      (∑ r : Fin 4, ∑ s : Fin 4, g2 r s i j * x r * x s) +
    (1 / 6 : ℝ) *
      (∑ r : Fin 4, ∑ s : Fin 4, ∑ t : Fin 4,
        g3 r s t i j * x r * x s * x t)

/-- The actual continuous-bilinear metric field associated to the cubic
Taylor matrix. -/
noncomputable def cubicMetricTaylorField4
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4)) :
    CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4 :=
  fun x => matrixContinuousBilinForm4
    (cubicMetricTaylorMatrixField4 g0 g2 g3 x)

/-- Coordinate matrix extraction is a left inverse to the finite-dimensional
matrix-to-bilinear conversion. -/
@[simp] theorem coordinateMetricMatrixField4_cubicMetricTaylorField4
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (x : CurvatureCoordinateSpace4) :
    coordinateMetricMatrixField4
        (cubicMetricTaylorField4 g0 g2 g3) x =
      cubicMetricTaylorMatrixField4 g0 g2 g3 x := by
  ext i j
  exact matrixContinuousBilinForm4_coordinateDirection _ i j

/-- The cubic Taylor field has the prescribed value at the origin. -/
@[simp] theorem cubicMetricTaylorMatrixField4_zero
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4)) :
    cubicMetricTaylorMatrixField4 g0 g2 g3 0 = g0 := by
  ext i j
  simp [cubicMetricTaylorMatrixField4]

private theorem scalarFieldCoordinateFDeriv_quadraticSum
    (g2 : CoordinateMetricJet2 (Fin 4))
    (x : CurvatureCoordinateSpace4) (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
      (fun y => ∑ a : Fin 4, ∑ b : Fin 4,
        g2 a b i j * y a * y b) x r =
      ∑ a : Fin 4, ∑ b : Fin 4,
        g2 a b i j *
          ((if r = a then 1 else 0) * x b +
            x a * (if r = b then 1 else 0)) := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      ∑ a : Fin 4, ∑ b : Fin 4, g2 a b i j * y a * y b) =
    ∑ a : Fin 4, ∑ b : Fin 4,
      fun y => g2 a b i j * y a * y b by rfl]
  rw [fderiv_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [fderiv_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro b _
      rw [show (fun y : CurvatureCoordinateSpace4 =>
          g2 a b i j * y a * y b) =
        (fun _ => g2 a b i j) * (fun y => y a) * (fun y => y b) by rfl]
      rw [fderiv_mul, fderiv_mul]
      rw [(hasFDerivAt_apply a x).fderiv,
        (hasFDerivAt_apply b x).fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul,
        ContinuousLinearMap.proj_apply]
      by_cases hra : r = a <;> by_cases hrb : r = b <;>
        by_cases hab : a = b <;>
        simp [curvatureCoordinateDirection, eq_comm, hra, hrb, hab] <;>
          ring_nf
      all_goals fun_prop
    · intro b _
      fun_prop
  · intro a _
    apply DifferentiableAt.sum
    intro b _
    fun_prop

private theorem half_quadraticDerivative_of_symm
    (g2 : CoordinateMetricJet2 (Fin 4))
    (h2 : ∀ a b i j, g2 a b i j = g2 b a i j)
    (x : CurvatureCoordinateSpace4) (r i j : Fin 4) :
    (1 / 2 : ℝ) *
      (∑ a : Fin 4, ∑ b : Fin 4,
        g2 a b i j *
          ((if r = a then 1 else 0) * x b +
            x a * (if r = b then 1 else 0))) =
      ∑ s : Fin 4, g2 r s i j * x s := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [eq_comm]
  rw [show (∑ a : Fin 4, g2 a r i j * x a) =
      ∑ a : Fin 4, g2 r a i j * x a by
    apply Finset.sum_congr rfl
    intro a _
    rw [h2]]
  ring_nf

private theorem scalarFieldCoordinateFDeriv_linearSum
    (c : OneForm4) (x : CurvatureCoordinateSpace4) (r : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => ∑ t : Fin 4, c t * y t) x r = c r := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      ∑ t : Fin 4, c t * y t) =
    ∑ t : Fin 4, fun y => c t * y t by rfl]
  rw [fderiv_sum]
  · simp only [sum_apply]
    have hterm (t : Fin 4) :
        (fderiv ℝ (fun y : CurvatureCoordinateSpace4 => c t * y t) x)
            (curvatureCoordinateDirection r) =
          c t * (if r = t then 1 else 0) := by
      rw [show (fderiv ℝ (fun y : CurvatureCoordinateSpace4 =>
          c t * y t) x) = c t • ContinuousLinearMap.proj t by
        simpa using ((hasFDerivAt_apply t x).const_mul (c t)).fderiv]
      simp [curvatureCoordinateDirection, eq_comm]
    simp_rw [hterm]
    simp
  · intro t _
    fun_prop

private theorem scalarFieldCoordinateFDeriv_cubicSum
    (g3 : CoordinateMetricJet3 (Fin 4))
    (x : CurvatureCoordinateSpace4) (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
      (fun y => ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        g3 a b c i j * y a * y b * y c) x r =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        g3 a b c i j *
          ((if r = a then 1 else 0) * x b * x c +
            x a * (if r = b then 1 else 0) * x c +
            x a * x b * (if r = c then 1 else 0)) := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        g3 a b c i j * y a * y b * y c) =
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      fun y => g3 a b c i j * y a * y b * y c by rfl]
  rw [fderiv_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [fderiv_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro b _
      rw [fderiv_sum]
      · simp only [sum_apply]
        apply Finset.sum_congr rfl
        intro c _
        rw [show (fun y : CurvatureCoordinateSpace4 =>
            g3 a b c i j * y a * y b * y c) =
          (((fun _ => g3 a b c i j) * (fun y => y a)) *
            (fun y => y b)) * (fun y => y c) by rfl]
        rw [fderiv_mul, fderiv_mul, fderiv_mul]
        rw [(hasFDerivAt_apply a x).fderiv,
          (hasFDerivAt_apply b x).fderiv,
          (hasFDerivAt_apply c x).fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul,
          ContinuousLinearMap.proj_apply]
        by_cases hra : r = a <;> by_cases hrb : r = b <;>
          by_cases hrc : r = c <;> by_cases hab : a = b <;>
          by_cases hac : a = c <;> by_cases hbc : b = c <;>
          simp [curvatureCoordinateDirection, eq_comm, hra, hrb, hrc,
            hab, hac, hbc] <;> ring_nf
        all_goals fun_prop
      · intro c _
        fun_prop
    · intro b _
      apply DifferentiableAt.sum
      intro c _
      fun_prop
  · intro a _
    apply DifferentiableAt.sum
    intro b _
    apply DifferentiableAt.sum
    intro c _
    fun_prop

private theorem sixth_cubicDerivative_of_symm
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h31 : ∀ a b c i j, g3 a b c i j = g3 b a c i j)
    (h32 : ∀ a b c i j, g3 a b c i j = g3 a c b i j)
    (x : CurvatureCoordinateSpace4) (r i j : Fin 4) :
    (1 / 6 : ℝ) *
      (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        g3 a b c i j *
          ((if r = a then 1 else 0) * x b * x c +
            x a * (if r = b then 1 else 0) * x c +
            x a * x b * (if r = c then 1 else 0))) =
      (1 / 2 : ℝ) * ∑ b : Fin 4, ∑ c : Fin 4,
        g3 r b c i j * x b * x c := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp
  have hsecond :
      (∑ a : Fin 4, ∑ c : Fin 4, g3 a r c i j * x a * x c) =
        ∑ a : Fin 4, ∑ c : Fin 4, g3 r a c i j * x a * x c := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [h31]
  have hthird :
      (∑ a : Fin 4, ∑ b : Fin 4, g3 a b r i j * x a * x b) =
        ∑ a : Fin 4, ∑ b : Fin 4, g3 r a b i j * x a * x b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [h32 a b r, h31 a r b]
  rw [show (∑ a : Fin 4, ∑ c : Fin 4,
        g3 a r c i j * (x a * x c)) =
      ∑ a : Fin 4, ∑ c : Fin 4,
        g3 r a c i j * (x a * x c) by
    simpa [mul_assoc] using hsecond]
  rw [show (∑ a : Fin 4, ∑ b : Fin 4,
        g3 a b r i j * (x a * x b)) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        g3 r a b i j * (x a * x b) by
    simpa [mul_assoc] using hthird]
  ring_nf

/-- Exact first derivative of the cubic Taylor matrix under the commuting
derivative-slot symmetries. -/
theorem scalarFieldCoordinateFDeriv_cubicMetricTaylorMatrixField4
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h2 : ∀ a b i j, g2 a b i j = g2 b a i j)
    (h31 : ∀ a b c i j, g3 a b c i j = g3 b a c i j)
    (h32 : ∀ a b c i j, g3 a b c i j = g3 a c b i j)
    (x : CurvatureCoordinateSpace4) (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y => cubicMetricTaylorMatrixField4 g0 g2 g3 y i j) x r =
      ∑ s : Fin 4, g2 r s i j * x s +
        (1 / 2 : ℝ) * ∑ s : Fin 4, ∑ t : Fin 4,
          g3 r s t i j * x s * x t := by
  unfold cubicMetricTaylorMatrixField4
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
        g0 i j +
          (1 / 2 : ℝ) *
            (∑ a : Fin 4, ∑ b : Fin 4, g2 a b i j * y a * y b) +
          (1 / 6 : ℝ) *
            (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
              g3 a b c i j * y a * y b * y c)) =
      (fun _ => g0 i j) +
        (fun y => (1 / 2 : ℝ) *
          (∑ a : Fin 4, ∑ b : Fin 4, g2 a b i j * y a * y b)) +
        (fun y => (1 / 6 : ℝ) *
          (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
            g3 a b c i j * y a * y b * y c)) by rfl]
  rw [fderiv_add, fderiv_add]
  simp only [add_apply]
  rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 => g0 i j) x = 0 by
    simp]
  simp only [zero_apply, zero_add]
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      (1 / 2 : ℝ) *
        (∑ a : Fin 4, ∑ b : Fin 4, g2 a b i j * y a * y b)) =
      (fun _ => (1 / 2 : ℝ)) *
        (fun y => ∑ a : Fin 4, ∑ b : Fin 4,
          g2 a b i j * y a * y b) by rfl]
  rw [fderiv_mul]
  rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 =>
      (1 / 2 : ℝ)) x = 0 by
    simp]
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      (1 / 6 : ℝ) *
        (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          g3 a b c i j * y a * y b * y c)) =
      (fun _ => (1 / 6 : ℝ)) *
        (fun y => ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          g3 a b c i j * y a * y b * y c) by rfl]
  rw [fderiv_mul]
  rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 =>
      (1 / 6 : ℝ)) x = 0 by
    simp]
  simp only [smul_apply, smul_eq_mul, smul_zero, add_zero]
  change (1 / 2 : ℝ) * scalarFieldCoordinateFDeriv
        (fun y => ∑ a : Fin 4, ∑ b : Fin 4,
          g2 a b i j * y a * y b) x r +
      (1 / 6 : ℝ) * scalarFieldCoordinateFDeriv
        (fun y => ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
          g3 a b c i j * y a * y b * y c) x r = _
  rw [scalarFieldCoordinateFDeriv_quadraticSum,
    scalarFieldCoordinateFDeriv_cubicSum,
    half_quadraticDerivative_of_symm g2 h2,
    sixth_cubicDerivative_of_symm g3 h31 h32]
  all_goals fun_prop

/-- The actual first metric jet at the origin vanishes. -/
theorem actualCoordinateMetricJet1Field4_cubicMetricTaylorField4_zero
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h2 : ∀ a b i j, g2 a b i j = g2 b a i j)
    (h31 : ∀ a b c i j, g3 a b c i j = g3 b a c i j)
    (h32 : ∀ a b c i j, g3 a b c i j = g3 a c b i j) :
    actualCoordinateMetricJet1Field4
        (cubicMetricTaylorField4 g0 g2 g3) 0 = 0 := by
  funext r i j
  unfold actualCoordinateMetricJet1Field4
  rw [show (fun y => coordinateMetricMatrixField4
      (cubicMetricTaylorField4 g0 g2 g3) y i j) =
    fun y => cubicMetricTaylorMatrixField4 g0 g2 g3 y i j by
      funext y
      rw [coordinateMetricMatrixField4_cubicMetricTaylorField4]]
  rw [scalarFieldCoordinateFDeriv_cubicMetricTaylorMatrixField4
    g0 g2 g3 h2 h31 h32]
  simp

/-- The actual second metric jet at the origin is the prescribed symmetric
array. -/
theorem actualCoordinateMetricJet2Field4_cubicMetricTaylorField4_zero
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h2 : ∀ a b i j, g2 a b i j = g2 b a i j)
    (h31 : ∀ a b c i j, g3 a b c i j = g3 b a c i j)
    (h32 : ∀ a b c i j, g3 a b c i j = g3 a c b i j) :
    actualCoordinateMetricJet2Field4
        (cubicMetricTaylorField4 g0 g2 g3) 0 = g2 := by
  funext r s i j
  unfold actualCoordinateMetricJet2Field4 actualCoordinateMetricJet1Field4
  simp only [coordinateMetricMatrixField4_cubicMetricTaylorField4]
  rw [show (fun y => scalarFieldCoordinateFDeriv
      (fun x => cubicMetricTaylorMatrixField4 g0 g2 g3 x i j) y s) =
    fun y => ∑ t : Fin 4, g2 s t i j * y t +
      (1 / 2 : ℝ) * ∑ t : Fin 4, ∑ u : Fin 4,
        g3 s t u i j * y t * y u by
    funext y
    exact scalarFieldCoordinateFDeriv_cubicMetricTaylorMatrixField4
      g0 g2 g3 h2 h31 h32 y s i j]
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      ∑ t : Fin 4, g2 s t i j * y t +
        (1 / 2 : ℝ) * ∑ t : Fin 4, ∑ u : Fin 4,
          g3 s t u i j * y t * y u) =
    (fun y => ∑ t : Fin 4, g2 s t i j * y t) +
      (fun y => (1 / 2 : ℝ) * ∑ t : Fin 4, ∑ u : Fin 4,
        g3 s t u i j * y t * y u) by rfl]
  rw [fderiv_add (by fun_prop) (by fun_prop)]
  simp only [add_apply]
  have hlinear :
      (fderiv ℝ (fun y : CurvatureCoordinateSpace4 =>
        ∑ t : Fin 4, g2 s t i j * y t) 0)
          (curvatureCoordinateDirection r) = g2 s r i j := by
    exact scalarFieldCoordinateFDeriv_linearSum
      (fun t => g2 s t i j) 0 r
  rw [hlinear]
  have hquad :
      (fderiv ℝ (fun y : CurvatureCoordinateSpace4 =>
        (1 / 2 : ℝ) * ∑ t : Fin 4, ∑ u : Fin 4,
          g3 s t u i j * y t * y u) 0)
          (curvatureCoordinateDirection r) = 0 := by
    rw [show (fun y : CurvatureCoordinateSpace4 =>
        (1 / 2 : ℝ) * ∑ t : Fin 4, ∑ u : Fin 4,
          g3 s t u i j * y t * y u) =
      (fun _ => (1 / 2 : ℝ)) *
        (fun y => ∑ t : Fin 4, ∑ u : Fin 4,
          g3 s t u i j * y t * y u) by rfl]
    rw [fderiv_mul]
    rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 =>
        (1 / 2 : ℝ)) 0 = 0 by
      simp]
    simp only [smul_zero, add_zero, smul_apply, smul_eq_mul]
    change (1 / 2 : ℝ) * scalarFieldCoordinateFDeriv
      (fun y => ∑ t : Fin 4, ∑ u : Fin 4,
        g3 s t u i j * y t * y u) 0 r = 0
    rw [show scalarFieldCoordinateFDeriv
        (fun y => ∑ t : Fin 4, ∑ u : Fin 4,
          g3 s t u i j * y t * y u) 0 r = 0 by
      rw [scalarFieldCoordinateFDeriv_quadraticSum]
      simp]
    · norm_num
    · fun_prop
    · rw [show (fun y : CurvatureCoordinateSpace4 =>
          ∑ t : Fin 4, ∑ u : Fin 4, g3 s t u i j * y t * y u) =
        ∑ t : Fin 4, ∑ u : Fin 4,
          fun y => g3 s t u i j * y t * y u by rfl]
      apply DifferentiableAt.sum
      intro t _
      apply DifferentiableAt.sum
      intro u _
      fun_prop
  rw [hquad, add_zero, h2 s r]

/-- Actual third coordinate jet obtained by differentiating the actual
second jet field. -/
noncomputable def actualCoordinateMetricJet3Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : CoordinateMetricJet3 (Fin 4) :=
  fun r s t i j => scalarFieldCoordinateFDeriv
    (fun y => scalarFieldCoordinateFDeriv
      (fun x => scalarFieldCoordinateFDeriv
        (fun w => coordinateMetricMatrixField4 g w i j) x t) y s) z r

/-- **Smooth metric-three-jet realization.** The actual third derivative of
the cubic metric germ is the prescribed fully symmetric third jet. -/
theorem actualCoordinateMetricJet3Field4_cubicMetricTaylorField4_zero
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h2 : ∀ a b i j, g2 a b i j = g2 b a i j)
    (h31 : ∀ a b c i j, g3 a b c i j = g3 b a c i j)
    (h32 : ∀ a b c i j, g3 a b c i j = g3 a c b i j) :
    actualCoordinateMetricJet3Field4
        (cubicMetricTaylorField4 g0 g2 g3) 0 = g3 := by
  funext r s t i j
  unfold actualCoordinateMetricJet3Field4
  rw [show (fun w => coordinateMetricMatrixField4
      (cubicMetricTaylorField4 g0 g2 g3) w i j) =
    fun w => cubicMetricTaylorMatrixField4 g0 g2 g3 w i j by
      funext w
      rw [coordinateMetricMatrixField4_cubicMetricTaylorField4]]
  rw [show (fun y => scalarFieldCoordinateFDeriv
      (fun x => scalarFieldCoordinateFDeriv
        (fun w => cubicMetricTaylorMatrixField4 g0 g2 g3 w i j) x t) y s) =
    fun y => g2 t s i j + ∑ u : Fin 4, g3 t s u i j * y u by
    funext y
    rw [show (fun x => scalarFieldCoordinateFDeriv
        (fun w => cubicMetricTaylorMatrixField4 g0 g2 g3 w i j) x t) =
      fun x => ∑ u : Fin 4, g2 t u i j * x u +
        (1 / 2 : ℝ) * ∑ u : Fin 4, ∑ v : Fin 4,
          g3 t u v i j * x u * x v by
      funext x
      exact scalarFieldCoordinateFDeriv_cubicMetricTaylorMatrixField4
        g0 g2 g3 h2 h31 h32 x t i j]
    rw [show (fun x : CurvatureCoordinateSpace4 =>
        ∑ u : Fin 4, g2 t u i j * x u +
          (1 / 2 : ℝ) * ∑ u : Fin 4, ∑ v : Fin 4,
            g3 t u v i j * x u * x v) =
      (fun x => ∑ u : Fin 4, g2 t u i j * x u) +
        (fun x => (1 / 2 : ℝ) * ∑ u : Fin 4, ∑ v : Fin 4,
          g3 t u v i j * x u * x v) by rfl]
    unfold scalarFieldCoordinateFDeriv
    rw [fderiv_add (by fun_prop) (by fun_prop)]
    simp only [add_apply]
    have hlin :
        (fderiv ℝ (fun x : CurvatureCoordinateSpace4 =>
          ∑ u : Fin 4, g2 t u i j * x u) y)
            (curvatureCoordinateDirection s) = g2 t s i j := by
      exact scalarFieldCoordinateFDeriv_linearSum
        (fun u => g2 t u i j) y s
    rw [hlin]
    rw [show (fun x : CurvatureCoordinateSpace4 =>
        (1 / 2 : ℝ) * ∑ u : Fin 4, ∑ v : Fin 4,
          g3 t u v i j * x u * x v) =
      (fun _ => (1 / 2 : ℝ)) *
        (fun x => ∑ u : Fin 4, ∑ v : Fin 4,
          g3 t u v i j * x u * x v) by rfl]
    rw [fderiv_mul]
    rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 =>
        (1 / 2 : ℝ)) y = 0 by
      simp]
    simp only [smul_zero, add_zero, smul_apply, smul_eq_mul]
    change g2 t s i j + (1 / 2 : ℝ) *
      scalarFieldCoordinateFDeriv
        (fun x => ∑ u : Fin 4, ∑ v : Fin 4,
          g3 t u v i j * x u * x v) y s = _
    rw [scalarFieldCoordinateFDeriv_quadraticSum,
      half_quadraticDerivative_of_symm
        (fun u v a b => g3 t u v a b) (fun u v a b => h32 t u v a b)]
    all_goals fun_prop]
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y : CurvatureCoordinateSpace4 =>
      g2 t s i j + ∑ u : Fin 4, g3 t s u i j * y u) =
    (fun _ => g2 t s i j) +
      (fun y => ∑ u : Fin 4, g3 t s u i j * y u) by rfl]
  rw [fderiv_add (by fun_prop) (by fun_prop)]
  simp only [add_apply]
  rw [show fderiv ℝ (fun _ : CurvatureCoordinateSpace4 =>
      g2 t s i j) 0 = 0 by
    simp]
  simp only [zero_apply, zero_add]
  change scalarFieldCoordinateFDeriv
      (fun y => ∑ u : Fin 4, g3 t s u i j * y u) 0 r = _
  rw [scalarFieldCoordinateFDeriv_linearSum]
  rw [h32 t s r, h31 t r s]
  exact h32 r t s i j

/-- The active ambiguity's formal metric three-jet is realized by one
genuine smooth cubic metric germ. -/
noncomputable def activeAmbiguityPolynomialMetricGerm :
    CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4 :=
  cubicMetricTaylorField4 minkowskiMetric
    activeAmbiguityFormalMetricJet2 activeAmbiguityFormalMetricJet3

/-- The active polynomial germ has the exact stored metric value and first
three jets at the origin. -/
theorem activeAmbiguityPolynomialMetricGerm_realizes_threeJet :
    coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm 0 =
        minkowskiMetric ∧
      actualCoordinateMetricJet1Field4 activeAmbiguityPolynomialMetricGerm 0 = 0 ∧
      actualCoordinateMetricJet2Field4 activeAmbiguityPolynomialMetricGerm 0 =
        activeAmbiguityFormalMetricJet2 ∧
      actualCoordinateMetricJet3Field4 activeAmbiguityPolynomialMetricGerm 0 =
        activeAmbiguityFormalMetricJet3 := by
  have h2 : ∀ a b i j,
      activeAmbiguityFormalMetricJet2 a b i j =
        activeAmbiguityFormalMetricJet2 b a i j := by
    intro a b i j
    exact normalCoordinateMetricJet2OfRicci_deriv_symm _
      activeAmbiguityCovariantRicciSource_transpose a b i j
  have h31 : ∀ a b c i j,
      activeAmbiguityFormalMetricJet3 a b c i j =
        activeAmbiguityFormalMetricJet3 b a c i j := by
    intro a b c i j
    exact (activeAmbiguityFormalMetricJet3_symmetries a b c i j).1
  have h32 : ∀ a b c i j,
      activeAmbiguityFormalMetricJet3 a b c i j =
        activeAmbiguityFormalMetricJet3 a c b i j := by
    intro a b c i j
    exact (activeAmbiguityFormalMetricJet3_symmetries a b c i j).2.1
  refine ⟨?_,
    actualCoordinateMetricJet1Field4_cubicMetricTaylorField4_zero
      _ _ _ h2 h31 h32,
    actualCoordinateMetricJet2Field4_cubicMetricTaylorField4_zero
      _ _ _ h2 h31 h32,
    actualCoordinateMetricJet3Field4_cubicMetricTaylorField4_zero
      _ _ _ h2 h31 h32⟩
  simp [activeAmbiguityPolynomialMetricGerm]

end RainichKaluza
