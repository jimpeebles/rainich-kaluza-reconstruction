import RainichKaluza.PolynomialMetricJetRealization

/-!
# A genuine Lorentz-sign neighborhood for the active polynomial metric germ

The active ambiguity's cubic Taylor field was previously shown to realize the
stored metric three-jet at the origin.  This file records the complementary
local-geometric fact needed to regard that field as an honest metric germ:

* the matrix field, and hence the continuous-bilinear-form field, depends
  continuously on the base point;
* every matrix in the field is symmetric;
* its determinant is negative on an explicit open neighborhood of the
  origin, because it equals the Minkowski determinant `-1` at the origin;
* consequently the associated algebraic bilinear form is nondegenerate on
  that neighborhood.

Negative determinant is the determinant-sign part of the Lorentzian branch.
The statements below deliberately do not identify it, by itself, with an
abstract index-one signature predicate.
-/

namespace RainichKaluza

open Set
open LinearMap (BilinForm)
open scoped Matrix Topology

/-- The cubic Taylor matrix field is continuous as a matrix-valued map. -/
theorem continuous_cubicMetricTaylorMatrixField4
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4)) :
    Continuous (cubicMetricTaylorMatrixField4 g0 g2 g3) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [cubicMetricTaylorMatrixField4]
  fun_prop

/-- Matrix-to-continuous-bilinear-form conversion upgrades entrywise
polynomial continuity to continuity of the actual metric field. -/
theorem continuous_cubicMetricTaylorField4
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4)) :
    Continuous (cubicMetricTaylorField4 g0 g2 g3) := by
  change Continuous
    (matrixContinuousBilinForm4CLM ∘
      cubicMetricTaylorMatrixField4 g0 g2 g3)
  exact matrixContinuousBilinForm4CLM.continuous.comp
    (continuous_cubicMetricTaylorMatrixField4 g0 g2 g3)

/-- Symmetry in the metric slots of the Taylor coefficients makes the whole
cubic Taylor matrix symmetric at every point. -/
theorem cubicMetricTaylorMatrixField4_transpose_eq_self
    (g0 : Matrix4)
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4))
    (h0 : g0.transpose = g0)
    (h2 : ∀ r s i j, g2 r s i j = g2 r s j i)
    (h3 : ∀ r s t i j, g3 r s t i j = g3 r s t j i)
    (x : CurvatureCoordinateSpace4) :
    (cubicMetricTaylorMatrixField4 g0 g2 g3 x).transpose =
      cubicMetricTaylorMatrixField4 g0 g2 g3 x := by
  ext i j
  have h0ij := congrArg (fun M : Matrix4 => M i j) h0
  simp only [Matrix.transpose_apply] at h0ij ⊢
  simp only [cubicMetricTaylorMatrixField4]
  have hquadratic :
      (∑ r : Fin 4, ∑ s : Fin 4, g2 r s j i * x r * x s) =
        ∑ r : Fin 4, ∑ s : Fin 4, g2 r s i j * x r * x s := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [h2 r s j i]
  have hcubic :
      (∑ r : Fin 4, ∑ s : Fin 4, ∑ t : Fin 4,
          g3 r s t j i * x r * x s * x t) =
        ∑ r : Fin 4, ∑ s : Fin 4, ∑ t : Fin 4,
          g3 r s t i j * x r * x s * x t := by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [h3 r s t j i]
  rw [h0ij, hquadratic, hcubic]

/-- The active polynomial metric field is continuous in the normed space of
continuous bilinear forms. -/
theorem continuous_activeAmbiguityPolynomialMetricGerm :
    Continuous activeAmbiguityPolynomialMetricGerm := by
  exact continuous_cubicMetricTaylorField4 _ _ _

/-- The active polynomial metric matrix is symmetric at every point, not
merely to finite order at the origin. -/
theorem activeAmbiguityPolynomialMetricGerm_matrix_symmetric
    (x : CurvatureCoordinateSpace4) :
    (coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm x).transpose =
      coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm x := by
  change
    (coordinateMetricMatrixField4
      (cubicMetricTaylorField4 minkowskiMetric
        activeAmbiguityFormalMetricJet2 activeAmbiguityFormalMetricJet3) x).transpose =
      coordinateMetricMatrixField4
        (cubicMetricTaylorField4 minkowskiMetric
          activeAmbiguityFormalMetricJet2 activeAmbiguityFormalMetricJet3) x
  rw [coordinateMetricMatrixField4_cubicMetricTaylorField4]
  apply cubicMetricTaylorMatrixField4_transpose_eq_self
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [minkowskiMetric]
  · intro r s i j
    exact normalCoordinateMetricJet2OfRicci_metric_symm _ r s i j
  · intro r s t i j
    exact (activeAmbiguityFormalMetricJet3_symmetries r s t i j).2.2

/-- Symmetry of the active matrix is exactly symmetry of its underlying
algebraic bilinear form. -/
theorem activeAmbiguityPolynomialMetricGerm_bilin_symmetric
    (x : CurvatureCoordinateSpace4) :
    (continuousBilinFormToBilin
      (activeAmbiguityPolynomialMetricGerm x)).IsSymm := by
  rw [← coordinateMetricMatrixField4_toBilin']
  exact Matrix.isSymm_toBilin'_iff_isSymm.mpr
    (activeAmbiguityPolynomialMetricGerm_matrix_symmetric x)

/-- The standard Minkowski bilinear form satisfies the operational index-one
Lorentzian condition used by the reconstruction pipeline. -/
theorem minkowskiBilinForm_hasLorentzianIndexOne :
    HasLorentzianIndexOne minkowskiBilinForm := by
  have hform (u v : CurvatureCoordinateSpace4) :
      minkowskiBilinForm u v =
        -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 := by
    rw [minkowskiBilinForm]
    simp only [Matrix.toBilin_apply, Pi.basisFun_repr]
    rw [minkowskiMetric]
    simp [Fin.sum_univ_succ]
    ring
  intro t z htt htz hz
  rw [hform] at htt htz ⊢
  have htSpatialNonneg :
      0 ≤ t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 := by positivity
  have ht0SqPos : 0 < t 0 ^ 2 := by
    nlinarith
  have hzSpatialNonneg :
      0 ≤ z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by positivity
  have hzSpatialPos :
      0 < z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
    by_contra hnot
    have hzSpatialZero : z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 = 0 := by
      exact le_antisymm (le_of_not_gt hnot) hzSpatialNonneg
    have hz1 : z 1 = 0 := by
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
    have hz2 : z 2 = 0 := by
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
    have hz3 : z 3 = 0 := by
      nlinarith [sq_nonneg (z 1), sq_nonneg (z 2), sq_nonneg (z 3)]
    have ht0ne : t 0 ≠ 0 := by nlinarith
    have hz0 : z 0 = 0 := by
      rw [hz1, hz2, hz3] at htz
      simp only [mul_zero, add_zero] at htz
      have hmul : t 0 * z 0 = 0 := by nlinarith
      exact (mul_eq_zero.mp hmul).resolve_left ht0ne
    apply hz
    funext i
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
    · exact hz3
  have hCauchy :
      (t 1 * z 1 + t 2 * z 2 + t 3 * z 3) ^ 2 ≤
        (t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2) *
          (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) := by
    nlinarith [sq_nonneg (t 1 * z 2 - t 2 * z 1),
      sq_nonneg (t 1 * z 3 - t 3 * z 1),
      sq_nonneg (t 2 * z 3 - t 3 * z 2)]
  have htime :
      t 1 ^ 2 + t 2 ^ 2 + t 3 ^ 2 < t 0 ^ 2 := by
    nlinarith
  have horth :
      t 1 * z 1 + t 2 * z 2 + t 3 * z 3 = t 0 * z 0 := by
    nlinarith
  have hstrict :
      (t 1 * z 1 + t 2 * z 2 + t 3 * z 3) ^ 2 <
        t 0 ^ 2 * (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2) :=
    lt_of_le_of_lt hCauchy (mul_lt_mul_of_pos_right htime hzSpatialPos)
  have hsquare :
      (t 1 * z 1 + t 2 * z 2 + t 3 * z 3) ^ 2 =
        t 0 ^ 2 * z 0 ^ 2 := by
    rw [horth]
    ring
  have hztime :
      z 0 ^ 2 < z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
    nlinarith
  nlinarith

/-- At the base point the active polynomial germ has the full operational
Lorentzian index-one signature, not only the correct determinant sign. -/
theorem activeAmbiguityPolynomialMetricGerm_zero_hasLorentzianIndexOne :
    HasLorentzianIndexOne
      (continuousBilinFormToBilin
        (activeAmbiguityPolynomialMetricGerm 0)) := by
  have hmetric :
      continuousBilinFormToBilin
          (activeAmbiguityPolynomialMetricGerm 0) =
        minkowskiBilinForm := by
    calc
      continuousBilinFormToBilin
          (activeAmbiguityPolynomialMetricGerm 0) =
          Matrix.toBilin'
            (coordinateMetricMatrixField4
              activeAmbiguityPolynomialMetricGerm 0) :=
        (coordinateMetricMatrixField4_toBilin'
          activeAmbiguityPolynomialMetricGerm 0).symm
      _ = Matrix.toBilin' minkowskiMetric := by
        rw [(activeAmbiguityPolynomialMetricGerm_realizes_threeJet).1]
      _ = minkowskiBilinForm := by
        rw [← Matrix.toBilin_basisFun]
        rfl
  rw [hmetric]
  exact minkowskiBilinForm_hasLorentzianIndexOne

/-- The determinant of the active coordinate metric is a continuous scalar
function. -/
theorem continuous_activeAmbiguityPolynomialMetricGerm_det :
    Continuous (fun x => Matrix.det
      (coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm x)) := by
  rw [show (fun x => Matrix.det
      (coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm x)) =
    (fun G : Matrix4 => Matrix.det G) ∘
      cubicMetricTaylorMatrixField4 minkowskiMetric
        activeAmbiguityFormalMetricJet2 activeAmbiguityFormalMetricJet3 by
    funext x
    change Matrix.det (coordinateMetricMatrixField4
        (cubicMetricTaylorField4 minkowskiMetric
          activeAmbiguityFormalMetricJet2 activeAmbiguityFormalMetricJet3) x) = _
    rw [Function.comp_apply,
      coordinateMetricMatrixField4_cubicMetricTaylorField4]]
  exact continuous_id.matrix_det.comp
    (continuous_cubicMetricTaylorMatrixField4 _ _ _)

/-- At the distinguished normal point the active polynomial metric has the
Minkowski determinant `-1`. -/
@[simp] theorem activeAmbiguityPolynomialMetricGerm_det_zero :
    Matrix.det
      (coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm 0) = -1 := by
  rw [(activeAmbiguityPolynomialMetricGerm_realizes_threeJet).1]
  exact minkowskiMetric_det

/-- The maximal determinant-sign neighborhood singled out by the active
polynomial representative. -/
def activeAmbiguityPolynomialMetricLorentzSignNeighborhood :
    Set CurvatureCoordinateSpace4 :=
  {x | Matrix.det
    (coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm x) < 0}

/-- The determinant-sign neighborhood is open. -/
theorem isOpen_activeAmbiguityPolynomialMetricLorentzSignNeighborhood :
    IsOpen activeAmbiguityPolynomialMetricLorentzSignNeighborhood := by
  exact isOpen_lt continuous_activeAmbiguityPolynomialMetricGerm_det
    continuous_const

/-- The origin belongs to the determinant-sign neighborhood. -/
theorem zero_mem_activeAmbiguityPolynomialMetricLorentzSignNeighborhood :
    (0 : CurvatureCoordinateSpace4) ∈
      activeAmbiguityPolynomialMetricLorentzSignNeighborhood := by
  simp [activeAmbiguityPolynomialMetricLorentzSignNeighborhood]

/-- Equivalently, negative determinant persists eventually in the
neighborhood filter of the origin. -/
theorem eventually_activeAmbiguityPolynomialMetricGerm_det_neg :
    ∀ᶠ x in 𝓝 (0 : CurvatureCoordinateSpace4),
      Matrix.det
        (coordinateMetricMatrixField4 activeAmbiguityPolynomialMetricGerm x) < 0 := by
  exact
    isOpen_activeAmbiguityPolynomialMetricLorentzSignNeighborhood.eventually_mem
      zero_mem_activeAmbiguityPolynomialMetricLorentzSignNeighborhood

/-- Every coordinate matrix in the determinant-sign neighborhood is
nondegenerate. -/
theorem activeAmbiguityPolynomialMetricGerm_matrix_nondegenerate
    {x : CurvatureCoordinateSpace4}
    (hx : x ∈ activeAmbiguityPolynomialMetricLorentzSignNeighborhood) :
    (coordinateMetricMatrixField4
      activeAmbiguityPolynomialMetricGerm x).Nondegenerate := by
  apply Matrix.Nondegenerate.of_det_ne_zero
  exact ne_of_lt hx

/-- The actual algebraic bilinear form is nondegenerate throughout the open
determinant-sign neighborhood. -/
theorem activeAmbiguityPolynomialMetricGerm_bilin_nondegenerate
    {x : CurvatureCoordinateSpace4}
    (hx : x ∈ activeAmbiguityPolynomialMetricLorentzSignNeighborhood) :
    (continuousBilinFormToBilin
      (activeAmbiguityPolynomialMetricGerm x)).Nondegenerate := by
  rw [← coordinateMetricMatrixField4_toBilin']
  exact (activeAmbiguityPolynomialMetricGerm_matrix_nondegenerate hx).toBilin'

/-- Bundled local metric-germ statement: one open neighborhood of the origin
simultaneously carries symmetry, nondegeneracy, and the negative determinant
sign inherited from Minkowski space. -/
theorem exists_activeAmbiguityPolynomialMetricGerm_nondegenerateNeighborhood :
    ∃ U : Set CurvatureCoordinateSpace4,
      IsOpen U ∧
      (0 : CurvatureCoordinateSpace4) ∈ U ∧
      ∀ x ∈ U,
        (continuousBilinFormToBilin
            (activeAmbiguityPolynomialMetricGerm x)).IsSymm ∧
          (continuousBilinFormToBilin
            (activeAmbiguityPolynomialMetricGerm x)).Nondegenerate ∧
          Matrix.det
            (coordinateMetricMatrixField4
              activeAmbiguityPolynomialMetricGerm x) < 0 := by
  refine ⟨activeAmbiguityPolynomialMetricLorentzSignNeighborhood,
    isOpen_activeAmbiguityPolynomialMetricLorentzSignNeighborhood,
    zero_mem_activeAmbiguityPolynomialMetricLorentzSignNeighborhood, ?_⟩
  intro x hx
  exact ⟨activeAmbiguityPolynomialMetricGerm_bilin_symmetric x,
    activeAmbiguityPolynomialMetricGerm_bilin_nondegenerate hx, hx⟩

end RainichKaluza
