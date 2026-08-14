import RainichKaluza.FourthOrderMetricDetector

/-!
# Matrix inverse semantic regression

This tiny behavioral lock distinguishes Mathlib's nonsingular matrix inverse
from entrywise reciprocal on an explicit nondiagonal real `4 × 4` matrix.
-/

namespace RainichKaluza

open scoped Matrix

/-- A unit upper-triangular shear, hence nonsingular and nondiagonal. -/
def matrixInverseRegressionShear4 : Matrix4 :=
  !![1, 1, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

/-- Its explicit inverse reverses the shear. -/
def matrixInverseRegressionShearInverse4 : Matrix4 :=
  !![1, -1, 0, 0;
     0,  1, 0, 0;
     0,  0, 1, 0;
     0,  0, 0, 1]

theorem matrixInverseRegressionShear4_inv :
    (matrixInverseRegressionShear4⁻¹ : Matrix4) =
      matrixInverseRegressionShearInverse4 := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixInverseRegressionShear4,
      matrixInverseRegressionShearInverse4, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- **Behavioral regression:** true matrix inversion is not entrywise
reciprocal.  The `(0,1)` component is `-1` for the inverse and `+1` for the
entrywise reciprocal. -/
theorem matrixInverseRegressionShear4_inv_ne_entrywiseReciprocal :
    (matrixInverseRegressionShear4⁻¹ : Matrix4) ≠
      fun i j => (matrixInverseRegressionShear4 i j)⁻¹ := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 4)) (1 : Fin 4)
  rw [matrixInverseRegressionShear4_inv] at h01
  norm_num [matrixInverseRegressionShear4,
    matrixInverseRegressionShearInverse4] at h01

end RainichKaluza
