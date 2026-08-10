import RainichKaluza.CanonicalMaxwellTwoForm
import Mathlib.Tactic.NoncommRing

/-!
# Lorentz-frame transport of the Maxwell seed

The canonical two-form is useful geometrically only if it transports correctly
between Lorentz frames.  This file proves the relevant matrix covariance
identities.  A frame matrix `L` and its inverse `K` are supplied with the
explicit Lorentz identities needed by the proof; bundle smoothness and the
existence of such frames are separate geometric hypotheses.
-/

namespace RainichKaluza

open scoped Matrix
open Matrix

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Diagonal Minkowski metric in the selected frame. -/
def minkowskiMetric : Matrix4 :=
  !![-1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, 1]

/-- Matrix form of the mixed Maxwell stress for an antisymmetric covariant
two-tensor.  For an antisymmetric `F`, `-tr(GFGF)` is its quadratic invariant.
-/
noncomputable def matrixMaxwellStress (G F : Matrix4) : Matrix4 :=
  let core := G * F * G * F
  (-core) + (1 / 4 * Matrix.trace core) • (1 : Matrix4)

/-- Covariant two-form transport by a frame matrix. -/
def transportTwoForm (L F : Matrix4) : Matrix4 :=
  Lᵀ * F * L

/-- Mixed-endomorphism transport by a frame and supplied inverse. -/
def transportMixed (K X L : Matrix4) : Matrix4 :=
  K * X * L

set_option maxHeartbeats 800000 in
/-- The trace formula agrees with the component Maxwell stress on the
canonical two-form. -/
theorem matrixMaxwellStress_canonical (E B : ℝ) :
    matrixMaxwellStress minkowskiMetric (canonicalMaxwellTwoForm E B) =
      canonicalMaxwellStress E B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMaxwellStress, minkowskiMetric, canonicalMaxwellTwoForm,
      canonicalMaxwellStress, canonicalStressMagnitude,
      Matrix.trace, Fin.sum_univ_succ] <;> ring

/-- Congruence transport preserves antisymmetry of a two-form. -/
theorem transportTwoForm_transpose
    (L F : Matrix4) (hF : Fᵀ = -F) :
    (transportTwoForm L F)ᵀ = -transportTwoForm L F := by
  unfold transportTwoForm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hF]
  simp [Matrix.mul_assoc]

/-- Lorentz identities transport the quadratic stress core by similarity. -/
theorem lorentzTransport_core
    (G L K F : Matrix4)
    (hGLt : G * Lᵀ = K * G)
    (hLGLt : L * G * Lᵀ = G) :
    G * transportTwoForm L F * G * transportTwoForm L F =
      transportMixed K (G * F * G * F) L := by
  unfold transportTwoForm transportMixed
  calc
    G * (Lᵀ * F * L) * G * (Lᵀ * F * L) =
        (G * Lᵀ) * F * (L * G * Lᵀ) * F * L := by noncomm_ring
    _ = (K * G) * F * G * F * L := by rw [hGLt, hLGLt]
    _ = K * (G * F * G * F) * L := by noncomm_ring

/-- Similarity by mutually inverse frame matrices preserves the core trace. -/
theorem lorentzTransport_core_trace
    (G L K F : Matrix4)
    (hLK : L * K = 1)
    (hGLt : G * Lᵀ = K * G)
    (hLGLt : L * G * Lᵀ = G) :
    Matrix.trace
        (G * transportTwoForm L F * G * transportTwoForm L F) =
      Matrix.trace (G * F * G * F) := by
  rw [lorentzTransport_core G L K F hGLt hLGLt]
  unfold transportMixed
  calc
    Matrix.trace (K * (G * F * G * F) * L) =
        Matrix.trace (L * (K * (G * F * G * F))) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((L * K) * (G * F * G * F)) := by
      congr 1
      exact (Matrix.mul_assoc L K (G * F * G * F)).symm
    _ = Matrix.trace (G * F * G * F) := by rw [hLK, one_mul]

/-- **Lorentz covariance of Maxwell stress.** -/
theorem matrixMaxwellStress_lorentzTransport
    (G L K F : Matrix4)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hGLt : G * Lᵀ = K * G)
    (hLGLt : L * G * Lᵀ = G) :
    matrixMaxwellStress G (transportTwoForm L F) =
      transportMixed K (matrixMaxwellStress G F) L := by
  have hcore := lorentzTransport_core G L K F hGLt hLGLt
  have htrace := lorentzTransport_core_trace G L K F hLK hGLt hLGLt
  have htrace' : Matrix.trace (transportMixed K (G * F * G * F) L) =
      Matrix.trace (G * F * G * F) := by
    rw [← hcore]
    exact htrace
  unfold matrixMaxwellStress transportMixed
  dsimp only
  rw [hcore, htrace']
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_assoc,
    smul_mul_assoc, mul_smul_comm, mul_one, hKL]
  unfold transportMixed
  noncomm_ring

/-- Similarity transport preserves a scalar square law. -/
theorem transportMixed_sq
    (L K X : Matrix4) (qSq : ℝ)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hX : X * X = qSq • (1 : Matrix4)) :
    transportMixed K X L * transportMixed K X L =
      qSq • (1 : Matrix4) := by
  unfold transportMixed
  calc
    (K * X * L) * (K * X * L) = K * X * (L * K) * X * L := by
      noncomm_ring
    _ = K * (X * X) * L := by rw [hLK]; noncomm_ring
    _ = K * (qSq • (1 : Matrix4)) * L := by rw [hX]
    _ = qSq • (1 : Matrix4) := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, hKL]

/-- Similarity transport preserves idempotence. -/
theorem transportMixed_idempotent
    (L K P : Matrix4)
    (hLK : L * K = 1)
    (hP : P * P = P) :
    transportMixed K P L * transportMixed K P L =
      transportMixed K P L := by
  unfold transportMixed
  calc
    (K * P * L) * (K * P * L) = K * P * (L * K) * P * L := by
      noncomm_ring
    _ = K * (P * P) * L := by rw [hLK]; noncomm_ring
    _ = K * P * L := by rw [hP]

/-- A transported complementary projector pair still resolves the identity. -/
theorem transportMixed_projectors_sum
    (L K P Q : Matrix4)
    (hKL : K * L = 1)
    (hsum : P + Q = 1) :
    transportMixed K P L + transportMixed K Q L = 1 := by
  unfold transportMixed
  calc
    K * P * L + K * Q * L = K * (P + Q) * L := by noncomm_ring
    _ = K * 1 * L := by rw [hsum]
    _ = 1 := by rw [mul_one, hKL]

/-- **Transported local Maxwell seed.** Every positive canonical residual has
an explicit real two-form square root in any supplied Lorentz frame, and its
stress is the similarity transport of the canonical residual. -/
theorem matrixMaxwellStress_transported_seed
    (L K : Matrix4) (q : ℝ) (hq : 0 < q)
    (hKL : K * L = 1) (hLK : L * K = 1)
    (hGLt : minkowskiMetric * Lᵀ = K * minkowskiMetric)
    (hLGLt : L * minkowskiMetric * Lᵀ = minkowskiMetric) :
    matrixMaxwellStress minkowskiMetric
        (transportTwoForm L
          (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)) =
      transportMixed K (canonicalMaxwellResidual q) L := by
  rw [matrixMaxwellStress_lorentzTransport minkowskiMetric L K
    (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)
    hKL hLK hGLt hLGLt]
  rw [matrixMaxwellStress_canonical]
  have harg : 0 ≤ 2 * q := by positivity
  have hsqrt : (Real.sqrt (2 * q)) ^ 2 = 2 * q := Real.sq_sqrt harg
  have hrho : canonicalStressMagnitude (Real.sqrt (2 * q)) 0 = q := by
    unfold canonicalStressMagnitude
    rw [hsqrt]
    ring
  congr 1
  unfold canonicalMaxwellStress
  rw [hrho]
  rfl

/-- The transported positive-`q` seed remains an antisymmetric two-form. -/
theorem transported_seed_transpose
    (L : Matrix4) (q : ℝ) :
    (transportTwoForm L
      (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0))ᵀ =
      -transportTwoForm L
        (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) :=
  transportTwoForm_transpose L _
    (canonicalMaxwellTwoForm_transpose (Real.sqrt (2 * q)) 0)

end RainichKaluza
