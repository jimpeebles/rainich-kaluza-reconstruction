import RainichKaluza.SmoothMaxwellSeed
import Mathlib.Tactic.NoncommRing

/-!
# First derivative of the transported Maxwell seed

This file supplies the missing first-jet connector between the smooth local
Maxwell seed and the exterior EMD equations.  All derivative symbols are
evaluated in one tangent direction.  If

`F₀ = Lᵀ Fcan(q) L`,

then the product rule and `Ω = (dL)L⁻¹` give

`dF₀ = Lᵀ(ΩᵀFcan + (dq/2q)Fcan + FcanΩ)L`.

The differentiated Lorentz equation implies `ΩG+GΩᵀ=0`, so the frame part
of this derivative is intrinsically a Lorentz-connection term.  The result is
an algebraic first-jet theorem: manifold directional derivatives instantiate
`dL` and `dq` in a chart.
-/

namespace RainichKaluza

open scoped Matrix
open Matrix

/-- Directional derivative of the canonical electric amplitude
`E=sqrt(2q)` on the positive branch. -/
noncomputable def canonicalPositiveQAmplitudeDerivative
    (q dq : ℝ) : ℝ :=
  dq / Real.sqrt (2 * q)

/-- Directional derivative of the canonical positive-`q` two-form. -/
noncomputable def canonicalPositiveQSeedDerivative
    (q dq : ℝ) : Matrix4 :=
  canonicalMaxwellTwoForm (canonicalPositiveQAmplitudeDerivative q dq) 0

/-- The reconstructed amplitude derivative differentiates `E²=2q`. -/
theorem canonicalPositiveQAmplitudeDerivative_relation
    (q dq : ℝ) (hq : 0 < q) :
    Real.sqrt (2 * q) * canonicalPositiveQAmplitudeDerivative q dq = dq := by
  unfold canonicalPositiveQAmplitudeDerivative
  have hsqrt : Real.sqrt (2 * q) ≠ 0 := by positivity
  field_simp [hsqrt]

/-- Equivalent logarithmic form of the positive-branch amplitude derivative. -/
theorem canonicalPositiveQAmplitudeDerivative_eq_logarithmic
    (q dq : ℝ) (hq : 0 < q) :
    canonicalPositiveQAmplitudeDerivative q dq =
      (dq / (2 * q)) * Real.sqrt (2 * q) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hsqrt0 : Real.sqrt (2 * q) ≠ 0 := by positivity
  have hsqrtSq : (Real.sqrt (2 * q)) ^ 2 = 2 * q := by
    exact Real.sq_sqrt (by positivity)
  unfold canonicalPositiveQAmplitudeDerivative
  apply (div_eq_iff hsqrt0).2
  have hEE : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := by
    simpa only [pow_two] using hsqrtSq
  symm
  calc
    (dq / (2 * q) * Real.sqrt (2 * q)) * Real.sqrt (2 * q) =
        dq / (2 * q) *
          (Real.sqrt (2 * q) * Real.sqrt (2 * q)) := by ring
    _ = dq / (2 * q) * (2 * q) := by rw [hEE]
    _ = dq := div_mul_cancel₀ dq (mul_ne_zero (by norm_num) hq0)

/-- The canonical seed derivative is its logarithmic amplitude derivative
times the seed itself. -/
theorem canonicalPositiveQSeedDerivative_eq_logarithmic_smul
    (q dq : ℝ) (hq : 0 < q) :
    canonicalPositiveQSeedDerivative q dq =
      (dq / (2 * q)) •
        canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 := by
  have hamp := canonicalPositiveQAmplitudeDerivative_eq_logarithmic q dq hq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalPositiveQSeedDerivative,
      canonicalMaxwellTwoForm, hamp]

/-- The canonical first derivative remains skew. -/
theorem canonicalPositiveQSeedDerivative_transpose (q dq : ℝ) :
    (canonicalPositiveQSeedDerivative q dq)ᵀ =
      -canonicalPositiveQSeedDerivative q dq :=
  canonicalMaxwellTwoForm_transpose _ _

/-- Product-rule derivative of `Lᵀ F L` in one direction. -/
def transportedTwoFormDerivative
    (L dL F dF : Matrix4) : Matrix4 :=
  dLᵀ * F * L + Lᵀ * dF * L + Lᵀ * F * dL

/-- Differentiating a family of skew two-forms again gives a skew tensor. -/
theorem transportedTwoFormDerivative_transpose
    (L dL F dF : Matrix4)
    (hF : Fᵀ = -F) (hdF : dFᵀ = -dF) :
    (transportedTwoFormDerivative L dL F dF)ᵀ =
      -transportedTwoFormDerivative L dL F dF := by
  unfold transportedTwoFormDerivative
  rw [Matrix.transpose_add, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul,
    hF, hdF]
  simp only [Matrix.transpose_transpose]
  noncomm_ring

/-- Evaluated Lorentz-frame connection `Ω=(dL)L⁻¹`. -/
def lorentzFrameConnection
    (dL K : Matrix4) : Matrix4 :=
  dL * K

/-- The derivative of a transported two-form is the transport of its
connection-corrected frame derivative. -/
theorem transportedTwoFormDerivative_eq_connectionTransport
    (L K dL F dF : Matrix4) (hKL : K * L = 1) :
    transportedTwoFormDerivative L dL F dF =
      transportTwoForm L
        ((lorentzFrameConnection dL K)ᵀ * F + dF +
          F * lorentzFrameConnection dL K) := by
  have hdL : lorentzFrameConnection dL K * L = dL := by
    unfold lorentzFrameConnection
    rw [Matrix.mul_assoc, hKL, Matrix.mul_one]
  have hdLt : Lᵀ * (lorentzFrameConnection dL K)ᵀ = dLᵀ := by
    have h := congrArg Matrix.transpose hdL
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h
  calc
    transportedTwoFormDerivative L dL F dF =
        dLᵀ * F * L + Lᵀ * dF * L + Lᵀ * F * dL := rfl
    _ = (Lᵀ * (lorentzFrameConnection dL K)ᵀ) * F * L +
        Lᵀ * dF * L +
        Lᵀ * F * (lorentzFrameConnection dL K * L) := by
      rw [hdL, hdLt]
    _ = transportTwoForm L
        ((lorentzFrameConnection dL K)ᵀ * F + dF +
          F * lorentzFrameConnection dL K) := by
      unfold transportTwoForm
      noncomm_ring

/-- A first derivative satisfying the differentiated Lorentz identity gives
a connection value in the Lorentz Lie algebra. -/
theorem lorentzFrameConnection_mem_lorentzLie
    (L K dL : Matrix4) (hKL : K * L = 1)
    (hLorentz : L * minkowskiMetric * Lᵀ = minkowskiMetric)
    (hLorentzDerivative :
      dL * minkowskiMetric * Lᵀ +
        L * minkowskiMetric * dLᵀ = 0) :
    lorentzFrameConnection dL K * minkowskiMetric +
        minkowskiMetric * (lorentzFrameConnection dL K)ᵀ = 0 := by
  have hdL : lorentzFrameConnection dL K * L = dL := by
    unfold lorentzFrameConnection
    rw [Matrix.mul_assoc, hKL, Matrix.mul_one]
  have hdLt : Lᵀ * (lorentzFrameConnection dL K)ᵀ = dLᵀ := by
    have h := congrArg Matrix.transpose hdL
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h
  calc
    lorentzFrameConnection dL K * minkowskiMetric +
        minkowskiMetric * (lorentzFrameConnection dL K)ᵀ =
      lorentzFrameConnection dL K *
          (L * minkowskiMetric * Lᵀ) +
        (L * minkowskiMetric * Lᵀ) *
          (lorentzFrameConnection dL K)ᵀ := by rw [hLorentz]
    _ = (lorentzFrameConnection dL K * L) *
          minkowskiMetric * Lᵀ +
        L * minkowskiMetric *
          (Lᵀ * (lorentzFrameConnection dL K)ᵀ) := by
      noncomm_ring
    _ = dL * minkowskiMetric * Lᵀ +
        L * minkowskiMetric * dLᵀ := by rw [hdL, hdLt]
    _ = 0 := hLorentzDerivative

/-- Directional derivative of the transported positive-`q` Maxwell seed. -/
noncomputable def transportedPositiveQSeedDerivative
    (L dL : Matrix4) (q dq : ℝ) : Matrix4 :=
  transportedTwoFormDerivative L dL
    (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0)
    (canonicalPositiveQSeedDerivative q dq)

/-- The transported seed derivative remains skew. -/
theorem transportedPositiveQSeedDerivative_transpose
    (L dL : Matrix4) (q dq : ℝ) :
    (transportedPositiveQSeedDerivative L dL q dq)ᵀ =
      -transportedPositiveQSeedDerivative L dL q dq := by
  exact transportedTwoFormDerivative_transpose _ _ _ _
    (canonicalMaxwellTwoForm_transpose _ _)
    (canonicalPositiveQSeedDerivative_transpose q dq)

/-- **Transported-seed first-jet formula.** The derivative splits into an
amplitude channel fixed by `dq` and a Lorentz-connection channel fixed by the
variation of the principal frame. -/
theorem transportedPositiveQSeedDerivative_eq_connectionFormula
    (L K dL : Matrix4) (q dq : ℝ) (hq : 0 < q)
    (hKL : K * L = 1) :
    transportedPositiveQSeedDerivative L dL q dq =
      transportTwoForm L
        ((lorentzFrameConnection dL K)ᵀ *
            canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          (dq / (2 * q)) •
            canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 +
          canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 *
            lorentzFrameConnection dL K) := by
  unfold transportedPositiveQSeedDerivative
  rw [transportedTwoFormDerivative_eq_connectionTransport L K dL _ _ hKL]
  rw [canonicalPositiveQSeedDerivative_eq_logarithmic_smul q dq hq]

end RainichKaluza
