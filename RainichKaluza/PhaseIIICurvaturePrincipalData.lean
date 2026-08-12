import RainichKaluza.PhaseIIITransportedSeedCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option maxSynthPendingDepth 2

/-!
# Curvature principal data for the Phase-III Maxwell seed

This file closes the coordinate bridge between the basis-free Maxwell
principal-plane theorem and the actual-field Phase-III constructor.

* a positive protected magnitude is selected canonically as `sqrt qSq`;
* the two Maxwell projectors are explicit smooth matrix fields in the
  residual and reconstructed squared magnitude;
* their idempotence, complementarity, and annihilation follow pointwise from
  the non-null square law;
* matrix projector identities feed the basis-free Gram--Schmidt theorem, so
  the smooth fixed-probe tetrad is genuinely pseudo-orthonormal rather than
  merely a smooth candidate;
* in a Minkowski orthonormal trivialization its coframe satisfies the exact
  Lorentz identity required by transported Maxwell stress covariance;
* a `C¹` local complexion angle then produces the complete actual Phase-III
  seed-pair realization.
-/

namespace RainichKaluza

open LinearMap (BilinForm)
open scoped Matrix Topology

/-- Forget continuity of a continuous bilinear form while retaining both
linear structures. -/
noncomputable def continuousBilinFormToBilin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ContinuousBilinForm V) : BilinForm ℝ V where
  toFun x := (g x).toLinearMap
  map_add' x y := by
    ext z
    simp
  map_smul' c x := by
    ext z
    simp

@[simp]
theorem continuousBilinFormToBilin_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ContinuousBilinForm V) (x y : V) :
    continuousBilinFormToBilin g x y = g x y := rfl

/-- The continuous form represented by the Minkowski matrix forgets to the
same algebraic bilinear form used by the principal-plane theorems. -/
theorem continuousBilinFormToBilin_matrix_minkowski :
    continuousBilinFormToBilin
      (matrixContinuousBilinForm4 minkowskiMetric) = minkowskiBilinForm := by
  ext x y
  simp [continuousBilinFormToBilin, matrixContinuousBilinForm4,
    minkowskiBilinForm, Matrix.toBilin'_apply, Pi.single_apply]

/-- Metric-self-adjoint endomorphisms are closed under subtraction. -/
theorem MetricSelfAdjoint.sub
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {g : BilinForm ℝ V} {R S : V →ₗ[ℝ] V}
    (hR : MetricSelfAdjoint g R) (hS : MetricSelfAdjoint g S) :
    MetricSelfAdjoint g (R - S) := by
  intro x y
  simp only [LinearMap.sub_apply, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right]
  rw [hR x y, hS x y]

/-- Negative Maxwell principal projector as an actual matrix field. -/
noncomputable def matrixMaxwellMinusProjectorField
    {X : Type*} (S : X → Matrix4) (q : X → ℝ) (z : X) : Matrix4 :=
  maxwellMinusProjector (S z) (q z)

/-- Positive Maxwell principal projector as an actual matrix field. -/
noncomputable def matrixMaxwellPlusProjectorField
    {X : Type*} (S : X → Matrix4) (q : X → ℝ) (z : X) : Matrix4 :=
  maxwellPlusProjector (S z) (q z)

/-- Matrix-to-endomorphism conversion commutes with the negative Maxwell
projector polynomial. -/
theorem matrixMaxwellMinusProjector_toLin'
    (S : Matrix4) (q : ℝ) :
    Matrix.toLin' (maxwellMinusProjector S q) =
      maxwellMinusProjector (Matrix.toLin' S) q := by
  simp [maxwellMinusProjector, involutionMinusProjector,
    normalizedMaxwellResidual, map_smul, map_sub, Matrix.toLin'_one,
    Module.End.one_eq_id]

/-- Matrix-to-endomorphism conversion commutes with the positive Maxwell
projector polynomial. -/
theorem matrixMaxwellPlusProjector_toLin'
    (S : Matrix4) (q : ℝ) :
    Matrix.toLin' (maxwellPlusProjector S q) =
      maxwellPlusProjector (Matrix.toLin' S) q := by
  simp [maxwellPlusProjector, involutionPlusProjector,
    normalizedMaxwellResidual, map_smul, map_add, Matrix.toLin'_one,
    Module.End.one_eq_id]

/-- A smooth nonzero magnitude and smooth residual give a smooth negative
principal-projector matrix field. -/
theorem contDiffOn_matrixMaxwellMinusProjectorField
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {S : X → Matrix4} {q : X → ℝ}
    (hS : MatrixFieldContDiffOn n U S) (hq : ContDiffOn ℝ n q U)
    (hq0 : ∀ z ∈ U, q z ≠ 0) :
    MatrixFieldContDiffOn n U (matrixMaxwellMinusProjectorField S q) := by
  have hqinv : ContDiffOn ℝ n (fun z => (q z)⁻¹) U := hq.inv hq0
  have hnorm : MatrixFieldContDiffOn n U
      (fun z => (q z)⁻¹ • S z) :=
    MatrixFieldContDiffOn.smulField hqinv hS
  have hone : MatrixFieldContDiffOn n U (fun _ : X => (1 : Matrix4)) :=
    matrixFieldContDiffOn_const 1
  have hhalf : ContDiffOn ℝ n (fun _ : X => (2 : ℝ)⁻¹) U :=
    contDiffOn_const
  change MatrixFieldContDiffOn n U
    (fun z => (2 : ℝ)⁻¹ • (1 - (q z)⁻¹ • S z))
  exact MatrixFieldContDiffOn.smulField hhalf (hone.sub hnorm)

/-- A smooth nonzero magnitude and smooth residual give a smooth positive
principal-projector matrix field. -/
theorem contDiffOn_matrixMaxwellPlusProjectorField
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {S : X → Matrix4} {q : X → ℝ}
    (hS : MatrixFieldContDiffOn n U S) (hq : ContDiffOn ℝ n q U)
    (hq0 : ∀ z ∈ U, q z ≠ 0) :
    MatrixFieldContDiffOn n U (matrixMaxwellPlusProjectorField S q) := by
  have hqinv : ContDiffOn ℝ n (fun z => (q z)⁻¹) U := hq.inv hq0
  have hnorm : MatrixFieldContDiffOn n U
      (fun z => (q z)⁻¹ • S z) :=
    MatrixFieldContDiffOn.smulField hqinv hS
  have hone : MatrixFieldContDiffOn n U (fun _ : X => (1 : Matrix4)) :=
    matrixFieldContDiffOn_const 1
  have hhalf : ContDiffOn ℝ n (fun _ : X => (2 : ℝ)⁻¹) U :=
    contDiffOn_const
  change MatrixFieldContDiffOn n U
    (fun z => (2 : ℝ)⁻¹ • (1 + (q z)⁻¹ • S z))
  exact MatrixFieldContDiffOn.smulField hhalf (hone.add hnorm)

/-- Canonical positive magnitude selected from the curvature-reconstructed
squared Maxwell magnitude. -/
noncomputable def positiveMaxwellMagnitudeFromSquare
    {X : Type*} (qSq : X → ℝ) (z : X) : ℝ :=
  Real.sqrt (qSq z)

/-- The positive square-root selection preserves all available smoothness on
a strictly positive reconstructed-square patch. -/
theorem contDiffOn_positiveMaxwellMagnitudeFromSquare
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {qSq : X → ℝ}
    (hqSq : ContDiffOn ℝ n qSq U)
    (hpos : ∀ z ∈ U, 0 < qSq z) :
    ContDiffOn ℝ n (positiveMaxwellMagnitudeFromSquare qSq) U := by
  exact hqSq.sqrt (fun z hz => ne_of_gt (hpos z hz))

/-- The chosen protected magnitude is strictly positive. -/
theorem positiveMaxwellMagnitudeFromSquare_pos
    {X : Type*} (qSq : X → ℝ) (z : X) (hpos : 0 < qSq z) :
    0 < positiveMaxwellMagnitudeFromSquare qSq z := by
  exact Real.sqrt_pos.2 hpos

/-- The chosen magnitude squares to the reconstructed curvature invariant. -/
theorem positiveMaxwellMagnitudeFromSquare_sq
    {X : Type*} (qSq : X → ℝ) (z : X) (hpos : 0 < qSq z) :
    positiveMaxwellMagnitudeFromSquare qSq z ^ 2 = qSq z := by
  exact Real.sq_sqrt (le_of_lt hpos)

/-- Smooth local angle on the positive-cosine chart of the unit complexion
circle. -/
noncomputable def positiveCosineComplexionAngle
    {X : Type*} (c s : X → ℝ) (z : X) : ℝ :=
  Real.arctan (s z / c z)

/-- The positive-cosine angle chart preserves smoothness wherever its
denominator stays positive. -/
theorem contDiffOn_positiveCosineComplexionAngle
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {c s : X → ℝ}
    (hc : ContDiffOn ℝ n c U) (hs : ContDiffOn ℝ n s U)
    (hcpos : ∀ z ∈ U, 0 < c z) :
    ContDiffOn ℝ n (positiveCosineComplexionAngle c s) U := by
  have hratio : ContDiffOn ℝ n (fun z => s z / c z) U :=
    hs.div hc (fun z hz => ne_of_gt (hcpos z hz))
  exact Real.contDiff_arctan.comp_contDiffOn hratio

/-- On the unit circle and positive-cosine chart, the recovered angle has
exactly the supplied cosine coefficient. -/
theorem cos_positiveCosineComplexionAngle
    {X : Type*} (c s : X → ℝ) (z : X)
    (hc : 0 < c z) (hunit : c z ^ 2 + s z ^ 2 = 1) :
    Real.cos (positiveCosineComplexionAngle c s z) = c z := by
  rw [positiveCosineComplexionAngle, Real.cos_arctan]
  have hc0 : c z ≠ 0 := ne_of_gt hc
  have harg : 1 + (s z / c z) ^ 2 = ((c z)⁻¹) ^ 2 := by
    field_simp [hc0]
    nlinarith
  rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  field_simp

/-- On the same chart, the recovered angle has exactly the supplied sine
coefficient. -/
theorem sin_positiveCosineComplexionAngle
    {X : Type*} (c s : X → ℝ) (z : X)
    (hc : 0 < c z) (hunit : c z ^ 2 + s z ^ 2 = 1) :
    Real.sin (positiveCosineComplexionAngle c s z) = s z := by
  rw [positiveCosineComplexionAngle, Real.sin_arctan]
  have hc0 : c z ≠ 0 := ne_of_gt hc
  have harg : 1 + (s z / c z) ^ 2 = ((c z)⁻¹) ^ 2 := by
    field_simp [hc0]
    nlinarith
  rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  field_simp

/-- Actual residual matrix field obtained by subtracting the accepted scalar
rank-one contribution from the mixed Ricci field. -/
def curvatureMaxwellResidualField
    {X : Type*} (R V : X → Matrix4) (z : X) : Matrix4 :=
  maxwellResidual (R z) (V z)

/-- The residual field inherits componentwise smoothness from the Ricci and
scalar-contribution fields. -/
theorem contDiffOn_curvatureMaxwellResidualField
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {R V : X → Matrix4}
    (hR : MatrixFieldContDiffOn n U R)
    (hV : MatrixFieldContDiffOn n U V) :
    MatrixFieldContDiffOn n U (curvatureMaxwellResidualField R V) := by
  exact hR.sub hV

/-- The pointwise scalar square law and reconstruction equation force the
actual curvature residual field to satisfy the Maxwell square law. -/
theorem curvatureMaxwellResidualField_sq
    {X : Type*} (R V : X → Matrix4)
    (traceV qSq : X → ℝ) (z : X)
    (hV : V z * V z = traceV z • V z)
    (hrecon : R z * V z + V z * R z - traceV z • V z =
      R z * R z - qSq z • (1 : Matrix4)) :
    curvatureMaxwellResidualField R V z *
        curvatureMaxwellResidualField R V z =
      qSq z • (1 : Matrix4) := by
  exact maxwellResidual_sq_of_reconstructionEquation
    (R z) (V z) (traceV z) (qSq z) hV hrecon

/-- Self-adjointness of the mixed Ricci and scalar rank-one contributions
passes automatically to the reconstructed residual. -/
theorem curvatureMaxwellResidualField_metricSelfAdjoint
    {X : Type*} (g : BilinForm ℝ (Fin 4 → ℝ))
    (R V : X → Matrix4) (z : X)
    (hR : MetricSelfAdjoint g (Matrix.toLin' (R z)))
    (hV : MetricSelfAdjoint g (Matrix.toLin' (V z))) :
    MetricSelfAdjoint g
      (Matrix.toLin' (curvatureMaxwellResidualField R V z)) := by
  change MetricSelfAdjoint g (Matrix.toLin' (R z - V z))
  rw [map_sub]
  exact hR.sub hV

/-- Curvature-reconstructed negative principal projector, with the positive
square root chosen canonically from `qSq`. -/
noncomputable def curvatureMaxwellMinusProjectorField
    {X : Type*} (S : X → Matrix4) (qSq : X → ℝ) (z : X) : Matrix4 :=
  matrixMaxwellMinusProjectorField S
    (positiveMaxwellMagnitudeFromSquare qSq) z

/-- Curvature-reconstructed positive principal projector. -/
noncomputable def curvatureMaxwellPlusProjectorField
    {X : Type*} (S : X → Matrix4) (qSq : X → ℝ) (z : X) : Matrix4 :=
  matrixMaxwellPlusProjectorField S
    (positiveMaxwellMagnitudeFromSquare qSq) z

/-- **Concrete principal-projector algebra.** The curvature square law and
positivity of `qSq` force both explicit matrix projectors to be idempotent,
mutually annihilating, complementary projectors. -/
theorem curvatureMaxwellPrincipalProjectorFields_structural
    {X : Type*} (S : X → Matrix4) (qSq : X → ℝ) (z : X)
    (hpos : 0 < qSq z)
    (hSq : S z * S z = qSq z • (1 : Matrix4)) :
    let P := curvatureMaxwellMinusProjectorField S qSq z
    let Q := curvatureMaxwellPlusProjectorField S qSq z
    P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ P + Q = 1 := by
  let q := positiveMaxwellMagnitudeFromSquare qSq z
  have hqpos : 0 < q := positiveMaxwellMagnitudeFromSquare_pos qSq z hpos
  have hqSq : q ^ 2 = qSq z :=
    positiveMaxwellMagnitudeFromSquare_sq qSq z hpos
  have hSqs : S z * S z = q ^ 2 • (1 : Matrix4) := by
    rw [hqSq]
    exact hSq
  have hP := maxwellMinusProjector_sq (S z) q (ne_of_gt hqpos) hSqs
  have hQ := maxwellPlusProjector_sq (S z) q (ne_of_gt hqpos) hSqs
  have hsum := maxwellProjectors_sum (S z) q
  have hSlin : Matrix.toLin' (S z) * Matrix.toLin' (S z) =
      q ^ 2 • (1 : Module.End ℝ (Fin 4 → ℝ)) := by
    have h' := congrArg Matrix.toLin' hSqs
    rw [Matrix.toLin'_mul] at h'
    simpa [map_smul, Matrix.toLin'_one, Module.End.one_eq_id,
      Module.End.mul_eq_comp] using h'
  have hzeroLin := maxwellProjectors_comp_zero_rev
    (Matrix.toLin' (S z)) q (ne_of_gt hqpos) hSlin
  have hPQ : maxwellMinusProjector (S z) q *
      maxwellPlusProjector (S z) q = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, matrixMaxwellMinusProjector_toLin',
      matrixMaxwellPlusProjector_toLin']
    simpa [Module.End.mul_eq_comp] using hzeroLin
  simpa [curvatureMaxwellMinusProjectorField,
    curvatureMaxwellPlusProjectorField,
    matrixMaxwellMinusProjectorField, matrixMaxwellPlusProjectorField,
    positiveMaxwellMagnitudeFromSquare, q, add_comm] using
    And.intro hP (And.intro hQ (And.intro hPQ hsum))

/-- The accepted scalar reconstruction equation therefore supplies the
complete concrete principal-projector algebra directly from `R-V`. -/
theorem curvatureMaxwellPrincipalProjectorFields_structural_of_reconstruction
    {X : Type*} (R V : X → Matrix4)
    (traceV qSq : X → ℝ) (z : X)
    (hpos : 0 < qSq z)
    (hV : V z * V z = traceV z • V z)
    (hrecon : R z * V z + V z * R z - traceV z • V z =
      R z * R z - qSq z • (1 : Matrix4)) :
    let S := curvatureMaxwellResidualField R V
    let P := curvatureMaxwellMinusProjectorField S qSq z
    let Q := curvatureMaxwellPlusProjectorField S qSq z
    P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ P + Q = 1 := by
  exact curvatureMaxwellPrincipalProjectorFields_structural
    (curvatureMaxwellResidualField R V) qSq z hpos
    (curvatureMaxwellResidualField_sq R V traceV qSq z hV hrecon)

/-- Both curvature-reconstructed principal projectors inherit the regularity
of the residual and reconstructed squared magnitude. -/
theorem contDiffOn_curvatureMaxwellPrincipalProjectorFields
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {S : X → Matrix4}
    {qSq : X → ℝ}
    (hS : MatrixFieldContDiffOn n U S)
    (hqSq : ContDiffOn ℝ n qSq U)
    (hpos : ∀ z ∈ U, 0 < qSq z) :
    MatrixFieldContDiffOn n U
        (curvatureMaxwellMinusProjectorField S qSq) ∧
      MatrixFieldContDiffOn n U
        (curvatureMaxwellPlusProjectorField S qSq) := by
  have hq := contDiffOn_positiveMaxwellMagnitudeFromSquare hqSq hpos
  have hq0 : ∀ z ∈ U,
      positiveMaxwellMagnitudeFromSquare qSq z ≠ 0 :=
    fun z hz => ne_of_gt
      (positiveMaxwellMagnitudeFromSquare_pos qSq z (hpos z hz))
  exact ⟨contDiffOn_matrixMaxwellMinusProjectorField hS hq hq0,
    contDiffOn_matrixMaxwellPlusProjectorField hS hq hq0⟩

/-- Smooth Ricci and accepted scalar-contribution fields therefore give
smooth concrete Maxwell projectors without an independently supplied
residual field. -/
theorem contDiffOn_curvatureMaxwellPrincipalProjectorFields_of_residual
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {n : WithTop ℕ∞} {U : Set X} {R V : X → Matrix4}
    {qSq : X → ℝ}
    (hR : MatrixFieldContDiffOn n U R)
    (hV : MatrixFieldContDiffOn n U V)
    (hqSq : ContDiffOn ℝ n qSq U)
    (hpos : ∀ z ∈ U, 0 < qSq z) :
    let S := curvatureMaxwellResidualField R V
    MatrixFieldContDiffOn n U
        (curvatureMaxwellMinusProjectorField S qSq) ∧
      MatrixFieldContDiffOn n U
        (curvatureMaxwellPlusProjectorField S qSq) := by
  exact contDiffOn_curvatureMaxwellPrincipalProjectorFields
    (contDiffOn_curvatureMaxwellResidualField hR hV) hqSq hpos

/-- **Coordinate fixed-probe frame criterion.** Matrix idempotence,
annihilation, and metric self-adjointness feed the basis-free principal-plane
theorem and verify the smooth matrix tetrad pointwise. -/
theorem smoothMatrixProjectedPrincipalTetrad_pseudoOrthonormal
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P Q : CurvatureCoordinateSpace4 → Matrix4)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hP : P z * P z = P z)
    (hQ : Q z * Q z = Q z)
    (hself : MetricSelfAdjoint (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (P z)))
    (hPQ : P z * Q z = 0)
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
    IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z))
      (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1 z).1
      (smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1 z).2 := by
  let gb := continuousBilinFormToBilin (g z)
  let Plin := Matrix.toLin' (P z)
  let Qlin := Matrix.toLin' (Q z)
  have hPid : Plin.comp Plin = Plin := by
    have h' := congrArg Matrix.toLin' hP
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hQid : Qlin.comp Qlin = Qlin := by
    have h' := congrArg Matrix.toLin' hQ
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hPQlin : Plin.comp Qlin = 0 := by
    have h' := congrArg Matrix.toLin' hPQ
    rw [Matrix.toLin'_mul] at h'
    simpa using h'
  have hu0 : gb (Plin u0) (Plin u0) < 0 := by
    simpa [gb, Plin, continuousBilinFormToBilin, smoothMetricPairing,
      smoothMatrixProjectedVector] using hL0 z hz
  have hu1 : 0 < gb (Plin u1) (Plin u1) -
      (gb (Plin u0) (Plin u1)) ^ 2 / gb (Plin u0) (Plin u0) := by
    rw [← metricOrthogonalizeSecond_norm gb hgsymm
      (Plin u0) (Plin u1) (ne_of_lt hu0)]
    simpa [gb, Plin, continuousBilinFormToBilin, smoothMetricPairing,
      smoothMetricOrthogonalizeSecond, smoothMatrixProjectedVector,
      metricOrthogonalizeSecond] using hL1 z hz
  have hv0 : 0 < gb (Qlin v0) (Qlin v0) := by
    simpa [gb, Qlin, continuousBilinFormToBilin, smoothMetricPairing,
      smoothMatrixProjectedVector] using hS0 z hz
  have hv1 : 0 < gb (Qlin v1) (Qlin v1) -
      (gb (Qlin v0) (Qlin v1)) ^ 2 / gb (Qlin v0) (Qlin v0) := by
    rw [← metricOrthogonalizeSecond_norm gb hgsymm
      (Qlin v0) (Qlin v1) (ne_of_gt hv0)]
    simpa [gb, Qlin, continuousBilinFormToBilin, smoothMetricPairing,
      smoothMetricOrthogonalizeSecond, smoothMatrixProjectedVector,
      metricOrthogonalizeSecond] using hS1 z hz
  have hframe := projectedPrincipalPlaneFrames_pseudoOrthonormal
    gb hgsymm Plin Qlin hPid hQid hself hPQlin
      u0 u1 v0 v1 hu0 hu1 hv0 hv1
  simpa [IsPseudoOrthonormalPrincipalTetrad,
    smoothMatrixProjectedPrincipalTetrad, smoothLorentzianPlaneFrame,
    smoothSpacelikePlaneFrame, smoothNormalizeTimelike,
    smoothNormalizeSpacelike, smoothMetricOrthogonalizeSecond,
    smoothMetricPairing, smoothMatrixProjectedVector,
    projectedLorentzianPlaneFrame, projectedSpacelikePlaneFrame,
    lorentzianPlaneFrame, spacelikePlaneFrame, normalizeTimelike,
    normalizeSpacelike, metricOrthogonalizeSecond,
    continuousBilinFormToBilin, gb, Plin, Qlin] using hframe

/-- The explicit curvature Maxwell projectors verify the fixed-probe tetrad
from the residual square law and residual metric self-adjointness. -/
theorem smoothCurvatureMaxwellPrincipalTetrad_pseudoOrthonormal
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) (hz : z ∈ U)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (hself : MetricSelfAdjoint (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (S z)))
    (hqSqPos : ∀ z ∈ U, 0 < qSq z)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1)) z) :
    IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z))
      (smoothMatrixProjectedPrincipalTetrad g
        (curvatureMaxwellMinusProjectorField S qSq)
        (curvatureMaxwellPlusProjectorField S qSq)
        u0 u1 v0 v1 z).1
      (smoothMatrixProjectedPrincipalTetrad g
        (curvatureMaxwellMinusProjectorField S qSq)
        (curvatureMaxwellPlusProjectorField S qSq)
        u0 u1 v0 v1 z).2 := by
  obtain ⟨hP, hQ, hPQ, _⟩ :=
    curvatureMaxwellPrincipalProjectorFields_structural
      S qSq z (hqSqPos z hz) hSq
  let q := positiveMaxwellMagnitudeFromSquare qSq z
  have hPself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin'
        (curvatureMaxwellMinusProjectorField S qSq z)) := by
    rw [show Matrix.toLin'
        (curvatureMaxwellMinusProjectorField S qSq z) =
          maxwellMinusProjector (Matrix.toLin' (S z)) q by
      simpa [curvatureMaxwellMinusProjectorField,
        matrixMaxwellMinusProjectorField, q] using
        matrixMaxwellMinusProjector_toLin' (S z) q]
    exact maxwellMinusProjector_metricSelfAdjoint
      (continuousBilinFormToBilin (g z)) hgsymm
      (Matrix.toLin' (S z)) q hself
  exact smoothMatrixProjectedPrincipalTetrad_pseudoOrthonormal g
    (curvatureMaxwellMinusProjectorField S qSq)
    (curvatureMaxwellPlusProjectorField S qSq)
    u0 u1 v0 v1 z hz hgsymm hP hQ hPself hPQ hL0 hL1 hS0 hS1

/-- In an orthonormal trivialization whose metric is represented by the
standard Minkowski form, the verified curvature tetrad has the exact Lorentz
coframe identity used by Maxwell stress transport. -/
theorem smoothCurvatureMaxwellPrincipalCoframe_lorentz
    {U : Set CurvatureCoordinateSpace4}
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (hmetric : ∀ z ∈ U,
      continuousBilinFormToBilin (g z) = minkowskiBilinForm)
    (hSq : ∀ z ∈ U, S z * S z = qSq z • (1 : Matrix4))
    (hself : ∀ z ∈ U,
      MetricSelfAdjoint (continuousBilinFormToBilin (g z))
        (Matrix.toLin' (S z)))
    (hqSqPos : ∀ z ∈ U, 0 < qSq z)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1)) z) :
    ∀ z ∈ U,
      let T := smoothMatrixProjectedPrincipalTetrad g
        (curvatureMaxwellMinusProjectorField S qSq)
        (curvatureMaxwellPlusProjectorField S qSq)
        u0 u1 v0 v1
      smoothPrincipalCoframeMatrix T z * minkowskiMetric *
          (smoothPrincipalCoframeMatrix T z)ᵀ = minkowskiMetric := by
  intro z hz
  let T := smoothMatrixProjectedPrincipalTetrad g
    (curvatureMaxwellMinusProjectorField S qSq)
    (curvatureMaxwellPlusProjectorField S qSq)
    u0 u1 v0 v1
  apply smoothPrincipalCoframeMatrix_lorentz T z
  have hframe := smoothCurvatureMaxwellPrincipalTetrad_pseudoOrthonormal
    g S qSq u0 u1 v0 v1 z hz
    (by rw [hmetric z hz];
        exact ⟨fun x y => by
          simp [minkowskiBilinForm, minkowskiMetric, Fin.sum_univ_succ]
          ring⟩)
    (hSq z hz) (hself z hz) hqSqPos hL0 hL1 hS0 hS1
  rw [hmetric z hz] at hframe
  exact hframe

namespace PositiveQPhaseIIISeedPairC1Realization

variable {U : Set CurvatureCoordinateSpace4}

/-- **Curvature-principal Phase-III entry.** A smooth residual, positive
reconstructed square, admissible fixed probes, and a local `C¹` complexion
angle produce the complete actual transported-seed realization. -/
noncomputable def ofCurvatureMaxwellProjectorsComplexionAngle
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq theta : CurvatureCoordinateSpace4 → ℝ)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (coupling : ℝ) (hopen : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U)
    (hS : MatrixFieldContDiffOn 2 U S)
    (hqSq : ContDiffOn ℝ 2 qSq U)
    (hqSqPos : ∀ z ∈ U, 0 < qSq z)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1)) z)
    (htheta : ContDiffOn ℝ 1 theta U) :
    let T := smoothMatrixProjectedPrincipalTetrad g
      (curvatureMaxwellMinusProjectorField S qSq)
      (curvatureMaxwellPlusProjectorField S qSq)
      u0 u1 v0 v1
    PositiveQPhaseIIISeedPairC1Realization
      (PositiveQPhaseIIIPatch4.ofActualComplexionAngle
        (smoothPrincipalCoframeMatrix T)
        (positiveMaxwellMagnitudeFromSquare qSq)
        theta coupling hopen htheta) := by
  let P := curvatureMaxwellMinusProjectorField S qSq
  let Q := curvatureMaxwellPlusProjectorField S qSq
  let T := smoothMatrixProjectedPrincipalTetrad g P Q u0 u1 v0 v1
  obtain ⟨hP, hQ⟩ :=
    contDiffOn_curvatureMaxwellPrincipalProjectorFields hS hqSq hqSqPos
  have hT : ContDiffOn ℝ 2 T U :=
    contDiffOn_smoothMatrixProjectedPrincipalTetrad u0 u1 v0 v1
      hg hP hQ hL0 hL1 hS0 hS1
  exact ofActualSmoothPrincipalTetradComplexionAngle T
    (positiveMaxwellMagnitudeFromSquare qSq) theta coupling hopen hT
    (contDiffOn_positiveMaxwellMagnitudeFromSquare hqSq hqSqPos)
    (fun z hz => positiveMaxwellMagnitudeFromSquare_pos
      qSq z (hqSqPos z hz)) htheta

/-- A smooth coefficient pair on the positive-cosine chart canonically
supplies the local ratio angle required by the curvature-principal
constructor. When the supplied pair is unit, the preceding cosine/sine
theorems show that the generated coefficients recover it exactly. -/
noncomputable def ofCurvatureMaxwellProjectorsPositiveCosineComplexion
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq c s : CurvatureCoordinateSpace4 → ℝ)
    (u0 u1 v0 v1 : CurvatureCoordinateSpace4)
    (coupling : ℝ) (hopen : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U)
    (hS : MatrixFieldContDiffOn 2 U S)
    (hqSq : ContDiffOn ℝ 2 qSq U)
    (hqSqPos : ∀ z ∈ U, 0 < qSq z)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellMinusProjectorField S qSq) u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellMinusProjectorField S qSq) u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0)
      (smoothMatrixProjectedVector
        (curvatureMaxwellPlusProjectorField S qSq) v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v0)
        (smoothMatrixProjectedVector
          (curvatureMaxwellPlusProjectorField S qSq) v1)) z)
    (hc : ContDiffOn ℝ 1 c U) (hs : ContDiffOn ℝ 1 s U)
    (hcpos : ∀ z ∈ U, 0 < c z) :
    let T := smoothMatrixProjectedPrincipalTetrad g
      (curvatureMaxwellMinusProjectorField S qSq)
      (curvatureMaxwellPlusProjectorField S qSq)
      u0 u1 v0 v1
    PositiveQPhaseIIISeedPairC1Realization
      (PositiveQPhaseIIIPatch4.ofActualComplexionAngle
        (smoothPrincipalCoframeMatrix T)
        (positiveMaxwellMagnitudeFromSquare qSq)
        (positiveCosineComplexionAngle c s)
        coupling hopen
          (contDiffOn_positiveCosineComplexionAngle hc hs hcpos)) := by
  exact ofCurvatureMaxwellProjectorsComplexionAngle g S qSq
    (positiveCosineComplexionAngle c s) u0 u1 v0 v1 coupling hopen
    hg hS hqSq hqSqPos hL0 hL1 hS0 hS1
    (contDiffOn_positiveCosineComplexionAngle hc hs hcpos)

end PositiveQPhaseIIISeedPairC1Realization

end RainichKaluza
