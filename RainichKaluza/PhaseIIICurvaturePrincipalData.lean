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

/-- An idempotent real coordinate matrix with trace one has a rank-one
linear-map range.  This turns the detector's directly checkable polynomial
projector identities into the geometric rank certificate used by finite
eigenline selection. -/
theorem matrixProjector_finrank_range_eq_one_of_trace_one
    (P : Matrix4) (hP : P * P = P) (htrace : Matrix.trace P = 1) :
    Module.finrank ℝ (Matrix.toLin' P).range = 1 := by
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    rw [isIdempotentElem_iff]
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hP
  have hlinTrace :
      LinearMap.trace ℝ CurvatureCoordinateSpace4 (Matrix.toLin' P) = 1 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 4))]
    simpa using htrace
  have hproj :=
    LinearMap.IsIdempotentElem.isProj_range (Matrix.toLin' P) hidem
  have hfinTrace :
      LinearMap.trace ℝ CurvatureCoordinateSpace4 (Matrix.toLin' P) =
        (Module.finrank ℝ (Matrix.toLin' P).range : ℝ) := hproj.trace
  have hcast : (Module.finrank ℝ (Matrix.toLin' P).range : ℝ) = 1 := by
    rw [← hfinTrace]
    exact hlinTrace
  exact_mod_cast hcast

/-- Coordinate specialization of finite rank-one timelike-line selection.
If the projector range is intrinsically timelike, one of the four projected
coordinate directions has the strict negative sign required by scalar
normalization. -/
theorem exists_smoothMatrixProjectedBasisTimelikeScalarSignAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hrank : Module.finrank ℝ (Matrix.toLin' (P z)).range = 1)
    (htimelike : ∀ x : (Matrix.toLin' (P z)).range,
      (x : CurvatureCoordinateSpace4) ≠ 0 →
      continuousBilinFormToBilin (g z)
        (x : CurvatureCoordinateSpace4) (x : CurvatureCoordinateSpace4) < 0) :
    ∃ i : Fin 4,
      smoothMetricPairing g
        (smoothMatrixProjectedVector P (curvatureCoordinateDirection i))
        (smoothMatrixProjectedVector P (curvatureCoordinateDirection i)) z < 0 := by
  let gb := continuousBilinFormToBilin (g z)
  let Plin := Matrix.toLin' (P z)
  obtain ⟨i, hi⟩ :=
    exists_projectedBasisTimelikeVector_of_rankOneRange gb
      (Pi.basisFun ℝ (Fin 4)) Plin hrank htimelike
  refine ⟨i, ?_⟩
  have hcoord : curvatureCoordinateDirection i = Pi.single i 1 := by
    funext k
    simp [curvatureCoordinateDirection, Pi.single_apply]
  have hx : smoothMatrixProjectedVector P
      (curvatureCoordinateDirection i) z =
      Plin ((Pi.basisFun ℝ (Fin 4)) i) := by
    ext k
    simp [Plin, smoothMatrixProjectedVector, hcoord,
      Matrix.toLin'_apply, Pi.basisFun_apply]
  change (g z)
    (smoothMatrixProjectedVector P (curvatureCoordinateDirection i) z)
    (smoothMatrixProjectedVector P (curvatureCoordinateDirection i) z) < 0
  rw [hx]
  exact hi

/-- Coordinate specialization of finite rank-one spacelike-line selection. -/
theorem exists_smoothMatrixProjectedBasisSpacelikeScalarSignAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hrank : Module.finrank ℝ (Matrix.toLin' (P z)).range = 1)
    (hspacelike : ∀ x : (Matrix.toLin' (P z)).range,
      (x : CurvatureCoordinateSpace4) ≠ 0 →
      0 < continuousBilinFormToBilin (g z)
        (x : CurvatureCoordinateSpace4) (x : CurvatureCoordinateSpace4)) :
    ∃ i : Fin 4,
      0 < smoothMetricPairing g
        (smoothMatrixProjectedVector P (curvatureCoordinateDirection i))
        (smoothMatrixProjectedVector P (curvatureCoordinateDirection i)) z := by
  let gb := continuousBilinFormToBilin (g z)
  let Plin := Matrix.toLin' (P z)
  obtain ⟨i, hi⟩ :=
    exists_projectedBasisSpacelikeVector_of_rankOneRange gb
      (Pi.basisFun ℝ (Fin 4)) Plin hrank hspacelike
  refine ⟨i, ?_⟩
  have hcoord : curvatureCoordinateDirection i = Pi.single i 1 := by
    funext k
    simp [curvatureCoordinateDirection, Pi.single_apply]
  have hx : smoothMatrixProjectedVector P
      (curvatureCoordinateDirection i) z =
      Plin ((Pi.basisFun ℝ (Fin 4)) i) := by
    ext k
    simp [Plin, smoothMatrixProjectedVector, hcoord,
      Matrix.toLin'_apply, Pi.basisFun_apply]
  change 0 < (g z)
    (smoothMatrixProjectedVector P (curvatureCoordinateDirection i) z)
    (smoothMatrixProjectedVector P (curvatureCoordinateDirection i) z)
  rw [hx]
  exact hi

/-- **Finite scalar-eigenline entrance.** Two intrinsic rank-one causal-line
certificates select coordinate probes for both scalar Ricci eigenlines, and
the two strict normalization signs persist simultaneously near the base
point.  No preferred scalar probe occurs in the hypotheses. -/
theorem exists_eventually_smoothMatrixProjectedBasisScalarEigenlineSignsAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (PA PB : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hPA : ∀ a b, ContinuousAt (fun w => PA w a b) z)
    (hPB : ∀ a b, ContinuousAt (fun w => PB w a b) z)
    (hPAidem : PA z * PA z = PA z)
    (hPBidem : PB z * PB z = PB z)
    (htraceA : Matrix.trace (PA z) = 1)
    (htraceB : Matrix.trace (PB z) = 1)
    (htimelike : ∀ x : (Matrix.toLin' (PA z)).range,
      (x : CurvatureCoordinateSpace4) ≠ 0 →
      continuousBilinFormToBilin (g z)
        (x : CurvatureCoordinateSpace4) (x : CurvatureCoordinateSpace4) < 0)
    (hspacelike : ∀ x : (Matrix.toLin' (PB z)).range,
      (x : CurvatureCoordinateSpace4) ≠ 0 →
      0 < continuousBilinFormToBilin (g z)
        (x : CurvatureCoordinateSpace4) (x : CurvatureCoordinateSpace4)) :
    ∃ i j : Fin 4,
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g
            (smoothMatrixProjectedVector PA (curvatureCoordinateDirection i))
            (smoothMatrixProjectedVector PA (curvatureCoordinateDirection i)) w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMatrixProjectedVector PB (curvatureCoordinateDirection j))
            (smoothMatrixProjectedVector PB (curvatureCoordinateDirection j)) w := by
  have hrankA : Module.finrank ℝ (Matrix.toLin' (PA z)).range = 1 :=
    matrixProjector_finrank_range_eq_one_of_trace_one (PA z) hPAidem htraceA
  have hrankB : Module.finrank ℝ (Matrix.toLin' (PB z)).range = 1 :=
    matrixProjector_finrank_range_eq_one_of_trace_one (PB z) hPBidem htraceB
  obtain ⟨i, hi⟩ :=
    exists_smoothMatrixProjectedBasisTimelikeScalarSignAt
      g PA z hrankA htimelike
  obtain ⟨j, hj⟩ :=
    exists_smoothMatrixProjectedBasisSpacelikeScalarSignAt
      g PB z hrankB hspacelike
  let x := smoothMatrixProjectedVector PA (curvatureCoordinateDirection i)
  let y := smoothMatrixProjectedVector PB (curvatureCoordinateDirection j)
  have hx : ContinuousAt x z := by
    apply continuousAt_pi.mpr
    intro k
    simp only [x, smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum Finset.univ fun l _ =>
      (hPA k l).mul continuousAt_const
  have hy : ContinuousAt y z := by
    apply continuousAt_pi.mpr
    intro k
    simp only [y, smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum Finset.univ fun l _ =>
      (hPB k l).mul continuousAt_const
  have hxx := continuousAt_smoothMetricPairing hg hx hx
  have hyy := continuousAt_smoothMetricPairing hg hy hy
  refine ⟨i, j, ?_⟩
  filter_upwards
    [hxx.eventually_lt continuousAt_const hi,
      continuousAt_const.eventually_lt hyy hj] with w hwA hwB
  exact ⟨hwA, hwB⟩

/-- **Coordinate-matrix specialization of the arbitrary-basis Lorentzian
entrance.** At any point where the matrix projector has rank-two range
containing a timelike vector, the finite coordinate-basis/pivot-recipe search
supplies exactly the two strict signs consumed by the field-driven
Gram--Schmidt constructor. -/
theorem exists_smoothMatrixProjectedBasisLorentzianFrameSignsAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hrank : Module.finrank ℝ (Matrix.toLin' (P z)).range = 2)
    (t : (Matrix.toLin' (P z)).range)
    (ht : continuousBilinFormToBilin (g z) (t : CurvatureCoordinateSpace4)
      (t : CurvatureCoordinateSpace4) < 0) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe,
      let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
      let pivot := smoothLorentzianPivotCandidate g x y recipe
      let companion := smoothLorentzianPivotCompanion x y recipe
      smoothMetricPairing g pivot pivot z < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g pivot companion)
          (smoothMetricOrthogonalizeSecond g pivot companion) z := by
  let gb := continuousBilinFormToBilin (g z)
  let Plin := Matrix.toLin' (P z)
  obtain ⟨i, j, recipe, htime, hrem⟩ :=
    exists_projectedBasisLorentzianFrameSigns gb hgsymm hindex
      (Pi.basisFun ℝ (Fin 4)) Plin hrank t ht
  let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
  let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
  let pivot := smoothLorentzianPivotCandidate g x y recipe
  let companion := smoothLorentzianPivotCompanion x y recipe
  have hcoord (n : Fin 4) :
      curvatureCoordinateDirection n = Pi.single n 1 := by
    funext k
    simp [curvatureCoordinateDirection, Pi.single_apply]
  have hxz : x z = Plin ((Pi.basisFun ℝ (Fin 4)) i) := by
    ext k
    simp [x, Plin, smoothMatrixProjectedVector, hcoord,
      Matrix.toLin'_apply, Pi.basisFun_apply]
  have hyz : y z = Plin ((Pi.basisFun ℝ (Fin 4)) j) := by
    ext k
    simp [y, Plin, smoothMatrixProjectedVector, hcoord,
      Matrix.toLin'_apply, Pi.basisFun_apply]
  have hpivot : pivot z = lorentzianPivotCandidate gb
      (Plin ((Pi.basisFun ℝ (Fin 4)) i))
      (Plin ((Pi.basisFun ℝ (Fin 4)) j)) recipe := by
    cases recipe <;>
      simp [pivot, smoothLorentzianPivotCandidate,
        smoothMetricPairing, gb, continuousBilinFormToBilin, hxz, hyz,
        lorentzianPivotCandidate]
  have hcompanion : companion z = lorentzianPivotCompanion
      (Plin ((Pi.basisFun ℝ (Fin 4)) i))
      (Plin ((Pi.basisFun ℝ (Fin 4)) j)) recipe := by
    cases recipe <;>
      simp [companion, smoothLorentzianPivotCompanion, hxz, hyz,
        lorentzianPivotCompanion]
  refine ⟨i, j, recipe, ?_, ?_⟩
  · change (g z) (pivot z) (pivot z) < 0
    rw [hpivot]
    exact htime
  · have horth : smoothMetricOrthogonalizeSecond g pivot companion z =
        metricOrthogonalizeSecond gb
          (lorentzianPivotCandidate gb
            (Plin ((Pi.basisFun ℝ (Fin 4)) i))
            (Plin ((Pi.basisFun ℝ (Fin 4)) j)) recipe)
          (lorentzianPivotCompanion
            (Plin ((Pi.basisFun ℝ (Fin 4)) i))
            (Plin ((Pi.basisFun ℝ (Fin 4)) j)) recipe) := by
      simp [smoothMetricOrthogonalizeSecond, metricOrthogonalizeSecond,
        smoothMetricPairing, gb, continuousBilinFormToBilin,
        hpivot, hcompanion]
    change 0 < (g z)
      (smoothMetricOrthogonalizeSecond g pivot companion z)
      (smoothMetricOrthogonalizeSecond g pivot companion z)
    rw [horth]
    exact hrem

/-- **Local coordinate-matrix Lorentzian entrance.** Under pointwise
continuity of the actual metric and projector entries, the arbitrary-chart
finite search selects one pair and one pivot recipe whose two strict
Lorentzian frame signs persist on a neighborhood of the base point. -/
theorem exists_eventually_smoothMatrixProjectedBasisLorentzianFrameSignsAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hP : ∀ a b, ContinuousAt (fun w => P w a b) z)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hrank : Module.finrank ℝ (Matrix.toLin' (P z)).range = 2)
    (t : (Matrix.toLin' (P z)).range)
    (ht : continuousBilinFormToBilin (g z) (t : CurvatureCoordinateSpace4)
      (t : CurvatureCoordinateSpace4) < 0) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe,
      let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
      let pivot := smoothLorentzianPivotCandidate g x y recipe
      let companion := smoothLorentzianPivotCompanion x y recipe
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g pivot pivot w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g pivot companion)
            (smoothMetricOrthogonalizeSecond g pivot companion) w := by
  obtain ⟨i, j, recipe, htime, hrem⟩ :=
    exists_smoothMatrixProjectedBasisLorentzianFrameSignsAt
      g P z hgsymm hindex hrank t ht
  let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
  let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
  have hx : ContinuousAt x z := by
    apply continuousAt_pi.mpr
    intro k
    simp only [x, smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum Finset.univ fun l _ =>
      (hP k l).mul continuousAt_const
  have hy : ContinuousAt y z := by
    apply continuousAt_pi.mpr
    intro k
    simp only [y, smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum Finset.univ fun l _ =>
      (hP k l).mul continuousAt_const
  exact ⟨i, j, recipe,
    eventually_smoothLorentzianPivotFrameSigns recipe hg hx hy htime hrem⟩

/-- Coordinate-matrix specialization of the arbitrary-basis positive-plane
theorem, including persistence of one fixed projected coordinate pair on a
neighborhood. -/
theorem exists_eventually_smoothMatrixProjectedBasisSpacelikeFrameSignsAt
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (Q : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hQ : ∀ a b, ContinuousAt (fun w => Q w a b) z)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hrank : Module.finrank ℝ (Matrix.toLin' (Q z)).range = 2)
    (t : CurvatureCoordinateSpace4)
    (ht : continuousBilinFormToBilin (g z) t t < 0)
    (horth : ∀ v : (Matrix.toLin' (Q z)).range,
      continuousBilinFormToBilin (g z) t
        (v : CurvatureCoordinateSpace4) = 0) :
    ∃ i j : Fin 4,
      let x := smoothMatrixProjectedVector Q (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector Q (curvatureCoordinateDirection j)
      ∀ᶠ w in 𝓝 z,
        0 < smoothMetricPairing g x x w ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g x y)
            (smoothMetricOrthogonalizeSecond g x y) w := by
  let gb := continuousBilinFormToBilin (g z)
  let Qlin := Matrix.toLin' (Q z)
  obtain ⟨i, j, hspace, hrem⟩ :=
    exists_projectedBasisSpacelikeFrameSigns
      gb hindex (Pi.basisFun ℝ (Fin 4)) Qlin hrank t ht horth
  let x := smoothMatrixProjectedVector Q (curvatureCoordinateDirection i)
  let y := smoothMatrixProjectedVector Q (curvatureCoordinateDirection j)
  have hcoord (n : Fin 4) :
      curvatureCoordinateDirection n = Pi.single n 1 := by
    funext k
    simp [curvatureCoordinateDirection, Pi.single_apply]
  have hxz : x z = Qlin ((Pi.basisFun ℝ (Fin 4)) i) := by
    ext k
    simp [x, Qlin, smoothMatrixProjectedVector, hcoord,
      Matrix.toLin'_apply, Pi.basisFun_apply]
  have hyz : y z = Qlin ((Pi.basisFun ℝ (Fin 4)) j) := by
    ext k
    simp [y, Qlin, smoothMatrixProjectedVector, hcoord,
      Matrix.toLin'_apply, Pi.basisFun_apply]
  have hx : ContinuousAt x z := by
    apply continuousAt_pi.mpr
    intro k
    simp only [x, smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum Finset.univ fun l _ =>
      (hQ k l).mul continuousAt_const
  have hy : ContinuousAt y z := by
    apply continuousAt_pi.mpr
    intro k
    simp only [y, smoothMatrixProjectedVector, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum Finset.univ fun l _ =>
      (hQ k l).mul continuousAt_const
  have hspaceSmooth : 0 < smoothMetricPairing g x x z := by
    change 0 < (g z) (x z) (x z)
    rw [hxz]
    exact hspace
  have horthEq : smoothMetricOrthogonalizeSecond g x y z =
      metricOrthogonalizeSecond gb
        (Qlin ((Pi.basisFun ℝ (Fin 4)) i))
        (Qlin ((Pi.basisFun ℝ (Fin 4)) j)) := by
    simp [smoothMetricOrthogonalizeSecond, metricOrthogonalizeSecond,
      smoothMetricPairing, gb, continuousBilinFormToBilin, hxz, hyz]
  have hremSmooth : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g x y) z := by
    change 0 < (g z)
      (smoothMetricOrthogonalizeSecond g x y z)
      (smoothMetricOrthogonalizeSecond g x y z)
    rw [horthEq]
    exact hrem
  exact ⟨i, j,
    eventually_smoothSpacelikeFrameSigns hg hx hy hspaceSmooth hremSmooth⟩

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

/-- The coordinate matrix test `(G S)ᵀ = G S` is exactly the
metric-self-adjointness condition for the endomorphism represented by `S`. -/
theorem matrixMetricSelfAdjoint_of_mul_transpose_eq
    (G S : Matrix4) (hG : Gᵀ = G)
    (hself : (G * S)ᵀ = G * S) :
    MetricSelfAdjoint (Matrix.toBilin' G) (Matrix.toLin' S) := by
  have hmat : Sᵀ * G = G * S := by
    calc
      Sᵀ * G = Sᵀ * Gᵀ := by rw [hG]
      _ = (G * S)ᵀ := by rw [Matrix.transpose_mul]
      _ = G * S := hself
  have hforms :
      (Matrix.toBilin' G).compLeft (Matrix.toLin' S) =
        (Matrix.toBilin' G).compRight (Matrix.toLin' S) := by
    apply LinearMap.BilinForm.toMatrix'.injective
    simp only [LinearMap.BilinForm.toMatrix'_compLeft,
      LinearMap.BilinForm.toMatrix'_compRight,
      LinearMap.BilinForm.toMatrix'_toBilin', LinearMap.toMatrix'_toLin']
    exact hmat
  intro x y
  change ((Matrix.toBilin' G).compLeft (Matrix.toLin' S)) x y =
    ((Matrix.toBilin' G).compRight (Matrix.toLin' S)) x y
  rw [hforms]

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

/-- **Choice-free physical Maxwell range theorem.** A positive reconstructed
square, the Maxwell square law and trace, and the physical negative-energy
eigendirection force the actual curvature negative-projector matrix to have
rank two and contain a timelike vector.  No detector probe or coframe occurs
in the hypotheses. -/
theorem curvatureMaxwellMinusProjector_rank_two_and_timelike_of_energySign
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hpos : 0 < qSq z)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (htrace : Matrix.trace (S z) = 0)
    (henergy : HasPhysicalMaxwellEnergySign
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (S z))
      (positiveMaxwellMagnitudeFromSquare qSq z)) :
    let P := curvatureMaxwellMinusProjectorField S qSq
    Module.finrank ℝ (Matrix.toLin' (P z)).range = 2 ∧
      ∃ t : (Matrix.toLin' (P z)).range,
        continuousBilinFormToBilin (g z)
          (t : CurvatureCoordinateSpace4)
          (t : CurvatureCoordinateSpace4) < 0 := by
  let q := positiveMaxwellMagnitudeFromSquare qSq z
  let Slin := Matrix.toLin' (S z)
  let P := curvatureMaxwellMinusProjectorField S qSq
  have hqpos : 0 < q :=
    positiveMaxwellMagnitudeFromSquare_pos qSq z hpos
  have hqSq : q ^ 2 = qSq z :=
    positiveMaxwellMagnitudeFromSquare_sq qSq z hpos
  have hSlin : Slin * Slin =
      q ^ 2 • (1 : Module.End ℝ CurvatureCoordinateSpace4) := by
    have h' := congrArg Matrix.toLin' hSq
    rw [Matrix.toLin'_mul] at h'
    simpa [Slin, hqSq, map_smul, Matrix.toLin'_one,
      Module.End.one_eq_id, Module.End.mul_eq_comp] using h'
  have htraceLin : LinearMap.trace ℝ CurvatureCoordinateSpace4 Slin = 0 := by
    simpa [Slin] using htrace
  have hrankRaw : Module.finrank ℝ
      (maxwellMinusProjector Slin q).range = 2 :=
    (maxwellProjectors_finrank_range_eq_two Slin q (ne_of_gt hqpos)
      hSlin (by simp) htraceLin).2
  have hPtoLin : Matrix.toLin' (P z) = maxwellMinusProjector Slin q := by
    simp [P, curvatureMaxwellMinusProjectorField,
      matrixMaxwellMinusProjectorField, Slin, q,
      matrixMaxwellMinusProjector_toLin']
  obtain ⟨t, ht⟩ :=
    exists_timelike_mem_maxwellMinusProjector_range_of_energySign
      (continuousBilinFormToBilin (g z)) Slin q (ne_of_gt hqpos) henergy
  let tP : (Matrix.toLin' (P z)).range :=
    ⟨(t : CurvatureCoordinateSpace4), by
      rw [hPtoLin]
      exact t.property⟩
  refine ⟨?_, tP, ?_⟩
  · rw [hPtoLin]
    exact hrankRaw
  · exact ht

/-- The choice-free physical Maxwell conditions therefore trigger the
pointwise arbitrary-chart finite Lorentzian frame search. -/
theorem exists_smoothMatrixProjectedMaxwellLorentzianFrameSignsAt_of_energySign
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hpos : 0 < qSq z)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (htrace : Matrix.trace (S z) = 0)
    (henergy : HasPhysicalMaxwellEnergySign
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (S z))
      (positiveMaxwellMagnitudeFromSquare qSq z)) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe,
      let P := curvatureMaxwellMinusProjectorField S qSq
      let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
      let pivot := smoothLorentzianPivotCandidate g x y recipe
      let companion := smoothLorentzianPivotCompanion x y recipe
      smoothMetricPairing g pivot pivot z < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g pivot companion)
          (smoothMetricOrthogonalizeSecond g pivot companion) z := by
  obtain ⟨hrank, t, ht⟩ :=
    curvatureMaxwellMinusProjector_rank_two_and_timelike_of_energySign
      g S qSq z hpos hSq htrace henergy
  exact exists_smoothMatrixProjectedBasisLorentzianFrameSignsAt
    g (curvatureMaxwellMinusProjectorField S qSq) z
    hgsymm hindex hrank t ht

/-- Under pointwise continuity of the metric and the curvature projector,
the same choice-free Maxwell hypotheses select one finite coordinate pair
and pivot recipe that retain both strict Lorentzian signs on a neighborhood. -/
theorem exists_eventually_smoothMatrixProjectedMaxwellLorentzianFrameSignsAt_of_energySign
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hP : ∀ a b, ContinuousAt
      (fun w => curvatureMaxwellMinusProjectorField S qSq w a b) z)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hpos : 0 < qSq z)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (htrace : Matrix.trace (S z) = 0)
    (henergy : HasPhysicalMaxwellEnergySign
      (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (S z))
      (positiveMaxwellMagnitudeFromSquare qSq z)) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe,
      let P := curvatureMaxwellMinusProjectorField S qSq
      let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
      let pivot := smoothLorentzianPivotCandidate g x y recipe
      let companion := smoothLorentzianPivotCompanion x y recipe
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g pivot pivot w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g pivot companion)
            (smoothMetricOrthogonalizeSecond g pivot companion) w := by
  obtain ⟨hrank, t, ht⟩ :=
    curvatureMaxwellMinusProjector_rank_two_and_timelike_of_energySign
      g S qSq z hpos hSq htrace henergy
  exact exists_eventually_smoothMatrixProjectedBasisLorentzianFrameSignsAt
    g (curvatureMaxwellMinusProjectorField S qSq) z hg hP
    hgsymm hindex hrank t ht

/-- **Choice-free local Maxwell entrance from positive energy.** The
observer-energy inequality, rather than a supplied eigendirection, selects
the Lorentzian negative principal range.  The finite arbitrary-chart search
then returns one coordinate pair and pivot recipe valid on a neighborhood. -/
theorem exists_eventually_smoothMatrixProjectedMaxwellLorentzianFrameSignsAt_of_positiveEnergy
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hP : ∀ a b, ContinuousAt
      (fun w => curvatureMaxwellMinusProjectorField S qSq w a b) z)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hpos : 0 < qSq z)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (htrace : Matrix.trace (S z) = 0)
    (hself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z)) (Matrix.toLin' (S z)))
    (henergy : HasPositiveMaxwellEnergyDensity
      (continuousBilinFormToBilin (g z)) (Matrix.toLin' (S z))) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe,
      let P := curvatureMaxwellMinusProjectorField S qSq
      let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
      let pivot := smoothLorentzianPivotCandidate g x y recipe
      let companion := smoothLorentzianPivotCompanion x y recipe
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g pivot pivot w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g pivot companion)
            (smoothMetricOrthogonalizeSecond g pivot companion) w := by
  let q := positiveMaxwellMagnitudeFromSquare qSq z
  let Slin := Matrix.toLin' (S z)
  have hqpos : 0 < q :=
    positiveMaxwellMagnitudeFromSquare_pos qSq z hpos
  have hqSq : q ^ 2 = qSq z :=
    positiveMaxwellMagnitudeFromSquare_sq qSq z hpos
  have hSlin : Slin * Slin =
      q ^ 2 • (1 : Module.End ℝ CurvatureCoordinateSpace4) := by
    have h' := congrArg Matrix.toLin' hSq
    rw [Matrix.toLin'_mul] at h'
    simpa [Slin, hqSq, map_smul, Matrix.toLin'_one,
      Module.End.one_eq_id, Module.End.mul_eq_comp] using h'
  have hphysical : HasPhysicalMaxwellEnergySign
      (continuousBilinFormToBilin (g z)) Slin q :=
    hasPhysicalMaxwellEnergySign_of_positiveEnergyDensity
      (continuousBilinFormToBilin (g z)) hgsymm Slin q hqpos
      hSlin hself henergy
  exact
    exists_eventually_smoothMatrixProjectedMaxwellLorentzianFrameSignsAt_of_energySign
      g S qSq z hg hP hgsymm hindex hpos hSq htrace hphysical

/-- **Choice-free local Maxwell principal-frame entrance.** Positive observer
energy selects the Lorentzian negative principal range; the complementary
rank-two range is positive definite by index one.  A single finite
coordinate-basis search therefore selects both principal-plane pairs and a
negative-plane pivot recipe whose four strict Gram--Schmidt signs all persist
on one neighborhood. -/
theorem exists_eventually_smoothMatrixProjectedMaxwellPrincipalFrameSignsAt_of_positiveEnergy
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4)
    (hg : ContinuousAt g z)
    (hP : ∀ a b, ContinuousAt
      (fun w => curvatureMaxwellMinusProjectorField S qSq w a b) z)
    (hQ : ∀ a b, ContinuousAt
      (fun w => curvatureMaxwellPlusProjectorField S qSq w a b) z)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hindex : HasLorentzianIndexOne (continuousBilinFormToBilin (g z)))
    (hpos : 0 < qSq z)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (htrace : Matrix.trace (S z) = 0)
    (hself : MetricSelfAdjoint
      (continuousBilinFormToBilin (g z)) (Matrix.toLin' (S z)))
    (henergy : HasPositiveMaxwellEnergyDensity
      (continuousBilinFormToBilin (g z)) (Matrix.toLin' (S z))) :
    ∃ i j : Fin 4, ∃ recipe : LorentzianPivotRecipe, ∃ k l : Fin 4,
      let P := curvatureMaxwellMinusProjectorField S qSq
      let Q := curvatureMaxwellPlusProjectorField S qSq
      let x := smoothMatrixProjectedVector P (curvatureCoordinateDirection i)
      let y := smoothMatrixProjectedVector P (curvatureCoordinateDirection j)
      let pivot := smoothLorentzianPivotCandidate g x y recipe
      let companion := smoothLorentzianPivotCompanion x y recipe
      let u := smoothMatrixProjectedVector Q (curvatureCoordinateDirection k)
      let v := smoothMatrixProjectedVector Q (curvatureCoordinateDirection l)
      ∀ᶠ w in 𝓝 z,
        smoothMetricPairing g pivot pivot w < 0 ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g pivot companion)
            (smoothMetricOrthogonalizeSecond g pivot companion) w ∧
          0 < smoothMetricPairing g u u w ∧
          0 < smoothMetricPairing g
            (smoothMetricOrthogonalizeSecond g u v)
            (smoothMetricOrthogonalizeSecond g u v) w := by
  let gb := continuousBilinFormToBilin (g z)
  let q := positiveMaxwellMagnitudeFromSquare qSq z
  let Slin := Matrix.toLin' (S z)
  let P := curvatureMaxwellMinusProjectorField S qSq
  let Q := curvatureMaxwellPlusProjectorField S qSq
  have hqpos : 0 < q :=
    positiveMaxwellMagnitudeFromSquare_pos qSq z hpos
  have hqSq : q ^ 2 = qSq z :=
    positiveMaxwellMagnitudeFromSquare_sq qSq z hpos
  have hSlin : Slin * Slin =
      q ^ 2 • (1 : Module.End ℝ CurvatureCoordinateSpace4) := by
    have h' := congrArg Matrix.toLin' hSq
    rw [Matrix.toLin'_mul] at h'
    simpa [Slin, hqSq, map_smul, Matrix.toLin'_one,
      Module.End.one_eq_id, Module.End.mul_eq_comp] using h'
  have htraceLin : LinearMap.trace ℝ CurvatureCoordinateSpace4 Slin = 0 := by
    simpa [Slin] using htrace
  have hphysical : HasPhysicalMaxwellEnergySign gb Slin q :=
    hasPhysicalMaxwellEnergySign_of_positiveEnergyDensity
      gb hgsymm Slin q hqpos hSlin hself henergy
  obtain ⟨hrankPlusRaw, hrankMinusRaw⟩ :=
    maxwellProjectors_finrank_range_eq_two
      Slin q (ne_of_gt hqpos) hSlin (by simp) htraceLin
  have hPtoLin : Matrix.toLin' (P z) = maxwellMinusProjector Slin q := by
    simp [P, curvatureMaxwellMinusProjectorField,
      matrixMaxwellMinusProjectorField, Slin, q,
      matrixMaxwellMinusProjector_toLin']
  have hQtoLin : Matrix.toLin' (Q z) = maxwellPlusProjector Slin q := by
    simp [Q, curvatureMaxwellPlusProjectorField,
      matrixMaxwellPlusProjectorField, Slin, q,
      matrixMaxwellPlusProjector_toLin']
  have hrankPlus : Module.finrank ℝ (Matrix.toLin' (Q z)).range = 2 := by
    rw [hQtoLin]
    exact hrankPlusRaw
  obtain ⟨tRaw, ht⟩ :=
    exists_timelike_mem_maxwellMinusProjector_range_of_energySign
      gb Slin q (ne_of_gt hqpos) hphysical
  let t : (Matrix.toLin' (P z)).range :=
    ⟨(tRaw : CurvatureCoordinateSpace4), by
      rw [hPtoLin]
      exact tRaw.property⟩
  obtain ⟨i, j, recipe, hminus⟩ :=
    exists_eventually_smoothMatrixProjectedBasisLorentzianFrameSignsAt
      g P z hg hP hgsymm hindex
      (by rw [hPtoLin]; exact hrankMinusRaw) t ht
  have hPId : (maxwellMinusProjector Slin q).comp
      (maxwellMinusProjector Slin q) = maxwellMinusProjector Slin q :=
    maxwellMinusProjector_sq Slin q (ne_of_gt hqpos) hSlin
  have hQId : (maxwellPlusProjector Slin q).comp
      (maxwellPlusProjector Slin q) = maxwellPlusProjector Slin q :=
    maxwellPlusProjector_sq Slin q (ne_of_gt hqpos) hSlin
  have hPself : MetricSelfAdjoint gb (maxwellMinusProjector Slin q) :=
    maxwellMinusProjector_metricSelfAdjoint gb hgsymm Slin q hself
  have hPQ : (maxwellMinusProjector Slin q).comp
      (maxwellPlusProjector Slin q) = 0 :=
    maxwellProjectors_comp_zero_rev Slin q (ne_of_gt hqpos) hSlin
  have htFixed : maxwellMinusProjector Slin q
      (tRaw : CurvatureCoordinateSpace4) = tRaw :=
    projector_fixed_of_mem_range _ hPId tRaw tRaw.property
  have horth : ∀ v : (Matrix.toLin' (Q z)).range,
      gb (tRaw : CurvatureCoordinateSpace4)
        (v : CurvatureCoordinateSpace4) = 0 := by
    intro v
    have hvPlus : (v : CurvatureCoordinateSpace4) ∈
        (maxwellPlusProjector Slin q).range := by
      rw [← hQtoLin]
      exact v.property
    have hvFixed : maxwellPlusProjector Slin q
        (v : CurvatureCoordinateSpace4) = v :=
      projector_fixed_of_mem_range _ hQId v hvPlus
    exact complementaryProjector_fixed_orthogonal
      gb _ _ hPself hPQ tRaw v htFixed hvFixed
  obtain ⟨k, l, hplus⟩ :=
    exists_eventually_smoothMatrixProjectedBasisSpacelikeFrameSignsAt
      g Q z hg hQ hindex hrankPlus tRaw ht horth
  refine ⟨i, j, recipe, k, l, ?_⟩
  filter_upwards [hminus, hplus] with w hwMinus hwPlus
  exact ⟨hwMinus.1, hwMinus.2, hwPlus.1, hwPlus.2⟩

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

/-- Field-driven version of principal-tetrad verification.  The four vector
fields need only be fixed by the two complementary projectors at the point;
in particular, the Lorentzian pair may be produced by a finite pivot recipe
rather than by two raw projections. -/
theorem smoothPrincipalTetradFromFields_pseudoOrthonormal_of_projectorFixed
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (P Q : Matrix4)
    (x y u v : CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hself : MetricSelfAdjoint (continuousBilinFormToBilin (g z))
      (Matrix.toLin' P))
    (hPQ : P * Q = 0)
    (hPx : Matrix.toLin' P (x z) = x z)
    (hPy : Matrix.toLin' P (y z) = y z)
    (hQu : Matrix.toLin' Q (u z) = u z)
    (hQv : Matrix.toLin' Q (v z) = v z)
    (hx : smoothMetricPairing g x x z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g x y) z)
    (hu : 0 < smoothMetricPairing g u u z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g u v)
      (smoothMetricOrthogonalizeSecond g u v) z) :
    IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z))
      (smoothPrincipalTetradFromFields g x y u v z).1
      (smoothPrincipalTetradFromFields g x y u v z).2 := by
  let gb := continuousBilinFormToBilin (g z)
  have hPQlin : (Matrix.toLin' P).comp (Matrix.toLin' Q) = 0 := by
    have h' := congrArg Matrix.toLin' hPQ
    rw [Matrix.toLin'_mul] at h'
    simpa using h'
  have hx' : gb (x z) (x z) < 0 := by
    exact hx
  have hy' : 0 < gb (y z) (y z) -
      (gb (x z) (y z)) ^ 2 / gb (x z) (x z) := by
    rw [← metricOrthogonalizeSecond_norm gb hgsymm
      (x z) (y z) (ne_of_lt hx')]
    exact hy
  have hu' : 0 < gb (u z) (u z) := by
    exact hu
  have hv' : 0 < gb (v z) (v z) -
      (gb (u z) (v z)) ^ 2 / gb (u z) (u z) := by
    rw [← metricOrthogonalizeSecond_norm gb hgsymm
      (u z) (v z) (ne_of_gt hu')]
    exact hv
  have hframe := principalPlaneFrames_pseudoOrthonormal_of_fixed
    gb hgsymm (Matrix.toLin' P) (Matrix.toLin' Q)
    hself hPQlin (x z) (y z) (u z) (v z)
    hPx hPy hQu hQv hx' hy' hu' hv'
  simpa [smoothPrincipalTetradFromFields, smoothLorentzianPlaneFrame,
    smoothSpacelikePlaneFrame, smoothNormalizeTimelike,
    smoothNormalizeSpacelike, smoothMetricOrthogonalizeSecond,
    smoothMetricPairing, lorentzianPlaneFrame, spacelikePlaneFrame,
    normalizeTimelike, normalizeSpacelike, metricOrthogonalizeSecond,
    gb, continuousBilinFormToBilin] using hframe

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

/-- Curvature-Maxwell verification for the field-driven tetrad.  This is the
finite-pivot counterpart of the fixed-probe theorem above. -/
theorem smoothCurvatureMaxwellPrincipalTetradFromFields_pseudoOrthonormal
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (S : CurvatureCoordinateSpace4 → Matrix4)
    (qSq : CurvatureCoordinateSpace4 → ℝ)
    (x y u v : CurvatureCoordinateSpace4 → CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (hgsymm : (continuousBilinFormToBilin (g z)).IsSymm)
    (hSq : S z * S z = qSq z • (1 : Matrix4))
    (hself : MetricSelfAdjoint (continuousBilinFormToBilin (g z))
      (Matrix.toLin' (S z)))
    (hqSqPos : 0 < qSq z)
    (hPx : Matrix.toLin'
      (curvatureMaxwellMinusProjectorField S qSq z) (x z) = x z)
    (hPy : Matrix.toLin'
      (curvatureMaxwellMinusProjectorField S qSq z) (y z) = y z)
    (hQu : Matrix.toLin'
      (curvatureMaxwellPlusProjectorField S qSq z) (u z) = u z)
    (hQv : Matrix.toLin'
      (curvatureMaxwellPlusProjectorField S qSq z) (v z) = v z)
    (hx : smoothMetricPairing g x x z < 0)
    (hy : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g x y) z)
    (hu : 0 < smoothMetricPairing g u u z)
    (hv : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g u v)
      (smoothMetricOrthogonalizeSecond g u v) z) :
    IsPseudoOrthonormalPrincipalTetrad
      (continuousBilinFormToBilin (g z))
      (smoothPrincipalTetradFromFields g x y u v z).1
      (smoothPrincipalTetradFromFields g x y u v z).2 := by
  obtain ⟨hP, hQ, hPQ, _⟩ :=
    curvatureMaxwellPrincipalProjectorFields_structural
      S qSq z hqSqPos hSq
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
  exact smoothPrincipalTetradFromFields_pseudoOrthonormal_of_projectorFixed
    g (curvatureMaxwellMinusProjectorField S qSq z)
    (curvatureMaxwellPlusProjectorField S qSq z)
    x y u v z hgsymm hPself hPQ hPx hPy hQu hQv hx hy hu hv

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
