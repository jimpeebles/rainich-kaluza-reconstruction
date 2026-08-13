import RainichKaluza.LorentzFrameTransport
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Explicit frames on Maxwell principal planes

The non-null Maxwell residual determines complementary rank-two principal
planes.  To turn the canonical two-form into a smooth local seed, one needs
orthonormal frames of those planes.  This file gives the constructive algebraic
kernel of that step: indefinite Gram--Schmidt on a Lorentzian two-plane and
ordinary Gram--Schmidt on its positive-definite complement.

The formulas only divide by quantities whose signs are explicit.  Therefore,
once vectors with these sign conditions are selected smoothly on a local
patch, the resulting frame is smooth there.  The actual manifold-level local
selection theorem remains a separate obligation.
-/

namespace RainichKaluza

open LinearMap (BilinForm)
open Module
open scoped Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Remove from `y` its metric component along a non-null vector `x`. -/
noncomputable def metricOrthogonalizeSecond
    (g : BilinForm ℝ V) (x y : V) : V :=
  y - (g x y / g x x) • x

/-- The Gram--Schmidt remainder is orthogonal to its pivot. -/
theorem metricOrthogonalizeSecond_orthogonal
    (g : BilinForm ℝ V) (x y : V) (hx : g x x ≠ 0) :
    g x (metricOrthogonalizeSecond g x y) = 0 := by
  unfold metricOrthogonalizeSecond
  simp only [LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_right]
  field_simp [hx]
  ring

/-- For a symmetric metric, the squared norm of the Gram--Schmidt remainder
is the Schur complement of the pivot entry in the two-vector Gram matrix. -/
theorem metricOrthogonalizeSecond_norm
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hx : g x x ≠ 0) :
    g (metricOrthogonalizeSecond g x y)
        (metricOrthogonalizeSecond g x y) =
      g y y - (g x y) ^ 2 / g x x := by
  unfold metricOrthogonalizeSecond
  simp only [LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hg.eq y x]
  field_simp [hx]
  ring

/-- Unit normalization of a timelike vector. -/
noncomputable def normalizeTimelike (g : BilinForm ℝ V) (x : V) : V :=
  (Real.sqrt (-g x x))⁻¹ • x

/-- A timelike vector normalizes to squared norm `-1`. -/
theorem normalizeTimelike_norm
    (g : BilinForm ℝ V) (x : V) (hx : g x x < 0) :
    g (normalizeTimelike g x) (normalizeTimelike g x) = -1 := by
  have hsqrt_pos : 0 < Real.sqrt (-g x x) := Real.sqrt_pos.2 (by linarith)
  have hsqrt_ne : Real.sqrt (-g x x) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt (-g x x)) ^ 2 = -g x x :=
    Real.sq_sqrt (by linarith)
  unfold normalizeTimelike
  simp only [LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  field_simp [hsqrt_ne]
  nlinarith

/-- Unit normalization of a spacelike vector. -/
noncomputable def normalizeSpacelike (g : BilinForm ℝ V) (x : V) : V :=
  (Real.sqrt (g x x))⁻¹ • x

/-- A spacelike vector normalizes to squared norm `+1`. -/
theorem normalizeSpacelike_norm
    (g : BilinForm ℝ V) (x : V) (hx : 0 < g x x) :
    g (normalizeSpacelike g x) (normalizeSpacelike g x) = 1 := by
  have hsqrt_pos : 0 < Real.sqrt (g x x) := Real.sqrt_pos.2 hx
  have hsqrt_ne : Real.sqrt (g x x) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : (Real.sqrt (g x x)) ^ 2 = g x x :=
    Real.sq_sqrt (le_of_lt hx)
  unfold normalizeSpacelike
  simp only [LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  field_simp [hsqrt_ne]
  nlinarith

/-- Explicit orthonormal frame obtained from a timelike pivot and a second
vector whose Gram--Schmidt remainder is spacelike. -/
noncomputable def lorentzianPlaneFrame
    (g : BilinForm ℝ V) (x y : V) : V × V :=
  (normalizeTimelike g x,
    normalizeSpacelike g (metricOrthogonalizeSecond g x y))

/-- **Lorentzian two-plane frame theorem.** The explicit Gram--Schmidt frame
has metric matrix `diag(-1,1)`. -/
theorem lorentzianPlaneFrame_orthonormal
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hx : g x x < 0)
    (hy : 0 < g y y - (g x y) ^ 2 / g x x) :
    g (lorentzianPlaneFrame g x y).1
        (lorentzianPlaneFrame g x y).1 = -1 ∧
      g (lorentzianPlaneFrame g x y).2
        (lorentzianPlaneFrame g x y).2 = 1 ∧
      g (lorentzianPlaneFrame g x y).1
        (lorentzianPlaneFrame g x y).2 = 0 := by
  have hxne : g x x ≠ 0 := ne_of_lt hx
  have hrem : 0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) := by
    rw [metricOrthogonalizeSecond_norm g hg x y hxne]
    exact hy
  refine ⟨normalizeTimelike_norm g x hx,
    normalizeSpacelike_norm g _ hrem, ?_⟩
  unfold lorentzianPlaneFrame normalizeTimelike normalizeSpacelike
  simp only [LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [metricOrthogonalizeSecond_orthogonal g x y hxne]
  ring

/-- Explicit orthonormal frame obtained from two vectors spanning a
positive-definite two-plane on the selected Gram branch. -/
noncomputable def spacelikePlaneFrame
    (g : BilinForm ℝ V) (x y : V) : V × V :=
  (normalizeSpacelike g x,
    normalizeSpacelike g (metricOrthogonalizeSecond g x y))

/-- **Spacelike two-plane frame theorem.** The explicit Gram--Schmidt frame
has metric matrix `diag(1,1)`. -/
theorem spacelikePlaneFrame_orthonormal
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hx : 0 < g x x)
    (hy : 0 < g y y - (g x y) ^ 2 / g x x) :
    g (spacelikePlaneFrame g x y).1
        (spacelikePlaneFrame g x y).1 = 1 ∧
      g (spacelikePlaneFrame g x y).2
        (spacelikePlaneFrame g x y).2 = 1 ∧
      g (spacelikePlaneFrame g x y).1
        (spacelikePlaneFrame g x y).2 = 0 := by
  have hxne : g x x ≠ 0 := ne_of_gt hx
  have hrem : 0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) := by
    rw [metricOrthogonalizeSecond_norm g hg x y hxne]
    exact hy
  refine ⟨normalizeSpacelike_norm g x hx,
    normalizeSpacelike_norm g _ hrem, ?_⟩
  unfold spacelikePlaneFrame normalizeSpacelike
  simp only [LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [metricOrthogonalizeSecond_orthogonal g x y hxne]
  ring

/-- Self-adjointness of a linear projector with respect to a metric bilinear
form. -/
def MetricSelfAdjoint
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) : Prop :=
  ∀ x y, g (P x) y = g x (P y)

/-- Vectors fixed by complementary projectors are metric-orthogonal whenever
the first projector is self-adjoint and annihilates the range of the second. -/
theorem complementaryProjector_fixed_orthogonal
    (g : BilinForm ℝ V) (P Q : V →ₗ[ℝ] V)
    (hself : MetricSelfAdjoint g P)
    (hPQ : P.comp Q = 0)
    (x y : V) (hx : P x = x) (hy : Q y = y) :
    g x y = 0 := by
  have hPQy : P (Q y) = 0 := by
    have := LinearMap.congr_fun hPQ y
    simpa using this
  calc
    g x y = g (P x) (Q y) := by rw [hx, hy]
    _ = g x (P (Q y)) := hself x (Q y)
    _ = 0 := by rw [hPQy, LinearMap.BilinForm.zero_right]

/-- Metric orthogonalization remains in the range of a projector when both
input vectors lie in that range. -/
theorem metricOrthogonalizeSecond_fixed
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) (x y : V)
    (hx : P x = x) (hy : P y = y) :
    P (metricOrthogonalizeSecond g x y) =
      metricOrthogonalizeSecond g x y := by
  unfold metricOrthogonalizeSecond
  simp only [map_sub, map_smul, hx, hy]

/-- Timelike normalization remains in a projector range. -/
theorem normalizeTimelike_fixed
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) (x : V)
    (hx : P x = x) :
    P (normalizeTimelike g x) = normalizeTimelike g x := by
  unfold normalizeTimelike
  simp only [map_smul, hx]

/-- Spacelike normalization remains in a projector range. -/
theorem normalizeSpacelike_fixed
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) (x : V)
    (hx : P x = x) :
    P (normalizeSpacelike g x) = normalizeSpacelike g x := by
  unfold normalizeSpacelike
  simp only [map_smul, hx]

/-- Both vectors of the Lorentzian Gram--Schmidt frame stay in the selected
projector range. -/
theorem lorentzianPlaneFrame_fixed
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) (x y : V)
    (hx : P x = x) (hy : P y = y) :
    P (lorentzianPlaneFrame g x y).1 =
        (lorentzianPlaneFrame g x y).1 ∧
      P (lorentzianPlaneFrame g x y).2 =
        (lorentzianPlaneFrame g x y).2 := by
  constructor
  · exact normalizeTimelike_fixed g P x hx
  · exact normalizeSpacelike_fixed g P _
      (metricOrthogonalizeSecond_fixed g P x y hx hy)

/-- Both vectors of the spacelike Gram--Schmidt frame stay in the selected
projector range. -/
theorem spacelikePlaneFrame_fixed
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) (x y : V)
    (hx : P x = x) (hy : P y = y) :
    P (spacelikePlaneFrame g x y).1 =
        (spacelikePlaneFrame g x y).1 ∧
      P (spacelikePlaneFrame g x y).2 =
        (spacelikePlaneFrame g x y).2 := by
  constructor
  · exact normalizeSpacelike_fixed g P x hx
  · exact normalizeSpacelike_fixed g P _
      (metricOrthogonalizeSecond_fixed g P x y hx hy)

/-- Every vector in the constructed Lorentzian frame is orthogonal to every
vector in the constructed complementary spacelike frame. -/
theorem principalPlaneFrames_cross_orthogonal
    (g : BilinForm ℝ V) (P Q : V →ₗ[ℝ] V)
    (hself : MetricSelfAdjoint g P) (hPQ : P.comp Q = 0)
    (x0 x1 y0 y1 : V)
    (hx0 : P x0 = x0) (hx1 : P x1 = x1)
    (hy0 : Q y0 = y0) (hy1 : Q y1 = y1) :
    g (lorentzianPlaneFrame g x0 x1).1
        (spacelikePlaneFrame g y0 y1).1 = 0 ∧
      g (lorentzianPlaneFrame g x0 x1).1
        (spacelikePlaneFrame g y0 y1).2 = 0 ∧
      g (lorentzianPlaneFrame g x0 x1).2
        (spacelikePlaneFrame g y0 y1).1 = 0 ∧
      g (lorentzianPlaneFrame g x0 x1).2
        (spacelikePlaneFrame g y0 y1).2 = 0 := by
  obtain ⟨hP0, hP1⟩ :=
    lorentzianPlaneFrame_fixed g P x0 x1 hx0 hx1
  obtain ⟨hQ0, hQ1⟩ :=
    spacelikePlaneFrame_fixed g Q y0 y1 hy0 hy1
  exact ⟨complementaryProjector_fixed_orthogonal g P Q hself hPQ _ _ hP0 hQ0,
    complementaryProjector_fixed_orthogonal g P Q hself hPQ _ _ hP0 hQ1,
    complementaryProjector_fixed_orthogonal g P Q hself hPQ _ _ hP1 hQ0,
    complementaryProjector_fixed_orthogonal g P Q hself hPQ _ _ hP1 hQ1⟩

/-- Applying an idempotent projector produces a vector fixed by that
projector. -/
theorem projector_apply_fixed
    (P : V →ₗ[ℝ] V) (hP : P.comp P = P) (x : V) :
    P (P x) = P x := by
  have := LinearMap.congr_fun hP x
  simpa using this

/-- Lorentzian frame obtained by projecting two ambient probe vectors and
then applying the explicit indefinite Gram--Schmidt formula. -/
noncomputable def projectedLorentzianPlaneFrame
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V) (u0 u1 : V) : V × V :=
  lorentzianPlaneFrame g (P u0) (P u1)

/-- Spacelike frame obtained from two projected ambient probes. -/
noncomputable def projectedSpacelikePlaneFrame
    (g : BilinForm ℝ V) (Q : V →ₗ[ℝ] V) (v0 v1 : V) : V × V :=
  spacelikePlaneFrame g (Q v0) (Q v1)

/-- **Constructive principal-tetrad criterion.** Two fixed pairs of ambient
probe vectors produce a pseudo-orthonormal tetrad whenever their projected
Gram pivots stay on the displayed nondegenerate sign branches. This is the
explicit local formula needed for a smooth principal frame on any patch where
the inequalities persist. -/
theorem projectedPrincipalPlaneFrames_pseudoOrthonormal
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (P Q : V →ₗ[ℝ] V)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (hself : MetricSelfAdjoint g P) (hPQ : P.comp Q = 0)
    (u0 u1 v0 v1 : V)
    (hu0 : g (P u0) (P u0) < 0)
    (hu1 : 0 < g (P u1) (P u1) -
      (g (P u0) (P u1)) ^ 2 / g (P u0) (P u0))
    (hv0 : 0 < g (Q v0) (Q v0))
    (hv1 : 0 < g (Q v1) (Q v1) -
      (g (Q v0) (Q v1)) ^ 2 / g (Q v0) (Q v0)) :
    (g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedLorentzianPlaneFrame g P u0 u1).1 = -1 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).2
          (projectedLorentzianPlaneFrame g P u0 u1).2 = 1 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedLorentzianPlaneFrame g P u0 u1).2 = 0) ∧
    (g (projectedSpacelikePlaneFrame g Q v0 v1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).1 = 1 ∧
      g (projectedSpacelikePlaneFrame g Q v0 v1).2
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 1 ∧
      g (projectedSpacelikePlaneFrame g Q v0 v1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 0) ∧
    (g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).1 = 0 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 0 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).2
          (projectedSpacelikePlaneFrame g Q v0 v1).1 = 0 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).2
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 0) := by
  have hLor := lorentzianPlaneFrame_orthonormal g hg
    (P u0) (P u1) hu0 hu1
  have hSpa := spacelikePlaneFrame_orthonormal g hg
    (Q v0) (Q v1) hv0 hv1
  have hCross := principalPlaneFrames_cross_orthogonal g P Q hself hPQ
    (P u0) (P u1) (Q v0) (Q v1)
    (projector_apply_fixed P hP u0) (projector_apply_fixed P hP u1)
    (projector_apply_fixed Q hQ v0) (projector_apply_fixed Q hQ v1)
  simpa [projectedLorentzianPlaneFrame, projectedSpacelikePlaneFrame] using
    And.intro hLor (And.intro hSpa hCross)

/-- The positive projector polynomial of a metric-self-adjoint involution is
again metric self-adjoint. -/
theorem involutionPlusProjector_metricSelfAdjoint
    (g : BilinForm ℝ V) (hg : g.IsSymm) (J : V →ₗ[ℝ] V)
    (hself : MetricSelfAdjoint g J) :
    MetricSelfAdjoint g (involutionPlusProjector J) := by
  intro x y
  unfold involutionPlusProjector
  simp only [LinearMap.add_apply, Module.End.one_apply,
    LinearMap.smul_apply, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hg.eq x y, hself x y]

/-- The negative projector polynomial is metric self-adjoint as well. -/
theorem involutionMinusProjector_metricSelfAdjoint
    (g : BilinForm ℝ V) (hg : g.IsSymm) (J : V →ₗ[ℝ] V)
    (hself : MetricSelfAdjoint g J) :
    MetricSelfAdjoint g (involutionMinusProjector J) := by
  intro x y
  unfold involutionMinusProjector
  simp only [LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hg.eq x y, hself x y]

/-- For endomorphisms, the algebraic annihilation identity for the two
involution projectors is exactly vanishing composition. -/
theorem involutionProjectors_comp_zero
    (J : V →ₗ[ℝ] V) (hJ : J * J = 1) :
    (involutionPlusProjector J).comp (involutionMinusProjector J) = 0 := by
  exact involutionProjectors_orthogonal J hJ

/-- The two involution projectors annihilate in the reverse order as well. -/
theorem involutionProjectors_comp_zero_rev
    (J : V →ₗ[ℝ] V) (hJ : J * J = 1) :
    (involutionMinusProjector J).comp (involutionPlusProjector J) = 0 := by
  unfold involutionMinusProjector involutionPlusProjector
  change ((2 : ℝ)⁻¹ • (1 - J)) * ((2 : ℝ)⁻¹ • (1 + J)) = 0
  rw [smul_mul_smul]
  have hprod : (1 - J) * (1 + J) = 0 := by
    calc
      (1 - J) * (1 + J) = 1 - J * J := by noncomm_ring
      _ = 0 := by rw [hJ]; noncomm_ring
  rw [hprod, smul_zero]

/-- The positive involution projector is idempotent as a linear map. -/
theorem involutionPlusProjector_comp_self
    (J : V →ₗ[ℝ] V) (hJ : J * J = 1) :
    (involutionPlusProjector J).comp (involutionPlusProjector J) =
      involutionPlusProjector J := by
  exact involutionPlusProjector_sq J hJ

/-- The negative involution projector is idempotent as a linear map. -/
theorem involutionMinusProjector_comp_self
    (J : V →ₗ[ℝ] V) (hJ : J * J = 1) :
    (involutionMinusProjector J).comp (involutionMinusProjector J) =
      involutionMinusProjector J := by
  exact involutionMinusProjector_sq J hJ

/-- Scalar normalization preserves metric self-adjointness of the Maxwell
residual. -/
theorem normalizedMaxwellResidual_metricSelfAdjoint
    (g : BilinForm ℝ V) (S : V →ₗ[ℝ] V) (q : ℝ)
    (hself : MetricSelfAdjoint g S) :
    MetricSelfAdjoint g (normalizedMaxwellResidual S q) := by
  intro x y
  unfold normalizedMaxwellResidual
  simp only [LinearMap.smul_apply, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hself x y]

/-- The curvature-polynomial positive Maxwell projector is metric
self-adjoint whenever the residual is. -/
theorem maxwellPlusProjector_metricSelfAdjoint
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (S : V →ₗ[ℝ] V) (q : ℝ)
    (hself : MetricSelfAdjoint g S) :
    MetricSelfAdjoint g (maxwellPlusProjector S q) :=
  involutionPlusProjector_metricSelfAdjoint g hg _
    (normalizedMaxwellResidual_metricSelfAdjoint g S q hself)

/-- The curvature-polynomial negative Maxwell projector is metric
self-adjoint whenever the residual is. -/
theorem maxwellMinusProjector_metricSelfAdjoint
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (S : V →ₗ[ℝ] V) (q : ℝ)
    (hself : MetricSelfAdjoint g S) :
    MetricSelfAdjoint g (maxwellMinusProjector S q) :=
  involutionMinusProjector_metricSelfAdjoint g hg _
    (normalizedMaxwellResidual_metricSelfAdjoint g S q hself)

/-- The two curvature-polynomial Maxwell principal projectors annihilate one
another on the non-null square-law branch. -/
theorem maxwellProjectors_comp_zero
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V)) :
    (maxwellPlusProjector S q).comp (maxwellMinusProjector S q) = 0 := by
  exact involutionProjectors_comp_zero _
    (normalizedMaxwellResidual_sq S q hq hS)

/-- The two Maxwell principal projectors annihilate in the reverse order. -/
theorem maxwellProjectors_comp_zero_rev
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V)) :
    (maxwellMinusProjector S q).comp (maxwellPlusProjector S q) = 0 := by
  exact involutionProjectors_comp_zero_rev _
    (normalizedMaxwellResidual_sq S q hq hS)

/-- **Maxwell principal-tetrad entry theorem.** On the non-null square-law
branch, the curvature-polynomial projectors satisfy every structural
hypothesis of the constructive principal-tetrad criterion: both are
idempotent, their ranges are mutually orthogonal, and both are metric
self-adjoint. Only the local choice of four probes satisfying the open Gram
sign conditions remains. -/
theorem maxwellPrincipalProjectors_frameHypotheses
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hself : MetricSelfAdjoint g S) :
    (maxwellPlusProjector S q).comp (maxwellPlusProjector S q) =
        maxwellPlusProjector S q ∧
      (maxwellMinusProjector S q).comp (maxwellMinusProjector S q) =
        maxwellMinusProjector S q ∧
      (maxwellPlusProjector S q).comp (maxwellMinusProjector S q) = 0 ∧
      MetricSelfAdjoint g (maxwellPlusProjector S q) ∧
      MetricSelfAdjoint g (maxwellMinusProjector S q) := by
  exact ⟨maxwellPlusProjector_sq S q hq hS,
    maxwellMinusProjector_sq S q hq hS,
    maxwellProjectors_comp_zero S q hq hS,
    maxwellPlusProjector_metricSelfAdjoint g hg S q hself,
    maxwellMinusProjector_metricSelfAdjoint g hg S q hself⟩

/-- **Local persistence of the principal-frame branch.** The four strict Gram
sign conditions used by the projected-probe construction persist in a
neighborhood whenever their scalar functions are continuous. This is the
topological step that lets one fixed probe choice define a frame on a patch
rather than only at a single point. -/
theorem principalGramSigns_eventually
    {X : Type*} [TopologicalSpace X] (x0 : X)
    (lorentzPivot lorentzRemainder spacePivot spaceRemainder : X → ℝ)
    (hLorentzPivot : ContinuousAt lorentzPivot x0)
    (hLorentzRemainder : ContinuousAt lorentzRemainder x0)
    (hSpacePivot : ContinuousAt spacePivot x0)
    (hSpaceRemainder : ContinuousAt spaceRemainder x0)
    (h0 : lorentzPivot x0 < 0)
    (h1 : 0 < lorentzRemainder x0)
    (h2 : 0 < spacePivot x0)
    (h3 : 0 < spaceRemainder x0) :
    ∀ᶠ x in 𝓝 x0,
      lorentzPivot x < 0 ∧
      0 < lorentzRemainder x ∧
      0 < spacePivot x ∧
      0 < spaceRemainder x := by
  filter_upwards
    [hLorentzPivot.eventually_lt continuousAt_const h0,
      continuousAt_const.eventually_lt hLorentzRemainder h1,
      continuousAt_const.eventually_lt hSpacePivot h2,
      continuousAt_const.eventually_lt hSpaceRemainder h3] with x hx0 hx1 hx2 hx3
  exact ⟨hx0, hx1, hx2, hx3⟩

/-- Determinant of the symmetric two-vector Gram matrix. -/
def metricGramDet (g : BilinForm ℝ V) (x y : V) : ℝ :=
  g x x * g y y - (g x y) ^ 2

/-- A finite algebraic recipe for extracting a timelike pivot from a pair
whose two-by-two Gram determinant is negative.  The two weighted recipes are
the rows of an elementary adjugate construction; the final sum/difference
recipes cover the case in which both supplied vectors are null. -/
inductive LorentzianPivotRecipe where
  | first
  | second
  | firstWeighted
  | secondWeighted
  | sum
  | difference
  deriving DecidableEq, Fintype

/-- Candidate timelike vector associated with one finite pivot recipe. -/
def lorentzianPivotCandidate
    (g : BilinForm ℝ V) (x y : V) : LorentzianPivotRecipe → V
  | .first => x
  | .second => y
  | .firstWeighted => (g x y) • x - (g x x) • y
  | .secondWeighted => (g y y) • x - (g x y) • y
  | .sum => x + y
  | .difference => x - y

/-- Companion vector retained for Gram--Schmidt after selecting a finite
timelike pivot candidate. -/
def lorentzianPivotCompanion
    (x y : V) : LorentzianPivotRecipe → V
  | .first => y
  | .second => x
  | .firstWeighted => x
  | .secondWeighted => y
  | .sum => x
  | .difference => x

/-- The first weighted pivot has norm `g(x,x)` times the original Gram
determinant. -/
theorem lorentzianPivotCandidate_firstWeighted_norm
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V) :
    g (lorentzianPivotCandidate g x y .firstWeighted)
        (lorentzianPivotCandidate g x y .firstWeighted) =
      g x x * metricGramDet g x y := by
  simp only [lorentzianPivotCandidate, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hg.eq y x]
  unfold metricGramDet
  ring

/-- The second weighted pivot has norm `g(y,y)` times the original Gram
determinant. -/
theorem lorentzianPivotCandidate_secondWeighted_norm
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V) :
    g (lorentzianPivotCandidate g x y .secondWeighted)
        (lorentzianPivotCandidate g x y .secondWeighted) =
      g y y * metricGramDet g x y := by
  simp only [lorentzianPivotCandidate, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  rw [hg.eq y x]
  unfold metricGramDet
  ring

/-- The finite pivot recipes preserve the negative Gram determinant with the
displayed companion, up to a positive square in the weighted cases. -/
theorem lorentzianPivotCandidate_gramDet
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (recipe : LorentzianPivotRecipe) :
    metricGramDet g (lorentzianPivotCandidate g x y recipe)
        (lorentzianPivotCompanion x y recipe) =
      match recipe with
      | .first => metricGramDet g x y
      | .second => metricGramDet g x y
      | .firstWeighted => (g x x) ^ 2 * metricGramDet g x y
      | .secondWeighted => (g y y) ^ 2 * metricGramDet g x y
      | .sum => metricGramDet g x y
      | .difference => metricGramDet g x y := by
  cases recipe <;>
    simp only [lorentzianPivotCandidate, lorentzianPivotCompanion,
      metricGramDet, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right] <;>
    rw [hg.eq y x] <;> ring

/-- **Finite Lorentzian pivot theorem.** A pair with negative Gram
determinant always yields, from six explicit algebraic recipes, a timelike
pivot whose retained companion still has negative Gram determinant.  This is
the finite replacement for assuming that an individual coordinate-basis
projection is timelike. -/
theorem exists_lorentzianPivotRecipe_of_gramDet_neg
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hdet : metricGramDet g x y < 0) :
    ∃ recipe : LorentzianPivotRecipe,
      g (lorentzianPivotCandidate g x y recipe)
          (lorentzianPivotCandidate g x y recipe) < 0 ∧
      metricGramDet g (lorentzianPivotCandidate g x y recipe)
          (lorentzianPivotCompanion x y recipe) < 0 := by
  by_cases hx : g x x < 0
  · refine ⟨.first, hx, ?_⟩
    simpa [lorentzianPivotCandidate_gramDet g hg x y .first] using hdet
  by_cases hy : g y y < 0
  · refine ⟨.second, hy, ?_⟩
    simpa [lorentzianPivotCandidate_gramDet g hg x y .second] using hdet
  have hxnonneg : 0 ≤ g x x := le_of_not_gt hx
  have hynonneg : 0 ≤ g y y := le_of_not_gt hy
  by_cases hxp : 0 < g x x
  · refine ⟨.firstWeighted, ?_, ?_⟩
    · rw [lorentzianPivotCandidate_firstWeighted_norm g hg x y]
      exact mul_neg_of_pos_of_neg hxp hdet
    · rw [lorentzianPivotCandidate_gramDet g hg x y .firstWeighted]
      exact mul_neg_of_pos_of_neg (sq_pos_of_pos hxp) hdet
  have hxzero : g x x = 0 := le_antisymm (le_of_not_gt hxp) hxnonneg
  by_cases hyp : 0 < g y y
  · refine ⟨.secondWeighted, ?_, ?_⟩
    · rw [lorentzianPivotCandidate_secondWeighted_norm g hg x y]
      exact mul_neg_of_pos_of_neg hyp hdet
    · rw [lorentzianPivotCandidate_gramDet g hg x y .secondWeighted]
      exact mul_neg_of_pos_of_neg (sq_pos_of_pos hyp) hdet
  have hyzero : g y y = 0 := le_antisymm (le_of_not_gt hyp) hynonneg
  have hxyne : g x y ≠ 0 := by
    intro hzero
    simp [metricGramDet, hxzero, hyzero, hzero] at hdet
  by_cases hxy : g x y < 0
  · refine ⟨.sum, ?_, ?_⟩
    · simp only [lorentzianPivotCandidate, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.add_right]
      rw [hg.eq y x, hxzero, hyzero]
      linarith
    · simpa [lorentzianPivotCandidate_gramDet g hg x y .sum] using hdet
  · have hxypos : 0 < g x y := lt_of_le_of_ne (le_of_not_gt hxy) hxyne.symm
    refine ⟨.difference, ?_, ?_⟩
    · simp only [lorentzianPivotCandidate, LinearMap.BilinForm.sub_left,
        LinearMap.BilinForm.sub_right]
      rw [hg.eq y x, hxzero, hyzero]
      linarith
    · simpa [lorentzianPivotCandidate_gramDet g hg x y .difference] using hdet

/-- The squared norm of the Gram--Schmidt remainder is the Gram determinant
divided by the pivot norm. -/
theorem metricOrthogonalizeSecond_norm_eq_gramDet_div
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hx : g x x ≠ 0) :
    g (metricOrthogonalizeSecond g x y)
        (metricOrthogonalizeSecond g x y) =
      metricGramDet g x y / g x x := by
  rw [metricOrthogonalizeSecond_norm g hg x y hx]
  unfold metricGramDet
  field_simp [hx]

/-- A negative pivot and negative Gram determinant give a positive
Gram--Schmidt remainder, the invariant Lorentzian two-plane criterion. -/
theorem metricOrthogonalizeSecond_pos_of_lorentzianGram
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hx : g x x < 0) (hdet : metricGramDet g x y < 0) :
    0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) := by
  rw [metricOrthogonalizeSecond_norm_eq_gramDet_div g hg x y
    (ne_of_lt hx)]
  exact div_pos_of_neg_of_neg hdet hx

/-- A positive pivot and positive Gram determinant give a positive remainder,
the invariant positive-definite two-plane criterion. -/
theorem metricOrthogonalizeSecond_pos_of_spacelikeGram
    (g : BilinForm ℝ V) (hg : g.IsSymm) (x y : V)
    (hx : 0 < g x x) (hdet : 0 < metricGramDet g x y) :
    0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) := by
  rw [metricOrthogonalizeSecond_norm_eq_gramDet_div g hg x y
    (ne_of_gt hx)]
  exact div_pos hdet hx

/-- Operational index-one Lorentz signature condition: every nonzero vector
orthogonal to a timelike vector is spacelike. -/
def HasLorentzianIndexOne (g : BilinForm ℝ V) : Prop :=
  ∀ t z, g t t < 0 → g t z = 0 → z ≠ 0 → 0 < g z z

/-- Two vectors are noncollinear when the second is no scalar multiple of the
first. -/
def NoncollinearPair (x y : V) : Prop :=
  ∀ a : ℝ, y ≠ a • x

/-- The Gram--Schmidt remainder of a noncollinear pair is nonzero. -/
theorem metricOrthogonalizeSecond_ne_zero_of_noncollinear
    (g : BilinForm ℝ V) (x y : V) (hxy : NoncollinearPair x y) :
    metricOrthogonalizeSecond g x y ≠ 0 := by
  intro hzero
  apply hxy (g x y / g x x)
  exact sub_eq_zero.mp hzero

/-- Orthogonality to a third vector is preserved when removing the component
of `y` along `x`. -/
theorem metricOrthogonalizeSecond_orthogonal_of_both
    (g : BilinForm ℝ V) (t x y : V)
    (htx : g t x = 0) (hty : g t y = 0) :
    g t (metricOrthogonalizeSecond g x y) = 0 := by
  unfold metricOrthogonalizeSecond
  simp only [LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_right, htx, hty, mul_zero, sub_zero]

/-- On an index-one metric space, a timelike noncollinear pair automatically
satisfies the positive-remainder condition needed by indefinite
Gram--Schmidt. -/
theorem lorentzianPlaneFrame_orthonormal_of_indexOne
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (x y : V) (hx : g x x < 0) (hxy : NoncollinearPair x y) :
    g (lorentzianPlaneFrame g x y).1
        (lorentzianPlaneFrame g x y).1 = -1 ∧
      g (lorentzianPlaneFrame g x y).2
        (lorentzianPlaneFrame g x y).2 = 1 ∧
      g (lorentzianPlaneFrame g x y).1
        (lorentzianPlaneFrame g x y).2 = 0 := by
  have hxne : g x x ≠ 0 := ne_of_lt hx
  have hremne := metricOrthogonalizeSecond_ne_zero_of_noncollinear g x y hxy
  have hrempos : 0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) :=
    hindex x _ hx (metricOrthogonalizeSecond_orthogonal g x y hxne) hremne
  apply lorentzianPlaneFrame_orthonormal g hg x y hx
  rw [← metricOrthogonalizeSecond_norm g hg x y hxne]
  exact hrempos

/-- On an index-one metric space, any noncollinear pair orthogonal to a fixed
timelike vector automatically spans a positive-definite two-plane. -/
theorem spacelikePlaneFrame_orthonormal_of_indexOne
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (t x y : V) (ht : g t t < 0)
    (htx : g t x = 0) (hty : g t y = 0)
    (hxne : x ≠ 0) (hxy : NoncollinearPair x y) :
    g (spacelikePlaneFrame g x y).1
        (spacelikePlaneFrame g x y).1 = 1 ∧
      g (spacelikePlaneFrame g x y).2
        (spacelikePlaneFrame g x y).2 = 1 ∧
      g (spacelikePlaneFrame g x y).1
        (spacelikePlaneFrame g x y).2 = 0 := by
  have hxpos : 0 < g x x := hindex t x ht htx hxne
  have hremne := metricOrthogonalizeSecond_ne_zero_of_noncollinear g x y hxy
  have htrem : g t (metricOrthogonalizeSecond g x y) = 0 :=
    metricOrthogonalizeSecond_orthogonal_of_both g t x y htx hty
  have hrempos : 0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) :=
    hindex t _ ht htrem hremne
  apply spacelikePlaneFrame_orthonormal g hg x y hxpos
  rw [← metricOrthogonalizeSecond_norm g hg x y (ne_of_gt hxpos)]
  exact hrempos

/-- **Signature-driven projected tetrad theorem.** For an index-one metric,
noncollinear projected probes replace the four ad hoc Gram inequalities. A
timelike vector in the first principal range forces its orthogonal
complementary projector range to be spacelike. -/
theorem projectedPrincipalPlaneFrames_pseudoOrthonormal_of_indexOne
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (P Q : V →ₗ[ℝ] V)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (hself : MetricSelfAdjoint g P) (hPQ : P.comp Q = 0)
    (u0 u1 v0 v1 : V)
    (hu0 : g (P u0) (P u0) < 0)
    (hu : NoncollinearPair (P u0) (P u1))
    (hv0 : Q v0 ≠ 0)
    (hv : NoncollinearPair (Q v0) (Q v1)) :
    (g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedLorentzianPlaneFrame g P u0 u1).1 = -1 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).2
          (projectedLorentzianPlaneFrame g P u0 u1).2 = 1 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedLorentzianPlaneFrame g P u0 u1).2 = 0) ∧
    (g (projectedSpacelikePlaneFrame g Q v0 v1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).1 = 1 ∧
      g (projectedSpacelikePlaneFrame g Q v0 v1).2
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 1 ∧
      g (projectedSpacelikePlaneFrame g Q v0 v1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 0) ∧
    (g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).1 = 0 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).1
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 0 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).2
          (projectedSpacelikePlaneFrame g Q v0 v1).1 = 0 ∧
      g (projectedLorentzianPlaneFrame g P u0 u1).2
          (projectedSpacelikePlaneFrame g Q v0 v1).2 = 0) := by
  have hPu0 : P (P u0) = P u0 := projector_apply_fixed P hP u0
  have hPu1 : P (P u1) = P u1 := projector_apply_fixed P hP u1
  have hQv0 : Q (Q v0) = Q v0 := projector_apply_fixed Q hQ v0
  have hQv1 : Q (Q v1) = Q v1 := projector_apply_fixed Q hQ v1
  have ht0 : g (P u0) (Q v0) = 0 :=
    complementaryProjector_fixed_orthogonal g P Q hself hPQ _ _ hPu0 hQv0
  have ht1 : g (P u0) (Q v1) = 0 :=
    complementaryProjector_fixed_orthogonal g P Q hself hPQ _ _ hPu0 hQv1
  have hLor := lorentzianPlaneFrame_orthonormal_of_indexOne
    g hg hindex (P u0) (P u1) hu0 hu
  have hSpa := spacelikePlaneFrame_orthonormal_of_indexOne
    g hg hindex (P u0) (Q v0) (Q v1) hu0 ht0 ht1 hv0 hv
  have hCross := principalPlaneFrames_cross_orthogonal g P Q hself hPQ
    (P u0) (P u1) (Q v0) (Q v1) hPu0 hPu1 hQv0 hQv1
  simpa [projectedLorentzianPlaneFrame, projectedSpacelikePlaneFrame] using
    And.intro hLor (And.intro hSpa hCross)

/-- Compact predicate for a principal tetrad with signature `(-,+,+,+)` and
the two displayed frame pairs mutually orthogonal. -/
def IsPseudoOrthonormalPrincipalTetrad
    (g : BilinForm ℝ V) (lorentzFrame spaceFrame : V × V) : Prop :=
  (g lorentzFrame.1 lorentzFrame.1 = -1 ∧
    g lorentzFrame.2 lorentzFrame.2 = 1 ∧
    g lorentzFrame.1 lorentzFrame.2 = 0) ∧
  (g spaceFrame.1 spaceFrame.1 = 1 ∧
    g spaceFrame.2 spaceFrame.2 = 1 ∧
    g spaceFrame.1 spaceFrame.2 = 0) ∧
  (g lorentzFrame.1 spaceFrame.1 = 0 ∧
    g lorentzFrame.1 spaceFrame.2 = 0 ∧
    g lorentzFrame.2 spaceFrame.1 = 0 ∧
    g lorentzFrame.2 spaceFrame.2 = 0)

/-- Principal-plane orthonormality for vectors already known to be fixed by
the complementary projectors.  This form is used when the Lorentzian vectors
are finite metric-dependent combinations of projected coordinate probes. -/
theorem principalPlaneFrames_pseudoOrthonormal_of_fixed
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (P Q : V →ₗ[ℝ] V)
    (hself : MetricSelfAdjoint g P) (hPQ : P.comp Q = 0)
    (x y u v : V)
    (hPx : P x = x) (hPy : P y = y)
    (hQu : Q u = u) (hQv : Q v = v)
    (hx : g x x < 0)
    (hy : 0 < g y y - (g x y) ^ 2 / g x x)
    (hu : 0 < g u u)
    (hv : 0 < g v v - (g u v) ^ 2 / g u u) :
    IsPseudoOrthonormalPrincipalTetrad g
      (lorentzianPlaneFrame g x y) (spacelikePlaneFrame g u v) := by
  have hLor := lorentzianPlaneFrame_orthonormal g hg x y hx hy
  have hSpa := spacelikePlaneFrame_orthonormal g hg u v hu hv
  have hCross := principalPlaneFrames_cross_orthogonal g P Q hself hPQ
    x y u v hPx hPy hQu hQv
  exact ⟨hLor, hSpa, hCross⟩

/-- The four vectors underlying a paired principal tetrad. -/
def principalTetradVectors
    (lorentzFrame spaceFrame : V × V) : Fin 4 → V :=
  ![lorentzFrame.1, lorentzFrame.2, spaceFrame.1, spaceFrame.2]

/-- A pseudo-orthonormal principal tetrad is linearly independent. -/
theorem IsPseudoOrthonormalPrincipalTetrad.linearIndependent
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (lorentzFrame spaceFrame : V × V)
    (hframe : IsPseudoOrthonormalPrincipalTetrad g lorentzFrame spaceFrame) :
    LinearIndependent ℝ (principalTetradVectors lorentzFrame spaceFrame) := by
  rcases hframe with
    ⟨⟨h00, h11, h01⟩, ⟨h22, h33, h23⟩, ⟨h02, h03, h12, h13⟩⟩
  have h10 : g lorentzFrame.2 lorentzFrame.1 = 0 := by
    rw [hg.eq]
    exact h01
  have h20 : g spaceFrame.1 lorentzFrame.1 = 0 := by
    rw [hg.eq]
    exact h02
  have h30 : g spaceFrame.2 lorentzFrame.1 = 0 := by
    rw [hg.eq]
    exact h03
  have h21 : g spaceFrame.1 lorentzFrame.2 = 0 := by
    rw [hg.eq]
    exact h12
  have h31 : g spaceFrame.2 lorentzFrame.2 = 0 := by
    rw [hg.eq]
    exact h13
  have h32 : g spaceFrame.2 spaceFrame.1 = 0 := by
    rw [hg.eq]
    exact h23
  apply BilinForm.linearIndependent_of_iIsOrtho (B := g)
  · rw [BilinForm.iIsOrtho_def]
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [principalTetradVectors, h01, h02, h03, h10, h12, h13,
        h20, h21, h23, h30, h31, h32] at hij ⊢
  · intro i
    fin_cases i <;>
      simp [principalTetradVectors, h00, h11, h22, h33]

/-- In dimension four, a pseudo-orthonormal principal tetrad canonically
defines a basis. -/
noncomputable def principalTetradBasis
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (lorentzFrame spaceFrame : V × V)
    (hframe : IsPseudoOrthonormalPrincipalTetrad g lorentzFrame spaceFrame)
    (hdim : finrank ℝ V = 4) : Basis (Fin 4) ℝ V :=
  basisOfLinearIndependentOfCardEqFinrank
    (hframe.linearIndependent g hg lorentzFrame spaceFrame)
    (by simp [hdim])

/-- The constructed basis evaluates to the four original tetrad vectors. -/
@[simp]
theorem principalTetradBasis_apply
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (lorentzFrame spaceFrame : V × V)
    (hframe : IsPseudoOrthonormalPrincipalTetrad g lorentzFrame spaceFrame)
    (hdim : finrank ℝ V = 4) (i : Fin 4) :
    principalTetradBasis g hg lorentzFrame spaceFrame hframe hdim i =
      principalTetradVectors lorentzFrame spaceFrame i := by
  apply congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank
      (hframe.linearIndependent g hg lorentzFrame spaceFrame)
      (by simp [hdim]))

/-- Canonical Maxwell two-form transported to an abstract vector space through
a principal tetrad basis. -/
noncomputable def principalMaxwellTwoForm
    (b : Basis (Fin 4) ℝ V) (E B : ℝ) : BilinForm ℝ V :=
  Matrix.toBilin b (canonicalMaxwellTwoForm E B)

/-- In the adapted tetrad basis, the abstract two-form has exactly the
canonical Maxwell matrix. -/
@[simp]
theorem principalMaxwellTwoForm_toMatrix
    (b : Basis (Fin 4) ℝ V) (E B : ℝ) :
    LinearMap.BilinForm.toMatrix b (principalMaxwellTwoForm b E B) =
      canonicalMaxwellTwoForm E B := by
  simp [principalMaxwellTwoForm]

/-- The basis matrix of the transported Maxwell form is skew-symmetric. -/
theorem principalMaxwellTwoForm_toMatrix_transpose
    (b : Basis (Fin 4) ℝ V) (E B : ℝ) :
    Matrix.transpose
        (LinearMap.BilinForm.toMatrix b (principalMaxwellTwoForm b E B)) =
      -(LinearMap.BilinForm.toMatrix b (principalMaxwellTwoForm b E B)) := by
  simp [canonicalMaxwellTwoForm_transpose]

/-- Positive-`q` Maxwell seed in an abstract principal tetrad basis. -/
noncomputable def principalPositiveQMaxwellTwoForm
    (b : Basis (Fin 4) ℝ V) (q : ℝ) : BilinForm ℝ V :=
  principalMaxwellTwoForm b (Real.sqrt (2 * q)) 0

/-- Maxwell stress endomorphism computed in a supplied Lorentz-orthonormal
basis and transported back to the abstract vector space. -/
noncomputable def principalMaxwellStress
    (b : Basis (Fin 4) ℝ V) (F : BilinForm ℝ V) : V →ₗ[ℝ] V :=
  Matrix.toLin b b
    (matrixMaxwellStress minkowskiMetric (LinearMap.BilinForm.toMatrix b F))

/-- The abstract positive-`q` seed has the same canonical matrix as the
explicit Lorentzian construction. -/
@[simp]
theorem principalPositiveQMaxwellTwoForm_toMatrix
    (b : Basis (Fin 4) ℝ V) (q : ℝ) :
    LinearMap.BilinForm.toMatrix b (principalPositiveQMaxwellTwoForm b q) =
      canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 := by
  simp [principalPositiveQMaxwellTwoForm]

/-- Linear independence of a pair implies the noncollinearity condition used
by the constructive Gram--Schmidt theorem. -/
theorem noncollinearPair_of_linearIndependent
    (x y : V) (hx : x ≠ 0) (hxy : LinearIndependent ℝ ![x, y]) :
    NoncollinearPair x y := by
  intro a hay
  have hne : a • x ≠ y := (LinearIndependent.pair_iff' hx).mp hxy a
  exact hne hay.symm

/-- A linearly independent pair whose span contains a timelike vector has
negative Gram determinant in an index-one metric. This is the algebraic
signature bridge needed to turn a projected coordinate basis pair into the
finite Lorentzian pivot theorem. -/
theorem metricGramDet_neg_of_linearIndependent_span_timelike
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (x y t : V) (hxy : LinearIndependent ℝ ![x, y])
    (ht : g t t < 0) (htspan : t ∈ Submodule.span ℝ ({x, y} : Set V)) :
    metricGramDet g x y < 0 := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp htspan
  have htne : t ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.BilinForm.zero_left] at ht
    linarith
  have hcoeff := LinearIndependent.pair_iff.mp hxy
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hbzero
      rw [ha, hbzero, zero_smul, zero_smul, add_zero] at hab
      exact htne hab.symm
    have htx : LinearIndependent ℝ ![t, x] := by
      rw [LinearIndependent.pair_iff]
      intro s r hzero
      have hrel : r • x + (s * b) • y = 0 := by
        calc
          r • x + (s * b) • y = s • t + r • x := by
            rw [← hab, ha]
            module
          _ = 0 := hzero
      obtain ⟨hr, hsb⟩ := hcoeff r (s * b) hrel
      have hs : s = 0 := by
        exact (mul_eq_zero.mp hsb).resolve_right hb
      exact ⟨hs, hr⟩
    have hnoncol : NoncollinearPair t x :=
      noncollinearPair_of_linearIndependent t x htne htx
    have hremne :=
      metricOrthogonalizeSecond_ne_zero_of_noncollinear g t x hnoncol
    have hrempos : 0 < g (metricOrthogonalizeSecond g t x)
        (metricOrthogonalizeSecond g t x) :=
      hindex t _ ht (metricOrthogonalizeSecond_orthogonal g t x
        (ne_of_lt ht)) hremne
    have hdetTx : metricGramDet g t x < 0 := by
      rw [metricOrthogonalizeSecond_norm_eq_gramDet_div g hg t x
        (ne_of_lt ht)] at hrempos
      rcases (div_pos_iff.mp hrempos) with hsame | hsame
      · exact False.elim ((not_lt_of_ge (le_of_lt ht)) hsame.2)
      · exact hsame.1
    have htransform :
        metricGramDet g t x = b ^ 2 * metricGramDet g x y := by
      rw [← hab, ha]
      simp only [zero_smul, zero_add, metricGramDet,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      rw [hg.eq y x]
      ring
    rw [htransform] at hdetTx
    have hbsq : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith
  · have hty : LinearIndependent ℝ ![t, y] := by
      rw [LinearIndependent.pair_iff]
      intro s r hzero
      have hrel : (s * a) • x + (s * b + r) • y = 0 := by
        calc
          (s * a) • x + (s * b + r) • y = s • t + r • y := by
            rw [← hab]
            module
          _ = 0 := hzero
      obtain ⟨hsa, hrest⟩ := hcoeff (s * a) (s * b + r) hrel
      have hs : s = 0 := by
        exact (mul_eq_zero.mp hsa).resolve_right ha
      have hr : r = 0 := by
        rw [hs, zero_mul, zero_add] at hrest
        exact hrest
      exact ⟨hs, hr⟩
    have hnoncol : NoncollinearPair t y :=
      noncollinearPair_of_linearIndependent t y htne hty
    have hremne :=
      metricOrthogonalizeSecond_ne_zero_of_noncollinear g t y hnoncol
    have hrempos : 0 < g (metricOrthogonalizeSecond g t y)
        (metricOrthogonalizeSecond g t y) :=
      hindex t _ ht (metricOrthogonalizeSecond_orthogonal g t y
        (ne_of_lt ht)) hremne
    have hdetTy : metricGramDet g t y < 0 := by
      rw [metricOrthogonalizeSecond_norm_eq_gramDet_div g hg t y
        (ne_of_lt ht)] at hrempos
      rcases (div_pos_iff.mp hrempos) with hsame | hsame
      · exact False.elim ((not_lt_of_ge (le_of_lt ht)) hsame.2)
      · exact hsame.1
    have htransform :
        metricGramDet g t y = a ^ 2 * metricGramDet g x y := by
      rw [← hab]
      simp only [metricGramDet, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left,
        LinearMap.BilinForm.smul_right]
      rw [hg.eq y x]
      ring
    rw [htransform] at hdetTy
    have hasq : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith

/-- In a two-dimensional subspace, every nonzero vector has a second vector
noncollinear with it. -/
theorem exists_noncollinear_of_finrank_eq_two
    (W : Submodule ℝ V) (hW : finrank ℝ W = 2)
    (x : W) (hx : x ≠ 0) :
    ∃ y : W, NoncollinearPair (x : V) (y : V) := by
  have hrank : 1 < finrank ℝ W := by omega
  obtain ⟨y, hxy⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank hrank hx
  refine ⟨y, ?_⟩
  have hcoex : (x : V) ≠ 0 := by simpa using hx
  intro a hay
  have hne : a • x ≠ y := (LinearIndependent.pair_iff' hx).mp hxy a
  apply hne
  apply Subtype.ext
  simpa using hay.symm

/-- A rank-two linear-map range contains a basis selected from the projected
vectors of any ambient basis.  In particular, a finite coordinate basis
always supplies a noncollinear projected pair; no arbitrary ambient probes
are needed for this algebraic selection step. -/
theorem exists_projectedBasisPair_of_finrank_range_eq_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 2) :
    ∃ k : Fin 2 → ι,
      LinearIndependent ℝ (fun n => P (b (k n))) := by
  let s : Set V := Set.range fun i => P (b i)
  have hspan : Submodule.span ℝ s = P.range := by
    calc
      Submodule.span ℝ s =
          (Submodule.span ℝ (Set.range b)).map P := by
            rw [Submodule.map_span]
            congr 1
            ext z
            simp [s]
      _ = (⊤ : Submodule ℝ V).map P := by rw [b.span_eq]
      _ = P.range := Submodule.map_top P
  have hfinrank : finrank ℝ (Submodule.span ℝ s) = 2 := by
    rw [hspan, hrank]
  obtain ⟨f, hfmem, _, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ s
  have hcard : Fin (finrank ℝ (Submodule.span ℝ s)) = Fin 2 := by
    rw [hfinrank]
  let e : Fin 2 ≃ Fin (finrank ℝ (Submodule.span ℝ s)) :=
    Equiv.cast hcard.symm
  have hfmem' : ∀ n : Fin 2, f (e n) ∈ s := fun n => hfmem (e n)
  choose k hk using fun n => hfmem' n
  refine ⟨k, ?_⟩
  have hreindexed : LinearIndependent ℝ (fun n : Fin 2 => f (e n)) :=
    hfind.comp (fun n => e n) e.injective
  have heq : (fun n : Fin 2 => P (b (k n))) = fun n => f (e n) :=
    funext hk
  rw [heq]
  exact hreindexed

/-- A rank-one linear-map range cannot be missed by projection of an ambient
basis: at least one projected basis vector is nonzero.  This is the
one-dimensional analogue of `exists_projectedBasisPair_of_finrank_range_eq_two`
and is the finite-search fact needed by the scalar Ricci eigenlines. -/
theorem exists_projectedBasisVector_ne_zero_of_finrank_range_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 1) :
    ∃ i : ι, P (b i) ≠ 0 := by
  let s : Set V := Set.range fun i => P (b i)
  have hspan : Submodule.span ℝ s = P.range := by
    calc
      Submodule.span ℝ s =
          (Submodule.span ℝ (Set.range b)).map P := by
            rw [Submodule.map_span]
            congr 1
            ext z
            simp [s]
      _ = (⊤ : Submodule ℝ V).map P := by rw [b.span_eq]
      _ = P.range := Submodule.map_top P
  have hfinrank : finrank ℝ (Submodule.span ℝ s) = 1 := by
    rw [hspan, hrank]
  obtain ⟨f, hfmem, _, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ s
  have hcard : Fin (finrank ℝ (Submodule.span ℝ s)) = Fin 1 := by
    rw [hfinrank]
  let e : Fin 1 ≃ Fin (finrank ℝ (Submodule.span ℝ s)) :=
    Equiv.cast hcard.symm
  obtain ⟨i, hi⟩ := hfmem (e 0)
  refine ⟨i, ?_⟩
  change P (b i) = f (e 0) at hi
  rw [hi]
  exact hfind.ne_zero (e 0)

/-- Every ambient basis contains a projected timelike vector when a rank-one
range is a timelike line.  The causal-line hypothesis is intrinsic to the
range; no preferred vector or detector probe is supplied. -/
theorem exists_projectedBasisTimelikeVector_of_rankOneRange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 1)
    (htimelike : ∀ x : P.range, (x : V) ≠ 0 → g (x : V) (x : V) < 0) :
    ∃ i : ι, g (P (b i)) (P (b i)) < 0 := by
  obtain ⟨i, hi⟩ :=
    exists_projectedBasisVector_ne_zero_of_finrank_range_eq_one b P hrank
  let x : P.range := ⟨P (b i), LinearMap.mem_range_self P (b i)⟩
  exact ⟨i, htimelike x hi⟩

/-- Every ambient basis contains a projected spacelike vector when a rank-one
range is a spacelike line. -/
theorem exists_projectedBasisSpacelikeVector_of_rankOneRange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 1)
    (hspacelike : ∀ x : P.range, (x : V) ≠ 0 → 0 < g (x : V) (x : V)) :
    ∃ i : ι, 0 < g (P (b i)) (P (b i)) := by
  obtain ⟨i, hi⟩ :=
    exists_projectedBasisVector_ne_zero_of_finrank_range_eq_one b P hrank
  let x : P.range := ⟨P (b i), LinearMap.mem_range_self P (b i)⟩
  exact ⟨i, hspacelike x hi⟩

/-- **Normalized rank-one line uniqueness.** Two nonzero vectors in the same
rank-one range with the same nonzero signed metric norm agree up to the sole
remaining global sign.  This is the algebraic reason arbitrary admissible
scalar probes generate the same two-element relative-sign candidate set. -/
theorem rankOneRange_normalizedVectors_eq_or_neg
    (g : BilinForm ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 1)
    (x y : P.range) (hx : (x : V) ≠ 0)
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (hxx : g (x : V) (x : V) = sigma)
    (hyy : g (y : V) (y : V) = sigma) :
    (y : V) = (x : V) ∨ (y : V) = -(x : V) := by
  have hxsub : x ≠ 0 := by
    intro hzero
    apply hx
    simpa using congrArg Subtype.val hzero
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrank hxsub y
  have hcoe : c • (x : V) = (y : V) := congrArg Subtype.val hc
  have hmetric : c ^ 2 * sigma = sigma := by
    calc
      c ^ 2 * sigma = c * (c * g (x : V) (x : V)) := by
        rw [hxx]
        ring
      _ = g (c • (x : V)) (c • (x : V)) := by
        simp
      _ = sigma := by rw [hcoe, hyy]
  have hcsq : c ^ 2 = 1 := by
    have hzero : (c ^ 2 - 1) * sigma = 0 := by
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hsigma)
  rcases (sq_eq_one_iff.mp hcsq) with hcOne | hcNeg
  · left
    rw [← hcoe, hcOne, one_smul]
  · right
    rw [← hcoe, hcNeg, neg_smul, one_smul]

/-- Two independently chosen signs on a pair of one-dimensional components
are exhausted by the relative sum/difference branch and one irrelevant
overall sign.  This is the discrete algebra behind scalar-branch
identifiability. -/
theorem exists_relativeSignCombination_eq_or_neg
    {W : Type*} [AddCommGroup W]
    (alpha beta alpha' beta' : W)
    (halpha : alpha' = alpha ∨ alpha' = -alpha)
    (hbeta : beta' = beta ∨ beta' = -beta) :
    ∃ relativeMinus : Bool,
      (if relativeMinus then alpha' - beta' else alpha' + beta') =
          alpha + beta ∨
        (if relativeMinus then alpha' - beta' else alpha' + beta') =
          -(alpha + beta) := by
  rcases halpha with halpha | halpha <;>
    rcases hbeta with hbeta | hbeta
  · refine ⟨false, Or.inl ?_⟩
    simp [halpha, hbeta]
  · refine ⟨true, Or.inl ?_⟩
    rw [halpha, hbeta]
    simp
  · refine ⟨true, Or.inr ?_⟩
    rw [halpha, hbeta]
    simp [sub_eq_add_neg, add_comm]
  · refine ⟨false, Or.inr ?_⟩
    rw [halpha, hbeta]
    simp [add_comm]

/-- **Rank-one two-line scalar identifiability.** Let the two scalar
spectral lines have Lorentzian signs `-1,+1`.  Any normalized representatives
of those lines, including representatives selected by arbitrary finite
probes, generate through the two relative sum/difference branches exactly
the same metric-dual scalar covector up to the unavoidable overall sign.

Thus normalized scalar probes introduce no ambiguity beyond the already
enumerated relative-sign bit and the physically irrelevant transformation
`dphi ↦ -dphi`. -/
theorem exists_relativeSignMetricDualCombination_eq_or_neg_of_rankOneRanges
    (g : BilinForm ℝ V) (P Q : V →ₗ[ℝ] V)
    (hrankP : finrank ℝ P.range = 1)
    (hrankQ : finrank ℝ Q.range = 1)
    (physicalTimelike selectedTimelike : P.range)
    (physicalSpacelike selectedSpacelike : Q.range)
    (hphysicalTimelike : (physicalTimelike : V) ≠ 0)
    (hphysicalSpacelike : (physicalSpacelike : V) ≠ 0)
    (hphysicalTimelikeNorm :
      g (physicalTimelike : V) (physicalTimelike : V) = -1)
    (hselectedTimelikeNorm :
      g (selectedTimelike : V) (selectedTimelike : V) = -1)
    (hphysicalSpacelikeNorm :
      g (physicalSpacelike : V) (physicalSpacelike : V) = 1)
    (hselectedSpacelikeNorm :
      g (selectedSpacelike : V) (selectedSpacelike : V) = 1)
    (a b : ℝ) :
    ∃ relativeMinus : Bool,
      (if relativeMinus then
          a • g (selectedTimelike : V) -
            b • g (selectedSpacelike : V)
        else
          a • g (selectedTimelike : V) +
            b • g (selectedSpacelike : V)) =
          a • g (physicalTimelike : V) +
            b • g (physicalSpacelike : V) ∨
        (if relativeMinus then
            a • g (selectedTimelike : V) -
              b • g (selectedSpacelike : V)
          else
            a • g (selectedTimelike : V) +
              b • g (selectedSpacelike : V)) =
          -(a • g (physicalTimelike : V) +
            b • g (physicalSpacelike : V)) := by
  have htime := rankOneRange_normalizedVectors_eq_or_neg
    g P hrankP physicalTimelike selectedTimelike hphysicalTimelike
    (-1) (by norm_num)
    hphysicalTimelikeNorm hselectedTimelikeNorm
  have hspace := rankOneRange_normalizedVectors_eq_or_neg
    g Q hrankQ physicalSpacelike selectedSpacelike hphysicalSpacelike
    1 (by norm_num)
    hphysicalSpacelikeNorm hselectedSpacelikeNorm
  have htimeDual :
      a • g (selectedTimelike : V) =
          a • g (physicalTimelike : V) ∨
        a • g (selectedTimelike : V) =
          -(a • g (physicalTimelike : V)) := by
    rcases htime with htime | htime
    · exact Or.inl (by rw [htime])
    · exact Or.inr (by rw [htime]; simp)
  have hspaceDual :
      b • g (selectedSpacelike : V) =
          b • g (physicalSpacelike : V) ∨
        b • g (selectedSpacelike : V) =
          -(b • g (physicalSpacelike : V)) := by
    rcases hspace with hspace | hspace
    · exact Or.inl (by rw [hspace])
    · exact Or.inr (by rw [hspace]; simp)
  exact exists_relativeSignCombination_eq_or_neg
    (a • g (physicalTimelike : V))
    (b • g (physicalSpacelike : V))
    (a • g (selectedTimelike : V))
    (b • g (selectedSpacelike : V)) htimeDual hspaceDual

/-- **Finite-probe scalar identifiability.** Project any two admissible
ambient probes into the timelike and spacelike rank-one scalar eigenspaces
and normalize them.  The two relative-sign branches made from those concrete
probe outputs contain the physical scalar covector, up to its global sign.

This specializes the preceding line theorem to exactly the finite
project-and-normalize operation used by the metric detector. -/
theorem exists_relativeSignMetricDualCombination_eq_or_neg_of_projectedProbes
    (g : BilinForm ℝ V) (P Q : V →ₗ[ℝ] V)
    (hrankP : finrank ℝ P.range = 1)
    (hrankQ : finrank ℝ Q.range = 1)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (u v : V)
    (hPu : g (P u) (P u) < 0)
    (hQv : 0 < g (Q v) (Q v))
    (physicalTimelike : P.range) (physicalSpacelike : Q.range)
    (hphysicalTimelike : (physicalTimelike : V) ≠ 0)
    (hphysicalSpacelike : (physicalSpacelike : V) ≠ 0)
    (hphysicalTimelikeNorm :
      g (physicalTimelike : V) (physicalTimelike : V) = -1)
    (hphysicalSpacelikeNorm :
      g (physicalSpacelike : V) (physicalSpacelike : V) = 1)
    (a b : ℝ) :
    ∃ relativeMinus : Bool,
      (if relativeMinus then
          a • g (normalizeTimelike g (P u)) -
            b • g (normalizeSpacelike g (Q v))
        else
          a • g (normalizeTimelike g (P u)) +
            b • g (normalizeSpacelike g (Q v))) =
          a • g (physicalTimelike : V) +
            b • g (physicalSpacelike : V) ∨
        (if relativeMinus then
            a • g (normalizeTimelike g (P u)) -
              b • g (normalizeSpacelike g (Q v))
          else
            a • g (normalizeTimelike g (P u)) +
              b • g (normalizeSpacelike g (Q v))) =
          -(a • g (physicalTimelike : V) +
            b • g (physicalSpacelike : V)) := by
  have hPuFixed : P (P u) = P u := projector_apply_fixed P hP u
  have hQvFixed : Q (Q v) = Q v := projector_apply_fixed Q hQ v
  have htimeFixed : P (normalizeTimelike g (P u)) =
      normalizeTimelike g (P u) :=
    normalizeTimelike_fixed g P (P u) hPuFixed
  have hspaceFixed : Q (normalizeSpacelike g (Q v)) =
      normalizeSpacelike g (Q v) :=
    normalizeSpacelike_fixed g Q (Q v) hQvFixed
  let selectedTimelike : P.range :=
    ⟨normalizeTimelike g (P u), ⟨normalizeTimelike g (P u), htimeFixed⟩⟩
  let selectedSpacelike : Q.range :=
    ⟨normalizeSpacelike g (Q v),
      ⟨normalizeSpacelike g (Q v), hspaceFixed⟩⟩
  exact exists_relativeSignMetricDualCombination_eq_or_neg_of_rankOneRanges
    g P Q hrankP hrankQ physicalTimelike selectedTimelike
    physicalSpacelike selectedSpacelike hphysicalTimelike
    hphysicalSpacelike hphysicalTimelikeNorm
    (normalizeTimelike_norm g (P u) hPu)
    hphysicalSpacelikeNorm (normalizeSpacelike_norm g (Q v) hQv) a b

/-- **Arbitrary-basis Lorentzian pair theorem.** If a rank-two projector
range contains a timelike vector in an index-one metric, then every ambient
basis contains two vectors whose projections have negative Gram determinant.
Together with `exists_lorentzianPivotRecipe_of_gramDet_neg`, this removes the
time-adapted-coordinate assumption from the finite principal-plane entrance. -/
theorem exists_projectedBasisPair_gramDet_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 2)
    (t : P.range) (ht : g (t : V) (t : V) < 0) :
    ∃ i j : ι, metricGramDet g (P (b i)) (P (b j)) < 0 := by
  obtain ⟨k, hk⟩ :=
    exists_projectedBasisPair_of_finrank_range_eq_two b P hrank
  let pair : Fin 2 → V := fun n => P (b (k n))
  have hpair : LinearIndependent ℝ pair := by
    simpa [pair] using hk
  have hle : Submodule.span ℝ (Set.range pair) ≤ P.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact LinearMap.mem_range_self P (b (k n))
  have hfinspan : finrank ℝ (Submodule.span ℝ (Set.range pair)) = 2 := by
    rw [finrank_span_eq_card hpair]
    simp
  have hspan : Submodule.span ℝ (Set.range pair) = P.range :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinspan, hrank])
  have htspanRange :
      (t : V) ∈ Submodule.span ℝ (Set.range pair) := by
    rw [hspan]
    exact t.property
  have hrange : Set.range pair = {pair 0, pair 1} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      fin_cases n <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have htspanPair :
      (t : V) ∈ Submodule.span ℝ ({pair 0, pair 1} : Set V) := by
    rwa [hrange] at htspanRange
  have hpairMatrix : LinearIndependent ℝ ![pair 0, pair 1] := by
    have heq : (![pair 0, pair 1] : Fin 2 → V) = pair := by
      funext n
      fin_cases n <;> rfl
    rw [heq]
    exact hpair
  refine ⟨k 0, k 1, ?_⟩
  exact metricGramDet_neg_of_linearIndependent_span_timelike
    g hg hindex (pair 0) (pair 1) t
    hpairMatrix ht htspanPair

/-- Finite arbitrary-basis Lorentzian entrance: two basis indices and one of
the six pivot recipes produce a timelike pivot with a negative-Gram
companion. -/
theorem exists_projectedBasisLorentzianPivot
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 2)
    (t : P.range) (ht : g (t : V) (t : V) < 0) :
    ∃ i j : ι, ∃ recipe : LorentzianPivotRecipe,
      g (lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe)
          (lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe) < 0 ∧
      metricGramDet g
          (lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe)
          (lorentzianPivotCompanion (P (b i)) (P (b j)) recipe) < 0 := by
  obtain ⟨i, j, hdet⟩ :=
    exists_projectedBasisPair_gramDet_neg g hg hindex b P hrank t ht
  obtain ⟨recipe, htime, hrecipeDet⟩ :=
    exists_lorentzianPivotRecipe_of_gramDet_neg g hg
      (P (b i)) (P (b j)) hdet
  exact ⟨i, j, recipe, htime, hrecipeDet⟩

/-- The arbitrary-basis finite pivot directly supplies the two strict signs
consumed by Lorentzian Gram--Schmidt. -/
theorem exists_projectedBasisLorentzianFrameSigns
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V) (P : V →ₗ[ℝ] V)
    (hrank : finrank ℝ P.range = 2)
    (t : P.range) (ht : g (t : V) (t : V) < 0) :
    ∃ i j : ι, ∃ recipe : LorentzianPivotRecipe,
      let pivot := lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe
      let companion := lorentzianPivotCompanion (P (b i)) (P (b j)) recipe
      g pivot pivot < 0 ∧
        0 < g (metricOrthogonalizeSecond g pivot companion)
          (metricOrthogonalizeSecond g pivot companion) := by
  obtain ⟨i, j, recipe, htime, hdet⟩ :=
    exists_projectedBasisLorentzianPivot g hg hindex b P hrank t ht
  refine ⟨i, j, recipe, htime, ?_⟩
  exact metricOrthogonalizeSecond_pos_of_lorentzianGram g hg _ _ htime hdet

/-- **Arbitrary-basis spacelike pair theorem.** If a rank-two projector range
is orthogonal to a timelike vector in an index-one metric, then every ambient
basis supplies two projected vectors with both strict positive
Gram--Schmidt signs. -/
theorem exists_projectedBasisSpacelikeFrameSigns
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V) (Q : V →ₗ[ℝ] V)
    (hrank : finrank ℝ Q.range = 2)
    (t : V) (ht : g t t < 0)
    (horth : ∀ z : Q.range, g t (z : V) = 0) :
    ∃ i j : ι,
      0 < g (Q (b i)) (Q (b i)) ∧
        0 < g (metricOrthogonalizeSecond g (Q (b i)) (Q (b j)))
          (metricOrthogonalizeSecond g (Q (b i)) (Q (b j))) := by
  obtain ⟨k, hk⟩ :=
    exists_projectedBasisPair_of_finrank_range_eq_two b Q hrank
  let x := Q (b (k 0))
  let y := Q (b (k 1))
  have hxne : x ≠ 0 := by
    exact hk.ne_zero 0
  have hpair : LinearIndependent ℝ ![x, y] := by
    have heq : (![x, y] : Fin 2 → V) =
        fun n => Q (b (k n)) := by
      funext n
      fin_cases n <;> rfl
    rw [heq]
    exact hk
  have hnoncollinear : NoncollinearPair x y :=
    noncollinearPair_of_linearIndependent x y hxne hpair
  have htx : g t x = 0 := by
    exact horth ⟨x, LinearMap.mem_range_self Q (b (k 0))⟩
  have hty : g t y = 0 := by
    exact horth ⟨y, LinearMap.mem_range_self Q (b (k 1))⟩
  have hxpos : 0 < g x x := hindex t x ht htx hxne
  have hremne : metricOrthogonalizeSecond g x y ≠ 0 :=
    metricOrthogonalizeSecond_ne_zero_of_noncollinear g x y hnoncollinear
  have htrem : g t (metricOrthogonalizeSecond g x y) = 0 :=
    metricOrthogonalizeSecond_orthogonal_of_both g t x y htx hty
  have hrempos : 0 < g (metricOrthogonalizeSecond g x y)
      (metricOrthogonalizeSecond g x y) :=
    hindex t _ ht htrem hremne
  exact ⟨k 0, k 1, hxpos, hrempos⟩

/-- An idempotent projector fixes every vector in its range. -/
theorem projector_fixed_of_mem_range
    (P : V →ₗ[ℝ] V) (hP : P.comp P = P)
    (x : V) (hx : x ∈ P.range) :
    P x = x := by
  obtain ⟨u, rfl⟩ := hx
  exact projector_apply_fixed P hP u

/-- The Maxwell residual acts by `-q` on vectors fixed by its negative
principal projector. -/
theorem maxwellResidual_apply_eq_neg_smul_of_minus_fixed
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (x : V) (hx : maxwellMinusProjector S q x = x) :
    S x = (-q) • x := by
  have hJ := normalizedMaxwellResidual_sq S q hq hS
  have hmul := involution_mul_minusProjector
    (normalizedMaxwellResidual S q) hJ
  have happ := LinearMap.congr_fun hmul x
  have hfix : involutionMinusProjector (normalizedMaxwellResidual S q) x = x := by
    simpa [maxwellMinusProjector] using hx
  have hnorm : normalizedMaxwellResidual S q x = -x := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, hfix] using happ
  unfold normalizedMaxwellResidual at hnorm
  have hscaled := congrArg (fun z : V => q • z) hnorm
  simpa [smul_smul, hq] using hscaled

/-- A negative Maxwell eigenvector is fixed by the negative principal
projector.  This is the converse direction needed to turn the physical
energy-sign eigendirection into projector-range membership. -/
theorem maxwellMinusProjector_fixed_of_neg_eigenvector
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (x : V) (hx : S x = (-q) • x) :
    maxwellMinusProjector S q x = x := by
  simp only [maxwellMinusProjector, involutionMinusProjector,
    normalizedMaxwellResidual, LinearMap.smul_apply,
    LinearMap.sub_apply, hx, smul_smul]
  rw [mul_neg, inv_mul_cancel₀ hq]
  simp
  module

/-- Explicit physical energy-sign condition for a positive-magnitude Maxwell
residual: its negative eigenspace contains a timelike direction.  This is a
choice-free statement about the metric and residual, not a selected detector
frame. -/
def HasPhysicalMaxwellEnergySign
    (g : BilinForm ℝ V) (S : V →ₗ[ℝ] V) (q : ℝ) : Prop :=
  ∃ t : V, g t t < 0 ∧ S t = (-q) • t

/-- Observer formulation of the physical Maxwell energy condition: some
timelike observer measures strictly positive residual energy density. -/
def HasPositiveMaxwellEnergyDensity
    (g : BilinForm ℝ V) (S : V →ₗ[ℝ] V) : Prop :=
  ∃ u : V, g u u < 0 ∧ 0 < g u (S u)

/-- **Positive energy selects the Lorentzian Maxwell eigenspace.** For a
self-adjoint non-null Maxwell residual with positive magnitude, decompose a
positive-energy timelike observer with the two polynomial projectors.  Their
orthogonality, the timelike norm, and positivity of measured energy force the
negative-projector component to be timelike.  Hence the physical energy-sign
eigendirection is a consequence rather than an extra frame choice. -/
theorem hasPhysicalMaxwellEnergySign_of_positiveEnergyDensity
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : 0 < q)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hself : MetricSelfAdjoint g S)
    (henergy : HasPositiveMaxwellEnergyDensity g S) :
    HasPhysicalMaxwellEnergySign g S q := by
  obtain ⟨u, huTime, huEnergy⟩ := henergy
  let P := maxwellMinusProjector S q
  let Q := maxwellPlusProjector S q
  let x := P u
  let y := Q u
  have hPId : P.comp P = P :=
    maxwellMinusProjector_sq S q (ne_of_gt hq) hS
  have hQId : Q.comp Q = Q :=
    maxwellPlusProjector_sq S q (ne_of_gt hq) hS
  have hPQ : P.comp Q = 0 :=
    maxwellProjectors_comp_zero_rev S q (ne_of_gt hq) hS
  have hPself : MetricSelfAdjoint g P :=
    maxwellMinusProjector_metricSelfAdjoint g hg S q hself
  have hxFixed : P x = x := by
    exact projector_apply_fixed P hPId u
  have hyFixed : Q y = y := by
    exact projector_apply_fixed Q hQId u
  have hxy : g x y = 0 :=
    complementaryProjector_fixed_orthogonal
      g P Q hPself hPQ x y hxFixed hyFixed
  have hyx : g y x = 0 := by
    rw [hg.eq y x, hxy]
  have hdecomp : u = x + y := by
    have hsum := LinearMap.congr_fun (maxwellProjectors_sum S q) u
    simpa [P, Q, x, y, add_comm] using hsum.symm
  have hSx : S x = (-q) • x :=
    maxwellResidual_apply_eq_neg_smul_of_minus_fixed
      S q (ne_of_gt hq) hS x hxFixed
  have hSy : S y = q • y := by
    have hJ := normalizedMaxwellResidual_sq S q (ne_of_gt hq) hS
    have hmul := involution_mul_plusProjector
      (normalizedMaxwellResidual S q) hJ
    have happ := LinearMap.congr_fun hmul y
    have hfix : involutionPlusProjector
        (normalizedMaxwellResidual S q) y = y := by
      simpa [Q, maxwellPlusProjector] using hyFixed
    have hnorm : normalizedMaxwellResidual S q y = y := by
      simpa only [Module.End.mul_apply, LinearMap.neg_apply, hfix] using happ
    unfold normalizedMaxwellResidual at hnorm
    have hscaled := congrArg (fun z : V => q • z) hnorm
    simpa [smul_smul, ne_of_gt hq] using hscaled
  have hnorm : g x x + g y y < 0 := by
    have heq : g u u = g x x + g y y := by
      rw [hdecomp]
      simp only [LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.add_right, hxy, hyx, add_zero, zero_add]
    linarith
  have henergyEq : g u (S u) = q * (g y y - g x x) := by
    have hSu : S u = (-q) • x + q • y := by
      rw [hdecomp, map_add, hSx, hSy]
    rw [hSu, hdecomp]
    simp only [LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right,
      hxy, hyx]
    ring
  have hdiff : 0 < g y y - g x x := by
    rw [henergyEq] at huEnergy
    nlinarith
  have hxTime : g x x < 0 := by
    linarith
  exact ⟨x, hxTime, hSx⟩

/-- The physical energy sign supplies an actual timelike element of the
negative Maxwell projector range. -/
theorem exists_timelike_mem_maxwellMinusProjector_range_of_energySign
    (g : BilinForm ℝ V) (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (henergy : HasPhysicalMaxwellEnergySign g S q) :
    ∃ t : (maxwellMinusProjector S q).range,
      g (t : V) (t : V) < 0 := by
  obtain ⟨t, ht, heigen⟩ := henergy
  have hfixed :=
    maxwellMinusProjector_fixed_of_neg_eigenvector S q hq t heigen
  exact ⟨⟨t, ⟨t, hfixed⟩⟩, ht⟩

/-- The Maxwell residual acts by `+q` on vectors fixed by its positive
principal projector. -/
theorem maxwellResidual_apply_eq_smul_of_plus_fixed
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (x : V) (hx : maxwellPlusProjector S q x = x) :
    S x = q • x := by
  have hJ := normalizedMaxwellResidual_sq S q hq hS
  have hmul := involution_mul_plusProjector
    (normalizedMaxwellResidual S q) hJ
  have happ := LinearMap.congr_fun hmul x
  have hfix : involutionPlusProjector (normalizedMaxwellResidual S q) x = x := by
    simpa [maxwellPlusProjector] using hx
  have hnorm : normalizedMaxwellResidual S q x = x := by
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, hfix] using happ
  unfold normalizedMaxwellResidual at hnorm
  have hscaled := congrArg (fun z : V => q • z) hnorm
  simpa [smul_smul, hq] using hscaled

/-- In any basis whose first two vectors lie in the negative Maxwell plane
and last two in the positive plane, the residual has the canonical mixed
stress matrix. -/
theorem maxwellResidual_toMatrix_eq_canonical
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (b : Basis (Fin 4) ℝ V)
    (h0 : maxwellMinusProjector S q (b 0) = b 0)
    (h1 : maxwellMinusProjector S q (b 1) = b 1)
    (h2 : maxwellPlusProjector S q (b 2) = b 2)
    (h3 : maxwellPlusProjector S q (b 3) = b 3) :
    LinearMap.toMatrix b b S = canonicalMaxwellResidual q := by
  have hs0 := maxwellResidual_apply_eq_neg_smul_of_minus_fixed
    S q hq hS (b 0) h0
  have hs1 := maxwellResidual_apply_eq_neg_smul_of_minus_fixed
    S q hq hS (b 1) h1
  have hs2 := maxwellResidual_apply_eq_smul_of_plus_fixed
    S q hq hS (b 2) h2
  have hs3 := maxwellResidual_apply_eq_smul_of_plus_fixed
    S q hq hS (b 3) h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, hs0, hs1, hs2, hs3,
      canonicalMaxwellResidual]

/-- **Rank/signature local principal-frame existence.** If both complementary
principal projectors have rank two and the first range contains a timelike
vector, then an index-one metric supplies ambient probes whose projected
Gram--Schmidt frames form a full pseudo-orthonormal tetrad. This removes the
probe-existence hypothesis from the local algebraic frame theorem. -/
theorem exists_projectedPrincipalPlaneFrames_of_rank_two
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (P Q : V →ₗ[ℝ] V)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q)
    (hself : MetricSelfAdjoint g P) (hPQ : P.comp Q = 0)
    (hrankP : finrank ℝ P.range = 2)
    (hrankQ : finrank ℝ Q.range = 2)
    (t : P.range) (ht : g (t : V) (t : V) < 0) :
    ∃ u0 u1 v0 v1 : V,
      IsPseudoOrthonormalPrincipalTetrad g
        (projectedLorentzianPlaneFrame g P u0 u1)
        (projectedSpacelikePlaneFrame g Q v0 v1) := by
  have htne : t ≠ 0 := by
    intro hzero
    have hcoezero : (t : V) = 0 := by simpa using hzero
    rw [hcoezero, LinearMap.BilinForm.zero_left] at ht
    linarith
  obtain ⟨t1, ht1⟩ :=
    exists_noncollinear_of_finrank_eq_two P.range hrankP t htne
  have hrankQpos : 0 < finrank ℝ Q.range := by omega
  letI : Nontrivial Q.range := Module.nontrivial_of_finrank_pos hrankQpos
  obtain ⟨q0, hq0⟩ : ∃ q0 : Q.range, q0 ≠ 0 := exists_ne 0
  obtain ⟨q1, hq1⟩ :=
    exists_noncollinear_of_finrank_eq_two Q.range hrankQ q0 hq0
  let u0 : V := t
  let u1 : V := t1
  let v0 : V := q0
  let v1 : V := q1
  have hPu0 : P u0 = u0 :=
    projector_fixed_of_mem_range P hP u0 t.property
  have hPu1 : P u1 = u1 :=
    projector_fixed_of_mem_range P hP u1 t1.property
  have hQv0 : Q v0 = v0 :=
    projector_fixed_of_mem_range Q hQ v0 q0.property
  have hQv1 : Q v1 = v1 :=
    projector_fixed_of_mem_range Q hQ v1 q1.property
  have hv0ne : Q v0 ≠ 0 := by
    rw [hQv0]
    simpa [v0] using hq0
  have hresult := projectedPrincipalPlaneFrames_pseudoOrthonormal_of_indexOne
    g hg hindex P Q hP hQ hself hPQ u0 u1 v0 v1
    (by simpa [u0, hPu0] using ht)
    (by simpa [hPu0, hPu1, u0, u1] using ht1)
    hv0ne
    (by simpa [hQv0, hQv1, v0, v1] using hq1)
  exact ⟨u0, u1, v0, v1, hresult⟩

/-- In dimension four, a tracefree involution has a rank-two positive
projector. -/
theorem involutionPlusProjector_finrank_range_eq_two
    [FiniteDimensional ℝ V]
    (J : V →ₗ[ℝ] V) (hJ : J * J = 1)
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V J = 0) :
    finrank ℝ (involutionPlusProjector J).range = 2 := by
  have htraceP : LinearMap.trace ℝ V (involutionPlusProjector J) = 2 := by
    unfold involutionPlusProjector
    rw [map_smul, map_add, LinearMap.trace_one, htrace, add_zero, hdim]
    norm_num
  have hidem : IsIdempotentElem (involutionPlusProjector J) :=
    involutionPlusProjector_sq J hJ
  have hprojtrace : LinearMap.trace ℝ V (involutionPlusProjector J) =
      (finrank ℝ (involutionPlusProjector J).range : ℝ) :=
    (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [htraceP] at hprojtrace
  exact_mod_cast hprojtrace.symm

/-- In dimension four, the negative projector of a tracefree involution also
has rank two. -/
theorem involutionMinusProjector_finrank_range_eq_two
    [FiniteDimensional ℝ V]
    (J : V →ₗ[ℝ] V) (hJ : J * J = 1)
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V J = 0) :
    finrank ℝ (involutionMinusProjector J).range = 2 := by
  have htraceP : LinearMap.trace ℝ V (involutionMinusProjector J) = 2 := by
    unfold involutionMinusProjector
    rw [map_smul, map_sub, LinearMap.trace_one, htrace, sub_zero, hdim]
    norm_num
  have hidem : IsIdempotentElem (involutionMinusProjector J) :=
    involutionMinusProjector_sq J hJ
  have hprojtrace : LinearMap.trace ℝ V (involutionMinusProjector J) =
      (finrank ℝ (involutionMinusProjector J).range : ℝ) :=
    (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [htraceP] at hprojtrace
  exact_mod_cast hprojtrace.symm

/-- A tracefree non-null Maxwell residual in four dimensions has two
rank-two curvature-polynomial principal projectors. -/
theorem maxwellProjectors_finrank_range_eq_two
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0) :
    finrank ℝ (maxwellPlusProjector S q).range = 2 ∧
      finrank ℝ (maxwellMinusProjector S q).range = 2 := by
  have hJ := normalizedMaxwellResidual_sq S q hq hS
  have htraceJ : LinearMap.trace ℝ V (normalizedMaxwellResidual S q) = 0 := by
    unfold normalizedMaxwellResidual
    rw [map_smul, htrace, smul_zero]
  exact ⟨involutionPlusProjector_finrank_range_eq_two _ hJ hdim htraceJ,
    involutionMinusProjector_finrank_range_eq_two _ hJ hdim htraceJ⟩

/-- **Physical arbitrary-basis Maxwell entrance.** In dimension four, the
non-null Maxwell square law and trace force both principal ranges to have
rank two.  The choice-free physical energy sign then puts a timelike vector
in the negative range, so every ambient basis supplies a projected pair and
one of the six finite pivot recipes with both strict Lorentzian
Gram--Schmidt signs. -/
theorem exists_projectedBasisMaxwellLorentzianFrameSigns
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (henergy : HasPhysicalMaxwellEnergySign g S q) :
    ∃ i j : ι, ∃ recipe : LorentzianPivotRecipe,
      let P := maxwellMinusProjector S q
      let pivot := lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe
      let companion := lorentzianPivotCompanion (P (b i)) (P (b j)) recipe
      g pivot pivot < 0 ∧
        0 < g (metricOrthogonalizeSecond g pivot companion)
          (metricOrthogonalizeSecond g pivot companion) := by
  obtain ⟨_, hrankMinus⟩ :=
    maxwellProjectors_finrank_range_eq_two S q hq hS hdim htrace
  obtain ⟨t, ht⟩ :=
    exists_timelike_mem_maxwellMinusProjector_range_of_energySign
      g S q hq henergy
  exact exists_projectedBasisLorentzianFrameSigns
    g hg hindex b (maxwellMinusProjector S q) hrankMinus t ht

/-- The physical arbitrary-basis entrance stated directly with positive
observer energy density rather than an eigendirection. -/
theorem exists_projectedBasisMaxwellLorentzianFrameSigns_of_positiveEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : 0 < q)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hself : MetricSelfAdjoint g S)
    (henergy : HasPositiveMaxwellEnergyDensity g S) :
    ∃ i j : ι, ∃ recipe : LorentzianPivotRecipe,
      let P := maxwellMinusProjector S q
      let pivot := lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe
      let companion := lorentzianPivotCompanion (P (b i)) (P (b j)) recipe
      g pivot pivot < 0 ∧
        0 < g (metricOrthogonalizeSecond g pivot companion)
          (metricOrthogonalizeSecond g pivot companion) := by
  exact exists_projectedBasisMaxwellLorentzianFrameSigns
    g hg hindex b S q (ne_of_gt hq) hS hdim htrace
    (hasPhysicalMaxwellEnergySign_of_positiveEnergyDensity
      g hg S q hq hS hself henergy)

/-- **Finite arbitrary-basis Maxwell tetrad entrance.** The non-null square
law, trace, metric self-adjointness, index one, and positive observer energy
select both principal planes from any ambient basis: a finite Lorentzian
pivot recipe for the negative plane and an ordinary projected pair for the
positive plane, with all four strict Gram--Schmidt signs. -/
theorem exists_projectedBasisMaxwellPrincipalFrameSigns_of_positiveEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm)
    (hindex : HasLorentzianIndexOne g)
    (b : Basis ι ℝ V)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : 0 < q)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hself : MetricSelfAdjoint g S)
    (henergy : HasPositiveMaxwellEnergyDensity g S) :
    ∃ i j : ι, ∃ recipe : LorentzianPivotRecipe, ∃ k l : ι,
      let P := maxwellMinusProjector S q
      let Q := maxwellPlusProjector S q
      let pivot := lorentzianPivotCandidate g (P (b i)) (P (b j)) recipe
      let companion := lorentzianPivotCompanion (P (b i)) (P (b j)) recipe
      g pivot pivot < 0 ∧
        0 < g (metricOrthogonalizeSecond g pivot companion)
          (metricOrthogonalizeSecond g pivot companion) ∧
        0 < g (Q (b k)) (Q (b k)) ∧
        0 < g (metricOrthogonalizeSecond g (Q (b k)) (Q (b l)))
          (metricOrthogonalizeSecond g (Q (b k)) (Q (b l))) := by
  let P := maxwellMinusProjector S q
  let Q := maxwellPlusProjector S q
  have hphysical : HasPhysicalMaxwellEnergySign g S q :=
    hasPhysicalMaxwellEnergySign_of_positiveEnergyDensity
      g hg S q hq hS hself henergy
  obtain ⟨hrankPlus, hrankMinus⟩ :=
    maxwellProjectors_finrank_range_eq_two
      S q (ne_of_gt hq) hS hdim htrace
  obtain ⟨t, ht⟩ :=
    exists_timelike_mem_maxwellMinusProjector_range_of_energySign
      g S q (ne_of_gt hq) hphysical
  obtain ⟨i, j, recipe, htime, hrem⟩ :=
    exists_projectedBasisLorentzianFrameSigns
      g hg hindex b P hrankMinus t ht
  have hPId : P.comp P = P :=
    maxwellMinusProjector_sq S q (ne_of_gt hq) hS
  have hQId : Q.comp Q = Q :=
    maxwellPlusProjector_sq S q (ne_of_gt hq) hS
  have hPself : MetricSelfAdjoint g P :=
    maxwellMinusProjector_metricSelfAdjoint g hg S q hself
  have hPQ : P.comp Q = 0 :=
    maxwellProjectors_comp_zero_rev S q (ne_of_gt hq) hS
  have htFixed : P (t : V) = (t : V) :=
    projector_fixed_of_mem_range P hPId t t.property
  have horth : ∀ z : Q.range, g (t : V) (z : V) = 0 := by
    intro z
    have hzFixed : Q (z : V) = (z : V) :=
      projector_fixed_of_mem_range Q hQId z z.property
    exact complementaryProjector_fixed_orthogonal
      g P Q hPself hPQ t z htFixed hzFixed
  obtain ⟨k, l, hspace, hspaceRem⟩ :=
    exists_projectedBasisSpacelikeFrameSigns
      g hindex b Q hrankPlus t ht horth
  exact ⟨i, j, recipe, k, l, htime, hrem, hspace, hspaceRem⟩

/-- **Pointwise Maxwell principal-tetrad existence.** In a four-dimensional
index-one metric space, a self-adjoint tracefree residual satisfying the
non-null Maxwell square law has a constructive pseudo-orthonormal principal
tetrad as soon as the designated Lorentzian projector range contains a
timelike vector. Rank two of both ranges is now a consequence, not an input. -/
theorem exists_maxwellPrincipalTetrad
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : q ≠ 0)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hself : MetricSelfAdjoint g S)
    (t : (maxwellMinusProjector S q).range)
    (ht : g (t : V) (t : V) < 0) :
    ∃ u0 u1 v0 v1 : V,
      IsPseudoOrthonormalPrincipalTetrad g
        (projectedLorentzianPlaneFrame g (maxwellMinusProjector S q) u0 u1)
        (projectedSpacelikePlaneFrame g (maxwellPlusProjector S q) v0 v1) := by
  obtain ⟨hrankPlus, hrankMinus⟩ :=
    maxwellProjectors_finrank_range_eq_two S q hq hS hdim htrace
  have hMinusId := maxwellMinusProjector_sq S q hq hS
  have hPlusId := maxwellPlusProjector_sq S q hq hS
  have hMinusPlus := maxwellProjectors_comp_zero_rev S q hq hS
  have hMinusSelf := maxwellMinusProjector_metricSelfAdjoint g hg S q hself
  exact exists_projectedPrincipalPlaneFrames_of_rank_two g hg hindex
    (maxwellMinusProjector S q) (maxwellPlusProjector S q)
    hMinusId hPlusId hMinusSelf hMinusPlus hrankMinus hrankPlus t ht

/-- **Adapted Maxwell two-form existence.** Under the pointwise non-null
Rainich hypotheses and the physical positive-`q` branch, there is an adapted
pseudo-orthonormal principal tetrad basis and a real skew bilinear form whose
matrix is the explicit positive-`q` canonical Maxwell seed. -/
theorem exists_adaptedPrincipalMaxwellTwoForm
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : 0 < q)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hself : MetricSelfAdjoint g S)
    (t : (maxwellMinusProjector S q).range)
    (ht : g (t : V) (t : V) < 0) :
    ∃ u0 u1 v0 v1 : V,
      ∃ _hframe : IsPseudoOrthonormalPrincipalTetrad g
          (projectedLorentzianPlaneFrame g (maxwellMinusProjector S q) u0 u1)
          (projectedSpacelikePlaneFrame g (maxwellPlusProjector S q) v0 v1),
        ∃ b : Basis (Fin 4) ℝ V,
          (∀ i, b i = principalTetradVectors
            (projectedLorentzianPlaneFrame g (maxwellMinusProjector S q) u0 u1)
            (projectedSpacelikePlaneFrame g (maxwellPlusProjector S q) v0 v1) i) ∧
          ∃ F : BilinForm ℝ V,
            LinearMap.BilinForm.toMatrix b F =
                canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 ∧
              Matrix.transpose (LinearMap.BilinForm.toMatrix b F) =
                -(LinearMap.BilinForm.toMatrix b F) := by
  obtain ⟨u0, u1, v0, v1, hframe⟩ :=
    exists_maxwellPrincipalTetrad g hg hindex S q (ne_of_gt hq) hS
      hdim htrace hself t ht
  let lorentzFrame :=
    projectedLorentzianPlaneFrame g (maxwellMinusProjector S q) u0 u1
  let spaceFrame :=
    projectedSpacelikePlaneFrame g (maxwellPlusProjector S q) v0 v1
  let b := principalTetradBasis g hg lorentzFrame spaceFrame hframe hdim
  let F := principalPositiveQMaxwellTwoForm b q
  refine ⟨u0, u1, v0, v1, hframe, b, ?_, F, ?_, ?_⟩
  · intro i
    exact principalTetradBasis_apply g hg lorentzFrame spaceFrame hframe hdim i
  · exact principalPositiveQMaxwellTwoForm_toMatrix b q
  · exact principalMaxwellTwoForm_toMatrix_transpose b (Real.sqrt (2 * q)) 0

/-- **Pointwise Maxwell square-root theorem.** Under the non-null Rainich,
index-one, and physical energy-sign hypotheses, the adapted real skew form
constructed above has Maxwell stress exactly equal to the original residual,
not merely a residual with the same square and trace. -/
theorem exists_adaptedPrincipalMaxwellTwoForm_stress_eq
    [FiniteDimensional ℝ V]
    (g : BilinForm ℝ V) (hg : g.IsSymm) (hindex : HasLorentzianIndexOne g)
    (S : V →ₗ[ℝ] V) (q : ℝ) (hq : 0 < q)
    (hS : S * S = q ^ 2 • (1 : V →ₗ[ℝ] V))
    (hdim : finrank ℝ V = 4)
    (htrace : LinearMap.trace ℝ V S = 0)
    (hself : MetricSelfAdjoint g S)
    (t : (maxwellMinusProjector S q).range)
    (ht : g (t : V) (t : V) < 0) :
    ∃ b : Basis (Fin 4) ℝ V, ∃ F : BilinForm ℝ V,
      LinearMap.BilinForm.toMatrix b F =
          canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0 ∧
        Matrix.transpose (LinearMap.BilinForm.toMatrix b F) =
          -(LinearMap.BilinForm.toMatrix b F) ∧
        principalMaxwellStress b F = S := by
  obtain ⟨u0, u1, v0, v1, hframe, b, hb, F, hF, hskew⟩ :=
    exists_adaptedPrincipalMaxwellTwoForm g hg hindex S q hq hS hdim
      htrace hself t ht
  let P := maxwellMinusProjector S q
  let Q := maxwellPlusProjector S q
  have hPid : P.comp P = P := maxwellMinusProjector_sq S q (ne_of_gt hq) hS
  have hQid : Q.comp Q = Q := maxwellPlusProjector_sq S q (ne_of_gt hq) hS
  have hLorFixed :
      P (projectedLorentzianPlaneFrame g P u0 u1).1 =
          (projectedLorentzianPlaneFrame g P u0 u1).1 ∧
        P (projectedLorentzianPlaneFrame g P u0 u1).2 =
          (projectedLorentzianPlaneFrame g P u0 u1).2 := by
    simpa [projectedLorentzianPlaneFrame] using
      lorentzianPlaneFrame_fixed g P (P u0) (P u1)
        (projector_apply_fixed P hPid u0) (projector_apply_fixed P hPid u1)
  have hSpaceFixed :
      Q (projectedSpacelikePlaneFrame g Q v0 v1).1 =
          (projectedSpacelikePlaneFrame g Q v0 v1).1 ∧
        Q (projectedSpacelikePlaneFrame g Q v0 v1).2 =
          (projectedSpacelikePlaneFrame g Q v0 v1).2 := by
    simpa [projectedSpacelikePlaneFrame] using
      spacelikePlaneFrame_fixed g Q (Q v0) (Q v1)
        (projector_apply_fixed Q hQid v0) (projector_apply_fixed Q hQid v1)
  have hb0 : b 0 = (projectedLorentzianPlaneFrame g P u0 u1).1 := by
    simpa [P, Q, principalTetradVectors] using hb (0 : Fin 4)
  have hb1 : b 1 = (projectedLorentzianPlaneFrame g P u0 u1).2 := by
    simpa [P, Q, principalTetradVectors] using hb (1 : Fin 4)
  have hb2 : b 2 = (projectedSpacelikePlaneFrame g Q v0 v1).1 := by
    simpa [P, Q, principalTetradVectors] using hb (2 : Fin 4)
  have hb3 : b 3 = (projectedSpacelikePlaneFrame g Q v0 v1).2 := by
    simpa [P, Q, principalTetradVectors] using hb (3 : Fin 4)
  have hmatrix : LinearMap.toMatrix b b S = canonicalMaxwellResidual q := by
    apply maxwellResidual_toMatrix_eq_canonical S q (ne_of_gt hq) hS b
    · simpa [P, hb0] using hLorFixed.1
    · simpa [P, hb1] using hLorFixed.2
    · simpa [Q, hb2] using hSpaceFixed.1
    · simpa [Q, hb3] using hSpaceFixed.2
  have hcanonical :
      matrixMaxwellStress minkowskiMetric
          (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) =
        canonicalMaxwellResidual q := by
    rw [matrixMaxwellStress_canonical]
    have hc := exists_canonicalMaxwellTwoForm_of_pos q hq
    rw [maxwellStressMixed_canonical] at hc
    exact hc
  refine ⟨b, F, hF, hskew, ?_⟩
  unfold principalMaxwellStress
  rw [hF, hcanonical, ← hmatrix, Matrix.toLin_toMatrix]

end RainichKaluza
