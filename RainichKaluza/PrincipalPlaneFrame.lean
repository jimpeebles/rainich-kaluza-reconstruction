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
