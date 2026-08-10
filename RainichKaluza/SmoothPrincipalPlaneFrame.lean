import RainichKaluza.PrincipalPlaneFrame
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth local principal frames

This file closes the analytic part of the fixed-probe construction.  In a
normed local trivialization, a smooth metric field and smooth projected probe
vectors produce smooth Gram--Schmidt frames on every patch where the explicit
Lorentzian/spacelike sign conditions hold.  Thus no additional smooth-choice
theorem is needed after one admissible set of constant ambient probes has been
selected at the base point.
-/

namespace RainichKaluza

open scoped Topology

variable {X V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Continuous bilinear forms in a normed local trivialization. -/
abbrev ContinuousBilinForm (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  V →L[ℝ] V →L[ℝ] ℝ

/-- Pointwise contraction of a varying continuous bilinear form with two
varying vector fields. -/
noncomputable def smoothMetricPairing
    (g : X → ContinuousBilinForm V) (x y : X → V) (z : X) : ℝ :=
  g z (x z) (y z)

/-- Smooth metric and vector fields have a smooth scalar contraction. -/
theorem contDiffOn_smoothMetricPairing
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x y : X → V}
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (hy : ContDiffOn ℝ n y U) :
    ContDiffOn ℝ n (smoothMetricPairing g x y) U := by
  exact (hg.clm_apply hx).clm_apply hy

/-- Gram--Schmidt remainder for varying metric/vector fields. -/
noncomputable def smoothMetricOrthogonalizeSecond
    (g : X → ContinuousBilinForm V) (x y : X → V) (z : X) : V :=
  y z -
    (smoothMetricPairing g x y z / smoothMetricPairing g x x z) • x z

/-- The varying Gram--Schmidt remainder is smooth wherever its pivot is
non-null. -/
theorem contDiffOn_smoothMetricOrthogonalizeSecond
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x y : X → V}
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (hy : ContDiffOn ℝ n y U)
    (hxx : ∀ z ∈ U, smoothMetricPairing g x x z ≠ 0) :
    ContDiffOn ℝ n (smoothMetricOrthogonalizeSecond g x y) U := by
  have hxy := contDiffOn_smoothMetricPairing hg hx hy
  have hxxSmooth := contDiffOn_smoothMetricPairing hg hx hx
  exact hy.sub ((hxy.div hxxSmooth hxx).smul hx)

/-- Smooth timelike normalization in a varying metric. -/
noncomputable def smoothNormalizeTimelike
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X) : V :=
  (Real.sqrt (-smoothMetricPairing g x x z))⁻¹ • x z

/-- Timelike normalization is smooth on a strictly timelike patch. -/
theorem contDiffOn_smoothNormalizeTimelike
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x : X → V}
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (htime : ∀ z ∈ U, smoothMetricPairing g x x z < 0) :
    ContDiffOn ℝ n (smoothNormalizeTimelike g x) U := by
  have hnorm := (contDiffOn_smoothMetricPairing hg hx hx).neg
  have hsqrt := hnorm.sqrt (fun z hz => by
    have := htime z hz
    linarith)
  have hsqrtNe : ∀ z ∈ U,
      Real.sqrt (-smoothMetricPairing g x x z) ≠ 0 := by
    intro z hz
    exact Real.sqrt_ne_zero'.mpr (by linarith [htime z hz])
  exact (hsqrt.inv hsqrtNe).smul hx

/-- Smooth spacelike normalization in a varying metric. -/
noncomputable def smoothNormalizeSpacelike
    (g : X → ContinuousBilinForm V) (x : X → V) (z : X) : V :=
  (Real.sqrt (smoothMetricPairing g x x z))⁻¹ • x z

/-- Spacelike normalization is smooth on a strictly spacelike patch. -/
theorem contDiffOn_smoothNormalizeSpacelike
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x : X → V}
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (hspace : ∀ z ∈ U, 0 < smoothMetricPairing g x x z) :
    ContDiffOn ℝ n (smoothNormalizeSpacelike g x) U := by
  have hnorm := contDiffOn_smoothMetricPairing hg hx hx
  have hsqrt := hnorm.sqrt (fun z hz => ne_of_gt (hspace z hz))
  have hsqrtNe : ∀ z ∈ U,
      Real.sqrt (smoothMetricPairing g x x z) ≠ 0 := by
    intro z hz
    exact Real.sqrt_ne_zero'.mpr (hspace z hz)
  exact (hsqrt.inv hsqrtNe).smul hx

/-- Smooth Lorentzian two-plane frame field. -/
noncomputable def smoothLorentzianPlaneFrame
    (g : X → ContinuousBilinForm V) (x y : X → V) (z : X) : V × V :=
  (smoothNormalizeTimelike g x z,
    smoothNormalizeSpacelike g
      (smoothMetricOrthogonalizeSecond g x y) z)

/-- The explicit Lorentzian Gram--Schmidt frame is `C^n` on its strict sign
patch. -/
theorem contDiffOn_smoothLorentzianPlaneFrame
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x y : X → V}
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (hy : ContDiffOn ℝ n y U)
    (htime : ∀ z ∈ U, smoothMetricPairing g x x z < 0)
    (hrem : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g x y) z) :
    ContDiffOn ℝ n (smoothLorentzianPlaneFrame g x y) U := by
  have hxx : ∀ z ∈ U, smoothMetricPairing g x x z ≠ 0 :=
    fun z hz => ne_of_lt (htime z hz)
  have horth := contDiffOn_smoothMetricOrthogonalizeSecond hg hx hy hxx
  exact (contDiffOn_smoothNormalizeTimelike hg hx htime).prodMk
    (contDiffOn_smoothNormalizeSpacelike hg horth hrem)

/-- Smooth positive-definite two-plane frame field. -/
noncomputable def smoothSpacelikePlaneFrame
    (g : X → ContinuousBilinForm V) (x y : X → V) (z : X) : V × V :=
  (smoothNormalizeSpacelike g x z,
    smoothNormalizeSpacelike g
      (smoothMetricOrthogonalizeSecond g x y) z)

/-- The explicit spacelike Gram--Schmidt frame is `C^n` on its strict sign
patch. -/
theorem contDiffOn_smoothSpacelikePlaneFrame
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x y : X → V}
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (hy : ContDiffOn ℝ n y U)
    (hspace : ∀ z ∈ U, 0 < smoothMetricPairing g x x z)
    (hrem : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g x y) z) :
    ContDiffOn ℝ n (smoothSpacelikePlaneFrame g x y) U := by
  have hxx : ∀ z ∈ U, smoothMetricPairing g x x z ≠ 0 :=
    fun z hz => ne_of_gt (hspace z hz)
  have horth := contDiffOn_smoothMetricOrthogonalizeSecond hg hx hy hxx
  exact (contDiffOn_smoothNormalizeSpacelike hg hx hspace).prodMk
    (contDiffOn_smoothNormalizeSpacelike hg horth hrem)

/-- A fixed ambient probe projected by a varying continuous projector. -/
def smoothProjectedVector (P : X → V →L[ℝ] V) (u : V) (z : X) : V :=
  P z u

/-- Constant probes become smooth vector fields after application of a smooth
projector field. -/
theorem contDiffOn_smoothProjectedVector
    {n : WithTop ℕ∞} {U : Set X}
    {P : X → V →L[ℝ] V} (hP : ContDiffOn ℝ n P U) (u : V) :
    ContDiffOn ℝ n (smoothProjectedVector P u) U := by
  exact hP.clm_apply contDiffOn_const

/-- The full fixed-probe principal tetrad in a local trivialization. -/
noncomputable def smoothProjectedPrincipalTetrad
    (g : X → ContinuousBilinForm V) (P Q : X → V →L[ℝ] V)
    (u0 u1 v0 v1 : V) (z : X) : (V × V) × (V × V) :=
  (smoothLorentzianPlaneFrame g
      (smoothProjectedVector P u0) (smoothProjectedVector P u1) z,
    smoothSpacelikePlaneFrame g
      (smoothProjectedVector Q v0) (smoothProjectedVector Q v1) z)

/-- **Smooth fixed-probe principal-tetrad theorem.** Smooth metric/projector
fields and one fixed admissible probe quadruple give a smooth local tetrad on
the entire strict Gram-sign patch. -/
theorem contDiffOn_smoothProjectedPrincipalTetrad
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {P Q : X → V →L[ℝ] V}
    (u0 u1 v0 v1 : V)
    (hg : ContDiffOn ℝ n g U) (hP : ContDiffOn ℝ n P U)
    (hQ : ContDiffOn ℝ n Q U)
    (hL0 : ∀ z ∈ U, smoothMetricPairing g
      (smoothProjectedVector P u0) (smoothProjectedVector P u0) z < 0)
    (hL1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothProjectedVector P u0) (smoothProjectedVector P u1))
      (smoothMetricOrthogonalizeSecond g
        (smoothProjectedVector P u0) (smoothProjectedVector P u1)) z)
    (hS0 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothProjectedVector Q v0) (smoothProjectedVector Q v0) z)
    (hS1 : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothProjectedVector Q v0) (smoothProjectedVector Q v1))
      (smoothMetricOrthogonalizeSecond g
        (smoothProjectedVector Q v0) (smoothProjectedVector Q v1)) z) :
    ContDiffOn ℝ n
      (smoothProjectedPrincipalTetrad g P Q u0 u1 v0 v1) U := by
  have hPu0 := contDiffOn_smoothProjectedVector hP u0
  have hPu1 := contDiffOn_smoothProjectedVector hP u1
  have hQv0 := contDiffOn_smoothProjectedVector hQ v0
  have hQv1 := contDiffOn_smoothProjectedVector hQ v1
  exact (contDiffOn_smoothLorentzianPlaneFrame hg hPu0 hPu1 hL0 hL1).prodMk
    (contDiffOn_smoothSpacelikePlaneFrame hg hQv0 hQv1 hS0 hS1)

end RainichKaluza
