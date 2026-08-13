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

omit [NormedSpace ℝ X] in
/-- Pointwise continuity version of smooth metric contraction. -/
theorem continuousAt_smoothMetricPairing
    {g : X → ContinuousBilinForm V} {x y : X → V} {z : X}
    (hg : ContinuousAt g z) (hx : ContinuousAt x z)
    (hy : ContinuousAt y z) :
    ContinuousAt (smoothMetricPairing g x y) z := by
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

omit [NormedSpace ℝ X] in
/-- The varying Gram--Schmidt remainder is continuous at any point where its
pivot is non-null. -/
theorem continuousAt_smoothMetricOrthogonalizeSecond
    {g : X → ContinuousBilinForm V} {x y : X → V} {z : X}
    (hg : ContinuousAt g z) (hx : ContinuousAt x z)
    (hy : ContinuousAt y z)
    (hxx : smoothMetricPairing g x x z ≠ 0) :
    ContinuousAt (smoothMetricOrthogonalizeSecond g x y) z := by
  have hxy := continuousAt_smoothMetricPairing hg hx hy
  have hxxContinuous := continuousAt_smoothMetricPairing hg hx hx
  exact hy.sub ((hxy.div hxxContinuous hxx).smul hx)

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

/-- Varying version of the finite algebraic Lorentzian pivot candidates. -/
noncomputable def smoothLorentzianPivotCandidate
    (g : X → ContinuousBilinForm V) (x y : X → V)
    (recipe : LorentzianPivotRecipe) (z : X) : V :=
  match recipe with
  | .first => x z
  | .second => y z
  | .firstWeighted =>
      smoothMetricPairing g x y z • x z -
        smoothMetricPairing g x x z • y z
  | .secondWeighted =>
      smoothMetricPairing g y y z • x z -
        smoothMetricPairing g x y z • y z
  | .sum => x z + y z
  | .difference => x z - y z

/-- Varying companion retained by the finite Lorentzian pivot recipe. -/
def smoothLorentzianPivotCompanion
    (x y : X → V) (recipe : LorentzianPivotRecipe) (z : X) : V :=
  match recipe with
  | .first => y z
  | .second => x z
  | .firstWeighted => x z
  | .secondWeighted => y z
  | .sum => x z
  | .difference => x z

/-- Every finite pivot candidate is smooth when the metric and original
projected-vector fields are smooth. -/
theorem contDiffOn_smoothLorentzianPivotCandidate
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V} {x y : X → V}
    (recipe : LorentzianPivotRecipe)
    (hg : ContDiffOn ℝ n g U) (hx : ContDiffOn ℝ n x U)
    (hy : ContDiffOn ℝ n y U) :
    ContDiffOn ℝ n (smoothLorentzianPivotCandidate g x y recipe) U := by
  cases recipe
  · exact hx
  · exact hy
  · exact ((contDiffOn_smoothMetricPairing hg hx hy).smul hx).sub
      ((contDiffOn_smoothMetricPairing hg hx hx).smul hy)
  · exact ((contDiffOn_smoothMetricPairing hg hy hy).smul hx).sub
      ((contDiffOn_smoothMetricPairing hg hx hy).smul hy)
  · exact hx.add hy
  · exact hx.sub hy

omit [NormedSpace ℝ X] in
/-- Every finite pivot candidate is continuous at a point whenever the
metric and original projected-vector fields are continuous there. -/
theorem continuousAt_smoothLorentzianPivotCandidate
    {g : X → ContinuousBilinForm V} {x y : X → V} {z : X}
    (recipe : LorentzianPivotRecipe)
    (hg : ContinuousAt g z) (hx : ContinuousAt x z)
    (hy : ContinuousAt y z) :
    ContinuousAt (smoothLorentzianPivotCandidate g x y recipe) z := by
  cases recipe
  · exact hx
  · exact hy
  · exact ((continuousAt_smoothMetricPairing hg hx hy).smul hx).sub
      ((continuousAt_smoothMetricPairing hg hx hx).smul hy)
  · exact ((continuousAt_smoothMetricPairing hg hy hy).smul hx).sub
      ((continuousAt_smoothMetricPairing hg hx hy).smul hy)
  · exact hx.add hy
  · exact hx.sub hy

/-- Every companion field in the finite pivot construction is smooth. -/
theorem contDiffOn_smoothLorentzianPivotCompanion
    {n : WithTop ℕ∞} {U : Set X} {x y : X → V}
    (recipe : LorentzianPivotRecipe)
    (hx : ContDiffOn ℝ n x U) (hy : ContDiffOn ℝ n y U) :
    ContDiffOn ℝ n (smoothLorentzianPivotCompanion x y recipe) U := by
  cases recipe <;> assumption

omit [NormedSpace ℝ X] [NormedSpace ℝ V] in
/-- Every finite pivot companion is continuous with its input fields. -/
theorem continuousAt_smoothLorentzianPivotCompanion
    {x y : X → V} {z : X} (recipe : LorentzianPivotRecipe)
    (hx : ContinuousAt x z) (hy : ContinuousAt y z) :
    ContinuousAt (smoothLorentzianPivotCompanion x y recipe) z := by
  cases recipe <;> assumption

omit [NormedSpace ℝ X] in
/-- **Local persistence for a finite Lorentzian pivot.** Once one recipe has
the two strict Lorentzian Gram--Schmidt signs at a point, the same discrete
recipe has them throughout a neighborhood. -/
theorem eventually_smoothLorentzianPivotFrameSigns
    {g : X → ContinuousBilinForm V} {x y : X → V} {z : X}
    (recipe : LorentzianPivotRecipe)
    (hg : ContinuousAt g z) (hx : ContinuousAt x z)
    (hy : ContinuousAt y z)
    (htime : smoothMetricPairing g
      (smoothLorentzianPivotCandidate g x y recipe)
      (smoothLorentzianPivotCandidate g x y recipe) z < 0)
    (hrem : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g
        (smoothLorentzianPivotCandidate g x y recipe)
        (smoothLorentzianPivotCompanion x y recipe))
      (smoothMetricOrthogonalizeSecond g
        (smoothLorentzianPivotCandidate g x y recipe)
        (smoothLorentzianPivotCompanion x y recipe)) z) :
    ∀ᶠ w in 𝓝 z,
      smoothMetricPairing g
          (smoothLorentzianPivotCandidate g x y recipe)
          (smoothLorentzianPivotCandidate g x y recipe) w < 0 ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g
            (smoothLorentzianPivotCandidate g x y recipe)
            (smoothLorentzianPivotCompanion x y recipe))
          (smoothMetricOrthogonalizeSecond g
            (smoothLorentzianPivotCandidate g x y recipe)
            (smoothLorentzianPivotCompanion x y recipe)) w := by
  have hpivot :=
    continuousAt_smoothLorentzianPivotCandidate recipe hg hx hy
  have hcompanion :=
    continuousAt_smoothLorentzianPivotCompanion recipe hx hy
  have hpivotPair := continuousAt_smoothMetricPairing hg hpivot hpivot
  have horth := continuousAt_smoothMetricOrthogonalizeSecond
    hg hpivot hcompanion (ne_of_lt htime)
  have horthPair := continuousAt_smoothMetricPairing hg horth horth
  filter_upwards
    [hpivotPair.eventually_lt continuousAt_const htime,
      continuousAt_const.eventually_lt horthPair hrem] with w hw0 hw1
  exact ⟨hw0, hw1⟩

omit [NormedSpace ℝ X] in
/-- Local persistence of the two strict positive-plane Gram--Schmidt signs. -/
theorem eventually_smoothSpacelikeFrameSigns
    {g : X → ContinuousBilinForm V} {x y : X → V} {z : X}
    (hg : ContinuousAt g z) (hx : ContinuousAt x z)
    (hy : ContinuousAt y z)
    (hspace : 0 < smoothMetricPairing g x x z)
    (hrem : 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g x y)
      (smoothMetricOrthogonalizeSecond g x y) z) :
    ∀ᶠ w in 𝓝 z,
      0 < smoothMetricPairing g x x w ∧
        0 < smoothMetricPairing g
          (smoothMetricOrthogonalizeSecond g x y)
          (smoothMetricOrthogonalizeSecond g x y) w := by
  have hpair := continuousAt_smoothMetricPairing hg hx hx
  have horth := continuousAt_smoothMetricOrthogonalizeSecond
    hg hx hy (ne_of_gt hspace)
  have horthPair := continuousAt_smoothMetricPairing hg horth horth
  filter_upwards
    [continuousAt_const.eventually_lt hpair hspace,
      continuousAt_const.eventually_lt horthPair hrem] with w hw0 hw1
  exact ⟨hw0, hw1⟩

/-- A principal tetrad assembled from four already-constructed vector
fields.  This generalizes the fixed-probe tetrad and permits finite
metric-dependent Lorentzian pivot recipes. -/
noncomputable def smoothPrincipalTetradFromFields
    (g : X → ContinuousBilinForm V)
    (lorentzPivot lorentzCompanion spacePivot spaceCompanion : X → V)
    (z : X) : (V × V) × (V × V) :=
  (smoothLorentzianPlaneFrame g lorentzPivot lorentzCompanion z,
    smoothSpacelikePlaneFrame g spacePivot spaceCompanion z)

/-- Smoothness of the field-driven principal tetrad on its strict sign
patch. -/
theorem contDiffOn_smoothPrincipalTetradFromFields
    {n : WithTop ℕ∞} {U : Set X}
    {g : X → ContinuousBilinForm V}
    {lorentzPivot lorentzCompanion spacePivot spaceCompanion : X → V}
    (hg : ContDiffOn ℝ n g U)
    (hLorentzPivot : ContDiffOn ℝ n lorentzPivot U)
    (hLorentzCompanion : ContDiffOn ℝ n lorentzCompanion U)
    (hSpacePivot : ContDiffOn ℝ n spacePivot U)
    (hSpaceCompanion : ContDiffOn ℝ n spaceCompanion U)
    (htime : ∀ z ∈ U,
      smoothMetricPairing g lorentzPivot lorentzPivot z < 0)
    (hLorentzRemainder : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g lorentzPivot lorentzCompanion)
      (smoothMetricOrthogonalizeSecond g lorentzPivot lorentzCompanion) z)
    (hspace : ∀ z ∈ U,
      0 < smoothMetricPairing g spacePivot spacePivot z)
    (hSpaceRemainder : ∀ z ∈ U, 0 < smoothMetricPairing g
      (smoothMetricOrthogonalizeSecond g spacePivot spaceCompanion)
      (smoothMetricOrthogonalizeSecond g spacePivot spaceCompanion) z) :
    ContDiffOn ℝ n
      (smoothPrincipalTetradFromFields g lorentzPivot lorentzCompanion
        spacePivot spaceCompanion) U := by
  exact (contDiffOn_smoothLorentzianPlaneFrame hg hLorentzPivot
    hLorentzCompanion htime hLorentzRemainder).prodMk
      (contDiffOn_smoothSpacelikePlaneFrame hg hSpacePivot hSpaceCompanion
        hspace hSpaceRemainder)

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
