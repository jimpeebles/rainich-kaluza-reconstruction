import RainichKaluza.CoordinateEinsteinRegularity
import RainichKaluza.MatterStressDivergence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Differentiating the Einstein matter source at a normal point

This file isolates the source-side first-jet calculation needed by the
normal-coordinate scalar-equation bridge.  It defines the source with honest
mixed indices: inverse-metric raising is performed by the coordinate metric,
and the first index is lowered again before comparison with the covariant
Einstein tensor.  It then proves the complete fixed-Minkowski first variations
for the scalar and Maxwell pieces.

It then closes the moving-metric seam: at a Minkowski normal point the
inverse-metric and final lowering variations vanish, so the honest covariant
source derivative reduces to those fixed-frame formulas.  An eventual
neighborhood Einstein/source equality is differentiated and contracted to
the exact raw matter-divergence identity used by the Noether bridge.  What
remains external to this file is constructing that neighborhood equality and
the scalar/Maxwell fields from the full converse hypotheses.
-/

namespace RainichKaluza

open scoped Matrix Topology

/-- Raise a covector with an arbitrary inverse coordinate metric. -/
noncomputable def coordinateRaisedOneForm4
    (gInv : Matrix4) (v : OneForm4) : OneForm4 :=
  fun i => ∑ k, gInv i k * v k

/-- Raise both indices of a covariant two-form with an arbitrary inverse
coordinate metric. -/
noncomputable def coordinateRaisedTwoForm4
    (gInv : Matrix4) (F : Matrix4) : Matrix4 :=
  fun i j => ∑ p, ∑ q, gInv i p * gInv j q * F p q

/-- The mixed scalar part of the trace-reversed Einstein source. -/
noncomputable def coordinateScalarEinsteinStressMixed4
    (gInv : Matrix4) (v : OneForm4) : Matrix4 :=
  fun i j =>
    (1 / 2 : ℝ) * coordinateRaisedOneForm4 gInv v i * v j -
      (1 / 4 : ℝ) * (if i = j then 1 else 0) *
        (∑ k, coordinateRaisedOneForm4 gInv v k * v k)

/-- The ordinary mixed Maxwell stress in component form. -/
noncomputable def coordinateMaxwellEinsteinStressMixed4
    (gInv : Matrix4) (F : Matrix4) : Matrix4 :=
  fun i j =>
    (∑ r, coordinateRaisedTwoForm4 gInv F i r * F j r) -
      (1 / 4 : ℝ) * (if i = j then 1 else 0) *
        (∑ p, ∑ q, coordinateRaisedTwoForm4 gInv F p q * F p q)

/-- Complete mixed scalar-plus-Maxwell Einstein source. -/
noncomputable def coordinateMatterEinsteinStressMixed4
    (gInv : Matrix4) (v : OneForm4) (F : Matrix4) : Matrix4 :=
  coordinateScalarEinsteinStressMixed4 gInv v +
    coordinateMaxwellEinsteinStressMixed4 gInv F

/-- Lower the first index of the mixed matter source.  This is the covariant
tensor that can be equated to `actualCoordinateEinsteinField4`. -/
noncomputable def coordinateMatterEinsteinStressCovariant4
    (g gInv : Matrix4) (v : OneForm4) (F : Matrix4) : Matrix4 :=
  fun i j => ∑ k, g i k * coordinateMatterEinsteinStressMixed4 gInv v F k j

/-- The literal covariant matter source built from an actual coordinate
metric, its matrix inverse, a scalar covector field, and a Maxwell two-form
field. -/
noncomputable def actualCoordinateMatterEinsteinStressCovariantField4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (y : CurvatureCoordinateSpace4) : Matrix4 :=
  coordinateMatterEinsteinStressCovariant4
    (coordinateMetricMatrixField4 g y)
    ((coordinateMetricMatrixField4 g y)⁻¹ : Matrix4)
    (vField y) (FField y)

private theorem scalarFieldCoordinateFDeriv_add_source
    (f h : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y + h y) z r =
      scalarFieldCoordinateFDeriv f z r +
        scalarFieldCoordinateFDeriv h z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f + h) z) _ = _
  rw [fderiv_add hf hh]
  rfl

private theorem scalarFieldCoordinateFDeriv_sub_source
    (f h : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y - h y) z r =
      scalarFieldCoordinateFDeriv f z r -
        scalarFieldCoordinateFDeriv h z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f - h) z) _ = _
  rw [fderiv_sub hf hh]
  rfl

private theorem scalarFieldCoordinateFDeriv_mul_source
    (f h : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y * h y) z r =
      scalarFieldCoordinateFDeriv f z r * h z +
        f z * scalarFieldCoordinateFDeriv h z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f * h) z) _ = _
  rw [fderiv_mul hf hh]
  simp
  ring

private theorem scalarFieldCoordinateFDeriv_const_mul_source
    (c : ℝ) (f : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) :
    scalarFieldCoordinateFDeriv (fun y ↦ c * f y) z r =
      c * scalarFieldCoordinateFDeriv f z r := by
  rw [scalarFieldCoordinateFDeriv_mul_source
    (fun _ ↦ c) f z r (by fun_prop) hf]
  simp [scalarFieldCoordinateFDeriv]

private theorem scalarFieldCoordinateFDeriv_sum_source
    {I : Type*} [Fintype I]
    (f : I → CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    scalarFieldCoordinateFDeriv (fun y ↦ ∑ i, f i y) z r =
      ∑ i, scalarFieldCoordinateFDeriv (f i) z r := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y ↦ ∑ i, f i y) = ∑ i, f i by
    funext y
    simp]
  rw [fderiv_sum]
  simp
  exact fun i _ ↦ hf i

private theorem scalarFieldCoordinateFDeriv_sum_mul_source
    {I : Type*} [Fintype I]
    (f h : I → CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z)
    (hh : ∀ i, DifferentiableAt ℝ (h i) z) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ ∑ i, f i y * h i y) z r =
      ∑ i, (scalarFieldCoordinateFDeriv (f i) z r * h i z +
        f i z * scalarFieldCoordinateFDeriv (h i) z r) := by
  rw [scalarFieldCoordinateFDeriv_sum_source]
  · apply Finset.sum_congr rfl
    intro i _
    exact scalarFieldCoordinateFDeriv_mul_source
      (f i) (h i) z r (hf i) (hh i)
  · intro i
    exact (hf i).mul (hh i)

private theorem scalarFieldCoordinateFDeriv_double_sum_mul_source
    {I J : Type*} [Fintype I] [Fintype J]
    (f h : I → J → CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : ∀ i j, DifferentiableAt ℝ (f i j) z)
    (hh : ∀ i j, DifferentiableAt ℝ (h i j) z) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ ∑ i, ∑ j, f i j y * h i j y) z r =
      ∑ i, ∑ j,
        (scalarFieldCoordinateFDeriv (f i j) z r * h i j z +
          f i j z * scalarFieldCoordinateFDeriv (h i j) z r) := by
  rw [scalarFieldCoordinateFDeriv_sum_source]
  · apply Finset.sum_congr rfl
    intro i _
    exact scalarFieldCoordinateFDeriv_sum_mul_source
      (f i) (h i) z r (hf i) (hh i)
  · intro i
    fun_prop

/-- Differentiating the scalar source while the normal metric is fixed gives
the displayed scalar first variation. -/
theorem scalarFieldCoordinateFDeriv_normalScalarEinsteinStressMixed
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) (Dv : Fin 4 → OneForm4)
    (r i j : Fin 4)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ normalScalarEinsteinStressMixed (vField y) i j) z r =
      normalScalarEinsteinStressMixedFirstVariation (vField z) (Dv r) i j := by
  unfold normalScalarEinsteinStressMixed
    normalScalarEinsteinStressMixedFirstVariation
    normalScalarGradientSq normalRaisedOneForm
  rw [show (fun y ↦
      (1 / 2 : ℝ) * (minkowskiSign i * vField y i) * vField y j -
        (1 / 4 : ℝ) * (if i = j then 1 else 0) *
          (∑ k, minkowskiSign k * vField y k * vField y k)) =
      (fun y ↦
        (1 / 2 : ℝ) * ((minkowskiSign i * vField y i) * vField y j) -
          ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
            (∑ k, (minkowskiSign k * vField y k) * vField y k)) by
    funext y
    ring]
  have hfirst : scalarFieldCoordinateFDeriv
      (fun y ↦ (1 / 2 : ℝ) *
        ((minkowskiSign i * vField y i) * vField y j)) z r =
      (1 / 2 : ℝ) *
        (minkowskiSign i * Dv r i * vField z j +
          minkowskiSign i * vField z i * Dv r j) := by
    rw [scalarFieldCoordinateFDeriv_const_mul_source,
      scalarFieldCoordinateFDeriv_mul_source]
    · rw [scalarFieldCoordinateFDeriv_const_mul_source]
      simp_rw [hvJet]
      all_goals exact hv _
    all_goals fun_prop
  have htrace : scalarFieldCoordinateFDeriv
      (fun y ↦ ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ k, (minkowskiSign k * vField y k) * vField y k)) z r =
      ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ k, (minkowskiSign k * Dv r k * vField z k +
          minkowskiSign k * vField z k * Dv r k)) := by
    rw [scalarFieldCoordinateFDeriv_const_mul_source,
      scalarFieldCoordinateFDeriv_sum_mul_source]
    apply congrArg
    apply Finset.sum_congr rfl
    intro k _
    rw [scalarFieldCoordinateFDeriv_const_mul_source]
    simp_rw [hvJet]
    all_goals fun_prop
  rw [scalarFieldCoordinateFDeriv_sub_source, hfirst, htrace]
  all_goals fun_prop

/-- Differentiating the Maxwell source while the normal metric is fixed gives
the displayed Maxwell first variation. -/
theorem scalarFieldCoordinateFDeriv_normalMaxwellEinsteinStressMixed
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) (DF : Fin 4 → Matrix4)
    (r i j : Fin 4)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q) :
    scalarFieldCoordinateFDeriv
        (fun y ↦
          (∑ s, normalRaisedTwoForm (FField y) i s * FField y j s) -
            (1 / 4 : ℝ) * (if i = j then 1 else 0) *
              (∑ p, ∑ q,
                normalRaisedTwoForm (FField y) p q * FField y p q)) z r =
      normalMaxwellStressMixedFirstVariation (FField z) (DF r) i j := by
  unfold normalMaxwellStressMixedFirstVariation normalRaisedTwoForm
  have hFJetSign (p q : Fin 4) :
      scalarFieldCoordinateFDeriv
        (fun y ↦ minkowskiSign p * minkowskiSign q * FField y p q) z r =
        minkowskiSign p * minkowskiSign q * DF r p q := by
    rw [show (fun y ↦ minkowskiSign p * minkowskiSign q * FField y p q) =
      (fun y ↦ (minkowskiSign p * minkowskiSign q) * FField y p q) by
        rfl,
      scalarFieldCoordinateFDeriv_const_mul_source, hFJet]
    exact hF p q
  have hcore : scalarFieldCoordinateFDeriv
      (fun y ↦ ∑ s,
        (minkowskiSign i * minkowskiSign s * FField y i s) *
          FField y j s) z r =
      ∑ s,
        (minkowskiSign i * minkowskiSign s * DF r i s * FField z j s +
          minkowskiSign i * minkowskiSign s * FField z i s * DF r j s) := by
    rw [scalarFieldCoordinateFDeriv_sum_mul_source
      (fun s y ↦ minkowskiSign i * minkowskiSign s * FField y i s)
      (fun s y ↦ FField y j s) z r]
    · simp_rw [hFJetSign, hFJet]
    · intro s
      fun_prop
    · intro s
      exact hF j s
  have htrace : scalarFieldCoordinateFDeriv
      (fun y ↦ ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ p, ∑ q,
          (minkowskiSign p * minkowskiSign q * FField y p q) *
            FField y p q)) z r =
      ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ p, ∑ q,
          (minkowskiSign p * minkowskiSign q * DF r p q * FField z p q +
            minkowskiSign p * minkowskiSign q * FField z p q * DF r p q)) := by
    rw [scalarFieldCoordinateFDeriv_const_mul_source,
      scalarFieldCoordinateFDeriv_double_sum_mul_source
        (fun p q y ↦ minkowskiSign p * minkowskiSign q * FField y p q)
        (fun p q y ↦ FField y p q) z r]
    · simp_rw [hFJetSign, hFJet]
    · intro p q
      fun_prop
    · exact hF
    · fun_prop
  rw [scalarFieldCoordinateFDeriv_sub_source, hcore, htrace]
  · rw [Finset.sum_add_distrib]
  all_goals fun_prop

/-! ## First-order reduction of an honest moving metric -/

/-- At a point where an inverse-metric field has Minkowski value and zero
first jet, raising a moving scalar covector has the same first variation as
raising its variation in the fixed normal frame. -/
private theorem scalarFieldCoordinateFDeriv_coordinateRaisedOneForm4_of_normal
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) (Dv : Fin 4 → OneForm4)
    (r i : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hgInvValue : gInvField z = minkowskiMetric)
    (hgInvJet : ∀ a b,
      scalarFieldCoordinateFDeriv (fun y ↦ gInvField y a b) z r = 0)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateRaisedOneForm4 (gInvField y) (vField y) i) z r =
      normalRaisedOneForm (Dv r) i := by
  unfold coordinateRaisedOneForm4
  rw [scalarFieldCoordinateFDeriv_sum_mul_source]
  · simp_rw [hgInvJet, hvJet, hgInvValue]
    fin_cases i <;>
      simp [normalRaisedOneForm, minkowskiMetric, minkowskiSign,
        Fin.sum_univ_succ]
  · exact hgInv i
  · exact hv

private theorem differentiableAt_coordinateRaisedOneForm4_apply
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) (i : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateRaisedOneForm4 (gInvField y) (vField y) i) z := by
  unfold coordinateRaisedOneForm4
  fun_prop

private theorem differentiableAt_coordinateRaisedTwoForm4_apply
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) (i j : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateRaisedTwoForm4 (gInvField y) (FField y) i j) z := by
  unfold coordinateRaisedTwoForm4
  fun_prop

/-- The corresponding fixed-normal first-variation formula for raising both
indices of a moving two-form. -/
private theorem scalarFieldCoordinateFDeriv_coordinateRaisedTwoForm4_of_normal
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) (DF : Fin 4 → Matrix4)
    (r i j : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hgInvValue : gInvField z = minkowskiMetric)
    (hgInvJet : ∀ a b,
      scalarFieldCoordinateFDeriv (fun y ↦ gInvField y a b) z r = 0)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateRaisedTwoForm4 (gInvField y) (FField y) i j) z r =
      normalRaisedTwoForm (DF r) i j := by
  unfold coordinateRaisedTwoForm4
  have hproduct (p q : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ gInvField y i p * gInvField y j q * FField y p q) z r =
        (scalarFieldCoordinateFDeriv
              (fun y ↦ gInvField y i p) z r * gInvField z j q +
            gInvField z i p * scalarFieldCoordinateFDeriv
              (fun y ↦ gInvField y j q) z r) * FField z p q +
          (gInvField z i p * gInvField z j q) *
            scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r := by
    rw [show (fun y ↦
        gInvField y i p * gInvField y j q * FField y p q) =
        (fun y ↦
          (gInvField y i p * gInvField y j q) * FField y p q) by rfl,
      scalarFieldCoordinateFDeriv_mul_source,
      scalarFieldCoordinateFDeriv_mul_source]
    all_goals fun_prop
  have hinner (p : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ ∑ q, gInvField y i p * gInvField y j q * FField y p q) z r =
        ∑ q, scalarFieldCoordinateFDeriv
          (fun y ↦ gInvField y i p * gInvField y j q * FField y p q) z r := by
    apply scalarFieldCoordinateFDeriv_sum_source
    intro q
    fun_prop
  rw [scalarFieldCoordinateFDeriv_sum_source]
  · simp_rw [hinner, hproduct, hgInvJet, hFJet, hgInvValue]
    fin_cases i <;> fin_cases j <;>
      simp [normalRaisedTwoForm, minkowskiMetric, minkowskiSign,
        Fin.sum_univ_succ]
  · intro p
    fun_prop

/-- With a moving inverse metric whose value and first jet are normal, the
honest mixed scalar source reduces exactly to the already-audited fixed-frame
first variation. -/
private theorem scalarFieldCoordinateFDeriv_coordinateScalarEinsteinStressMixed4_of_normal
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) (Dv : Fin 4 → OneForm4)
    (r i j : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hgInvValue : gInvField z = minkowskiMetric)
    (hgInvJet : ∀ a b,
      scalarFieldCoordinateFDeriv (fun y ↦ gInvField y a b) z r = 0)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateScalarEinsteinStressMixed4
          (gInvField y) (vField y) i j) z r =
      normalScalarEinsteinStressMixedFirstVariation (vField z) (Dv r) i j := by
  unfold coordinateScalarEinsteinStressMixed4
  have hRaisedDiff (k : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateRaisedOneForm4 (gInvField y) (vField y) k) z :=
    differentiableAt_coordinateRaisedOneForm4_apply
      gInvField vField z k hgInv hv
  have hRaisedJet (k : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateRaisedOneForm4 (gInvField y) (vField y) k) z r =
        normalRaisedOneForm (Dv r) k :=
    scalarFieldCoordinateFDeriv_coordinateRaisedOneForm4_of_normal
      gInvField vField z Dv r k hgInv hgInvValue hgInvJet hv hvJet
  have hRaisedValue (k : Fin 4) : coordinateRaisedOneForm4
      (gInvField z) (vField z) k = normalRaisedOneForm (vField z) k := by
    rw [hgInvValue]
    fin_cases k <;>
      simp [coordinateRaisedOneForm4, normalRaisedOneForm,
        minkowskiMetric, minkowskiSign, Fin.sum_univ_succ]
  have hcoreDiff : DifferentiableAt ℝ
      (fun y ↦ (1 / 2 : ℝ) *
        (coordinateRaisedOneForm4 (gInvField y) (vField y) i *
          vField y j)) z :=
    ((hRaisedDiff i).mul (hv j)).const_mul _
  have htraceSumDiff : DifferentiableAt ℝ
      (fun y ↦ ∑ k, coordinateRaisedOneForm4
        (gInvField y) (vField y) k * vField y k) z := by
    rw [show (fun y ↦ ∑ k, coordinateRaisedOneForm4
        (gInvField y) (vField y) k * vField y k) =
      ∑ k, (fun y ↦ coordinateRaisedOneForm4
        (gInvField y) (vField y) k * vField y k) by rfl]
    apply DifferentiableAt.sum
    intro k _
    exact (hRaisedDiff k).mul (hv k)
  have htraceDiff : DifferentiableAt ℝ
      (fun y ↦ ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ k, coordinateRaisedOneForm4
          (gInvField y) (vField y) k * vField y k)) z :=
    htraceSumDiff.const_mul _
  have hcoreJet : scalarFieldCoordinateFDeriv
      (fun y ↦ (1 / 2 : ℝ) *
        (coordinateRaisedOneForm4 (gInvField y) (vField y) i *
          vField y j)) z r =
      (1 / 2 : ℝ) *
        (normalRaisedOneForm (Dv r) i * vField z j +
          normalRaisedOneForm (vField z) i * Dv r j) := by
    calc
      _ = (1 / 2 : ℝ) * scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateRaisedOneForm4
            (gInvField y) (vField y) i * vField y j) z r :=
        scalarFieldCoordinateFDeriv_const_mul_source
          (1 / 2 : ℝ) _ z r ((hRaisedDiff i).mul (hv j))
      _ = _ := by
        rw [scalarFieldCoordinateFDeriv_mul_source _ _ z r
            (hRaisedDiff i) (hv j),
          hRaisedJet, hRaisedValue, hvJet]
  have htraceJet : scalarFieldCoordinateFDeriv
      (fun y ↦ ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ k, coordinateRaisedOneForm4
          (gInvField y) (vField y) k * vField y k)) z r =
      ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ k, (normalRaisedOneForm (Dv r) k * vField z k +
          normalRaisedOneForm (vField z) k * Dv r k)) := by
    calc
      _ = ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
          scalarFieldCoordinateFDeriv
            (fun y ↦ ∑ k, coordinateRaisedOneForm4
              (gInvField y) (vField y) k * vField y k) z r :=
        scalarFieldCoordinateFDeriv_const_mul_source _ _ z r htraceSumDiff
      _ = _ := by
        rw [scalarFieldCoordinateFDeriv_sum_mul_source _ _ z r hRaisedDiff hv]
        simp_rw [hRaisedJet, hRaisedValue, hvJet]
  rw [show (fun y ↦
      (1 / 2 : ℝ) *
          coordinateRaisedOneForm4 (gInvField y) (vField y) i * vField y j -
        (1 / 4 : ℝ) * (if i = j then 1 else 0) *
          (∑ k, coordinateRaisedOneForm4 (gInvField y) (vField y) k *
            vField y k)) =
      (fun y ↦
        (1 / 2 : ℝ) *
            (coordinateRaisedOneForm4 (gInvField y) (vField y) i * vField y j) -
          ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
            (∑ k, coordinateRaisedOneForm4 (gInvField y) (vField y) k *
              vField y k)) by
    funext y
    ring]
  rw [scalarFieldCoordinateFDeriv_sub_source _ _ z r hcoreDiff htraceDiff,
    hcoreJet, htraceJet]
  unfold normalScalarEinsteinStressMixedFirstVariation
  ring

/-- The Maxwell analogue of the moving-metric reduction: all terms coming
from the inverse metric disappear at a normal point, leaving precisely the
fixed-Minkowski first variation. -/
private theorem scalarFieldCoordinateFDeriv_coordinateMaxwellEinsteinStressMixed4_of_normal
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) (DF : Fin 4 → Matrix4)
    (r i j : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hgInvValue : gInvField z = minkowskiMetric)
    (hgInvJet : ∀ a b,
      scalarFieldCoordinateFDeriv (fun y ↦ gInvField y a b) z r = 0)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateMaxwellEinsteinStressMixed4
          (gInvField y) (FField y) i j) z r =
      normalMaxwellStressMixedFirstVariation (FField z) (DF r) i j := by
  have hRaisedDiff (p q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateRaisedTwoForm4
        (gInvField y) (FField y) p q) z :=
    differentiableAt_coordinateRaisedTwoForm4_apply
      gInvField FField z p q hgInv hF
  have hRaisedJet (p q : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateRaisedTwoForm4
            (gInvField y) (FField y) p q) z r =
        normalRaisedTwoForm (DF r) p q :=
    scalarFieldCoordinateFDeriv_coordinateRaisedTwoForm4_of_normal
      gInvField FField z DF r p q hgInv hgInvValue hgInvJet hF hFJet
  have hRaisedValue (p q : Fin 4) : coordinateRaisedTwoForm4
      (gInvField z) (FField z) p q = normalRaisedTwoForm (FField z) p q := by
    rw [hgInvValue]
    fin_cases p <;> fin_cases q <;>
      simp [coordinateRaisedTwoForm4, normalRaisedTwoForm,
        minkowskiMetric, minkowskiSign, Fin.sum_univ_succ]
  have hcoreDiff : DifferentiableAt ℝ
      (fun y ↦ ∑ s, coordinateRaisedTwoForm4
        (gInvField y) (FField y) i s * FField y j s) z := by
    rw [show (fun y ↦ ∑ s, coordinateRaisedTwoForm4
        (gInvField y) (FField y) i s * FField y j s) =
      ∑ s, (fun y ↦ coordinateRaisedTwoForm4
        (gInvField y) (FField y) i s * FField y j s) by rfl]
    apply DifferentiableAt.sum
    intro s _
    exact (hRaisedDiff i s).mul (hF j s)
  have htraceSumDiff : DifferentiableAt ℝ
      (fun y ↦ ∑ p, ∑ q, coordinateRaisedTwoForm4
        (gInvField y) (FField y) p q * FField y p q) z := by
    rw [show (fun y ↦ ∑ p, ∑ q, coordinateRaisedTwoForm4
        (gInvField y) (FField y) p q * FField y p q) =
      ∑ p, (fun y ↦ ∑ q, coordinateRaisedTwoForm4
        (gInvField y) (FField y) p q * FField y p q) by rfl]
    apply DifferentiableAt.sum
    intro p _
    rw [show (fun y ↦ ∑ q, coordinateRaisedTwoForm4
        (gInvField y) (FField y) p q * FField y p q) =
      ∑ q, (fun y ↦ coordinateRaisedTwoForm4
        (gInvField y) (FField y) p q * FField y p q) by rfl]
    apply DifferentiableAt.sum
    intro q _
    exact (hRaisedDiff p q).mul (hF p q)
  have htraceDiff : DifferentiableAt ℝ
      (fun y ↦ ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ p, ∑ q, coordinateRaisedTwoForm4
          (gInvField y) (FField y) p q * FField y p q)) z :=
    htraceSumDiff.const_mul _
  have hcoreJet : scalarFieldCoordinateFDeriv
      (fun y ↦ ∑ s, coordinateRaisedTwoForm4
        (gInvField y) (FField y) i s * FField y j s) z r =
      (∑ s, normalRaisedTwoForm (DF r) i s * FField z j s) +
        (∑ s, normalRaisedTwoForm (FField z) i s * DF r j s) := by
    rw [scalarFieldCoordinateFDeriv_sum_mul_source _ _ z r
      (fun s ↦ hRaisedDiff i s) (hF j)]
    simp_rw [hRaisedJet, hRaisedValue, hFJet]
    rw [Finset.sum_add_distrib]
  have htraceJet : scalarFieldCoordinateFDeriv
      (fun y ↦ ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ p, ∑ q, coordinateRaisedTwoForm4
          (gInvField y) (FField y) p q * FField y p q)) z r =
      ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
        (∑ p, ∑ q,
          (normalRaisedTwoForm (DF r) p q * FField z p q +
            normalRaisedTwoForm (FField z) p q * DF r p q)) := by
    calc
      _ = ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
          scalarFieldCoordinateFDeriv
            (fun y ↦ ∑ p, ∑ q, coordinateRaisedTwoForm4
              (gInvField y) (FField y) p q * FField y p q) z r :=
        scalarFieldCoordinateFDeriv_const_mul_source _ _ z r htraceSumDiff
      _ = _ := by
        rw [scalarFieldCoordinateFDeriv_double_sum_mul_source
          (fun p q y ↦ coordinateRaisedTwoForm4
            (gInvField y) (FField y) p q)
          (fun p q y ↦ FField y p q) z r hRaisedDiff hF]
        simp_rw [hRaisedJet, hRaisedValue, hFJet]
  unfold coordinateMaxwellEinsteinStressMixed4
  rw [show (fun y ↦
      (∑ s, coordinateRaisedTwoForm4
          (gInvField y) (FField y) i s * FField y j s) -
        (1 / 4 : ℝ) * (if i = j then 1 else 0) *
          (∑ p, ∑ q, coordinateRaisedTwoForm4
            (gInvField y) (FField y) p q * FField y p q)) =
      (fun y ↦
        (∑ s, coordinateRaisedTwoForm4
          (gInvField y) (FField y) i s * FField y j s) -
        ((1 / 4 : ℝ) * (if i = j then 1 else 0)) *
          (∑ p, ∑ q, coordinateRaisedTwoForm4
            (gInvField y) (FField y) p q * FField y p q)) by
    funext y
    ring]
  rw [scalarFieldCoordinateFDeriv_sub_source _ _ z r hcoreDiff htraceDiff,
    hcoreJet, htraceJet]
  unfold normalMaxwellStressMixedFirstVariation
  rfl

private theorem differentiableAt_coordinateMatterEinsteinStressMixed4_apply
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4) (i j : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z) :
    DifferentiableAt ℝ
      (fun y ↦ coordinateMatterEinsteinStressMixed4
        (gInvField y) (vField y) (FField y) i j) z := by
  unfold coordinateMatterEinsteinStressMixed4
    coordinateScalarEinsteinStressMixed4
    coordinateMaxwellEinsteinStressMixed4
    coordinateRaisedOneForm4 coordinateRaisedTwoForm4
  fun_prop

private theorem scalarFieldCoordinateFDeriv_coordinateMatterEinsteinStressMixed4_of_normal
    (gInvField : CurvatureCoordinateSpace4 → Matrix4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (Dv : Fin 4 → OneForm4) (DF : Fin 4 → Matrix4)
    (r i j : Fin 4)
    (hgInv : ∀ a b,
      DifferentiableAt ℝ (fun y ↦ gInvField y a b) z)
    (hgInvValue : gInvField z = minkowskiMetric)
    (hgInvJet : ∀ a b,
      scalarFieldCoordinateFDeriv (fun y ↦ gInvField y a b) z r = 0)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateMatterEinsteinStressMixed4
          (gInvField y) (vField y) (FField y) i j) z r =
      normalScalarEinsteinStressMixedFirstVariation (vField z) (Dv r) i j +
        normalMaxwellStressMixedFirstVariation (FField z) (DF r) i j := by
  change scalarFieldCoordinateFDeriv
      (fun y ↦ coordinateScalarEinsteinStressMixed4
          (gInvField y) (vField y) i j +
        coordinateMaxwellEinsteinStressMixed4
          (gInvField y) (FField y) i j) z r = _
  rw [scalarFieldCoordinateFDeriv_add_source]
  · rw [scalarFieldCoordinateFDeriv_coordinateScalarEinsteinStressMixed4_of_normal
      gInvField vField z Dv r i j hgInv hgInvValue hgInvJet hv hvJet]
    rw [scalarFieldCoordinateFDeriv_coordinateMaxwellEinsteinStressMixed4_of_normal
      gInvField FField z DF r i j hgInv hgInvValue hgInvJet hF hFJet]
  · unfold coordinateScalarEinsteinStressMixed4 coordinateRaisedOneForm4
    fun_prop
  · unfold coordinateMaxwellEinsteinStressMixed4 coordinateRaisedTwoForm4
    fun_prop

/-- **Honest metric-dependent source reduction at a normal point.**

If the actual coordinate metric has Minkowski value and zero first jet, then
the derivative of the fully metric-dependent, covariant matter source is just
the Minkowski lowering of the fixed-frame scalar and Maxwell first
variations.  In particular, this theorem includes—and eliminates—the first
variations of both inverse-metric raisings and the final metric lowering. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateMatterEinsteinStressCovariantField4_of_minkowskiNormal
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (Dv : Fin 4 → OneForm4) (DF : Fin 4 → Matrix4)
    (hg : MatrixFieldDifferentiableAt4 (coordinateMetricMatrixField4 g) z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ r k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ r p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q)
    (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateMatterEinsteinStressCovariantField4
          g vField FField y i j) z r =
      ∑ k, minkowskiMetric i k *
        (normalScalarEinsteinStressMixedFirstVariation
            (vField z) (Dv r) k j +
          normalMaxwellStressMixedFirstVariation
            (FField z) (DF r) k j) := by
  let G : CurvatureCoordinateSpace4 → Matrix4 :=
    coordinateMetricMatrixField4 g
  have hdet : Matrix.det (G z) ≠ 0 := by
    dsimp [G]
    rw [hmetric, minkowskiMetric_det]
    norm_num
  have hInvValue : (G z)⁻¹ = minkowskiMetric := by
    dsimp [G]
    rw [hmetric]
    exact Matrix.inv_eq_right_inv minkowskiMetric_sq
  have hInvDiff (a b : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ (G y)⁻¹ a b) z :=
    differentiableAt_matrixNonsingInv_apply4 G z hg hdet a b
  have hMetricJet (s a b : Fin 4) :
      scalarFieldCoordinateFDeriv (fun y ↦ G y a b) z s = 0 := by
    change actualCoordinateMetricJet1Field4 g z s a b = 0
    rw [hfirst]
    rfl
  have hInvJet (a b : Fin 4) :
      scalarFieldCoordinateFDeriv (fun y ↦ (G y)⁻¹ a b) z r = 0 := by
    rw [scalarFieldCoordinateFDeriv_matrixNonsingInv_apply4 G z hg hdet]
    simp_rw [hMetricJet]
    simp
  have hMixedDiff (k : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateMatterEinsteinStressMixed4
        (G y)⁻¹ (vField y) (FField y) k j) z :=
    differentiableAt_coordinateMatterEinsteinStressMixed4_apply
      (fun y ↦ (G y)⁻¹) vField FField z k j hInvDiff hv hF
  have hMixedJet (k : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateMatterEinsteinStressMixed4
            (G y)⁻¹ (vField y) (FField y) k j) z r =
        normalScalarEinsteinStressMixedFirstVariation
            (vField z) (Dv r) k j +
          normalMaxwellStressMixedFirstVariation
            (FField z) (DF r) k j :=
    scalarFieldCoordinateFDeriv_coordinateMatterEinsteinStressMixed4_of_normal
      (fun y ↦ (G y)⁻¹) vField FField z Dv DF r k j
      hInvDiff hInvValue hInvJet hv (hvJet r) hF (hFJet r)
  unfold actualCoordinateMatterEinsteinStressCovariantField4
    coordinateMatterEinsteinStressCovariant4
  change scalarFieldCoordinateFDeriv
      (fun y ↦ ∑ k, G y i k *
        coordinateMatterEinsteinStressMixed4
          (G y)⁻¹ (vField y) (FField y) k j) z r = _
  rw [scalarFieldCoordinateFDeriv_sum_mul_source
    (fun k y ↦ G y i k)
    (fun k y ↦ coordinateMatterEinsteinStressMixed4
      (G y)⁻¹ (vField y) (FField y) k j)
    z r (hg i) hMixedDiff]
  simp_rw [hMetricJet, hMixedJet]
  have hGValue : G z = minkowskiMetric := hmetric
  rw [hGValue]
  simp

/-- Differentiating a neighborhood Einstein/source identity at a Minkowski
normal point gives the explicit scalar-plus-Maxwell source first jet.  The
neighborhood hypothesis is deliberately an `EventuallyEq`, which is exactly
the locality needed by the Fréchet derivative. -/
theorem scalarFieldCoordinateFDeriv_actualCoordinateEinsteinField4_eq_normalMatterSource_of_eventuallyEq
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (Dv : Fin 4 → OneForm4) (DF : Fin 4 → Matrix4)
    (hg : MatrixFieldDifferentiableAt4 (coordinateMetricMatrixField4 g) z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ r k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ r p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q)
    (hEinsteinSource :
      actualCoordinateEinsteinField4 g =ᶠ[nhds z]
        actualCoordinateMatterEinsteinStressCovariantField4
          g vField FField)
    (r i j : Fin 4) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateEinsteinField4 g y i j) z r =
      ∑ k, minkowskiMetric i k *
        (normalScalarEinsteinStressMixedFirstVariation
            (vField z) (Dv r) k j +
          normalMaxwellStressMixedFirstVariation
            (FField z) (DF r) k j) := by
  have hcomponent :
      (fun y ↦ actualCoordinateEinsteinField4 g y i j) =ᶠ[nhds z]
        (fun y ↦ actualCoordinateMatterEinsteinStressCovariantField4
          g vField FField y i j) := by
    filter_upwards [hEinsteinSource] with y hy
    exact congrFun (congrFun hy i) j
  calc
    _ = scalarFieldCoordinateFDeriv
        (fun y ↦ actualCoordinateMatterEinsteinStressCovariantField4
          g vField FField y i j) z r := by
      unfold scalarFieldCoordinateFDeriv
      rw [Filter.EventuallyEq.fderiv_eq hcomponent]
    _ = _ :=
      scalarFieldCoordinateFDeriv_actualCoordinateMatterEinsteinStressCovariantField4_of_minkowskiNormal
        g vField FField z Dv DF hg hmetric hfirst hv hvJet hF hFJet r i j

/-- The contracted form of the differentiated neighborhood Einstein
identity.  This is exactly the source-side hypothesis consumed by
`normalScalarEquationResidual_eq_zero_of_actualEinsteinBianchi`: after the
normal metric contractions, covariant lowering cancels inverse raising and
one obtains the raw mixed matter-stress divergence. -/
theorem actualCoordinateEinsteinContractedDivergenceAt4_eq_normalMatterStressDivergence_of_eventuallyEq
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (vField : CurvatureCoordinateSpace4 → OneForm4)
    (FField : CurvatureCoordinateSpace4 → Matrix4)
    (z : CurvatureCoordinateSpace4)
    (Dv : Fin 4 → OneForm4) (DF : Fin 4 → Matrix4)
    (hg : MatrixFieldDifferentiableAt4 (coordinateMetricMatrixField4 g) z)
    (hmetric : coordinateMetricMatrixField4 g z = minkowskiMetric)
    (hfirst : actualCoordinateMetricJet1Field4 g z = 0)
    (hv : ∀ k, DifferentiableAt ℝ (fun y ↦ vField y k) z)
    (hvJet : ∀ r k,
      scalarFieldCoordinateFDeriv (fun y ↦ vField y k) z r = Dv r k)
    (hF : ∀ p q, DifferentiableAt ℝ (fun y ↦ FField y p q) z)
    (hFJet : ∀ r p q,
      scalarFieldCoordinateFDeriv (fun y ↦ FField y p q) z r = DF r p q)
    (hEinsteinSource :
      actualCoordinateEinsteinField4 g =ᶠ[nhds z]
        actualCoordinateMatterEinsteinStressCovariantField4
          g vField FField)
    (j : Fin 4) :
    actualCoordinateEinsteinContractedDivergenceAt4 g z j =
      (normalScalarEinsteinStressDivergence (vField z) Dv +
        normalMaxwellStressFirstJetDivergence (FField z) DF) j := by
  have hInv : ((coordinateMetricMatrixField4 g z)⁻¹ : Matrix4) =
      minkowskiMetric := by
    rw [hmetric]
    exact Matrix.inv_eq_right_inv minkowskiMetric_sq
  have hSourceJet (r i k : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ actualCoordinateEinsteinField4 g y i k) z r =
        ∑ a, minkowskiMetric i a *
          (normalScalarEinsteinStressMixedFirstVariation
              (vField z) (Dv r) a k +
            normalMaxwellStressMixedFirstVariation
              (FField z) (DF r) a k) :=
    scalarFieldCoordinateFDeriv_actualCoordinateEinsteinField4_eq_normalMatterSource_of_eventuallyEq
      g vField FField z Dv DF hg hmetric hfirst hv hvJet hF hFJet
      hEinsteinSource r i k
  unfold actualCoordinateEinsteinContractedDivergenceAt4
    coordinateCovariant2Divergence
  rw [hInv, hfirst]
  simp_rw [hSourceJet]
  unfold normalScalarEinsteinStressDivergence
    normalMaxwellStressFirstJetDivergence
  fin_cases j <;>
    simp [coordinateChristoffel, coordinateChristoffelFirstKind,
      minkowskiMetric, Fin.sum_univ_succ] <;>
    ring

end RainichKaluza
