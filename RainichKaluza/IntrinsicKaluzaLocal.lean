import RainichKaluza.KaluzaFieldReduction

/-!
# Intrinsic local packaging of the Kaluza uplift

The curvature calculation in this project is deliberately performed in
coordinates.  This file packages the result at the exact geometric boundary
needed for a local theorem, without rebuilding the calculation in a manifold
library that currently has no ready-made pseudo-Riemannian Ricci API.

`PseudoRiemannianCoordinate2Jet` records a symmetric, nondegenerate metric
two-jet in one coordinate germ.  Its `RicciFlatInChart` predicate pulls the
entire two-jet through an invertible nonlinear coordinate three-jet.  The
nonlinear covariance theorem proves that this predicate is independent of the
chosen chart germ.

`LorentzianKaluzaLocalProductGermAt` then supplies that abstract package from
the actual componentwise `C²`, circle-invariant Kaluza metric on
`BaseCoordinateSpace × ℝ`.  The base normal/radial-gauge chart is used only to
evaluate the calculation.  Ricci-flatness in any, or equivalently every,
invertible `C³` overlap jet is equivalent to the extracted EMD equations.

The local circle is represented by a real coordinate on a product patch.
Global periodic identification and a global pseudo-Riemannian manifold API are
not asserted here.
-/

namespace RainichKaluza

open Filter Matrix
open scoped Topology ContDiff

section CoordinateGerm

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- A coordinate two-jet of a pseudo-Riemannian metric at one point.

The symmetry and inverse fields are the pointwise pseudo-Riemannian
hypotheses.  `metricJet1_symm` is retained explicitly because it is the exact
first-jet hypothesis used by nonlinear Ricci covariance.  Analytic realization
by an actual `C²` metric field is supplied separately by the Kaluza
specialization below. -/
structure PseudoRiemannianCoordinate2Jet where
  metric : I → I → ℝ
  inverseMetric : I → I → ℝ
  metricJet1 : CoordinateMetricJet1 I
  metricJet2 : CoordinateMetricJet2 I
  metric_symm : ∀ A B, metric A B = metric B A
  inverseMetric_symm : ∀ A B, inverseMetric A B = inverseMetric B A
  metricJet1_symm : ∀ R A B, metricJet1 R A B = metricJet1 R B A
  inverse_metric_contract : ∀ A B,
    (∑ D : I, inverseMetric A D * metric D B) =
      if A = B then 1 else 0

namespace PseudoRiemannianCoordinate2Jet

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Ricci-flatness in the coordinate germ in which the two-jet is stored. -/
noncomputable def RicciFlat (J : PseudoRiemannianCoordinate2Jet I) : Prop :=
  ∀ N P, coordinateRicci J.inverseMetric J.metricJet1 J.metricJet2 N P = 0

/-- Ricci-flatness after pulling the complete metric two-jet through an
invertible nonlinear coordinate three-jet.  Such a jet is precisely the
pointwise overlap datum contributed by a `C³` chart transition. -/
noncomputable def RicciFlatInChart (J : PseudoRiemannianCoordinate2Jet I)
    (C : CoordinateChangeJet3 I) : Prop :=
  ∀ N P,
    coordinateRicci
      (C.affine.transformContravariant2 J.inverseMetric)
      (C.secondJet.transformMetricJet1 J.metric J.metricJet1)
      (C.transformMetricJet2 J.metric J.metricJet1 J.metricJet2) N P = 0

/-- **Finite-jet chart-independence.** Ricci-flatness after an arbitrary
invertible nonlinear overlap jet is equivalent to Ricci-flatness in the
reference coordinate germ. -/
theorem ricciFlatInChart_iff (J : PseudoRiemannianCoordinate2Jet I)
    (C : CoordinateChangeJet3 I) :
    J.RicciFlatInChart C ↔ J.RicciFlat := by
  exact C.coordinateRicciFlat_transform_iff J.inverseMetric J.metric
    J.metricJet1 J.metricJet2 J.metric_symm J.inverseMetric_symm
    J.metricJet1_symm J.inverse_metric_contract

/-- Any two nonlinear chart germs related to the stored reference germ give
the same Ricci-flatness answer. -/
theorem ricciFlatInChart_iff_ricciFlatInChart
    (J : PseudoRiemannianCoordinate2Jet I)
    (C₁ C₂ : CoordinateChangeJet3 I) :
    J.RicciFlatInChart C₁ ↔ J.RicciFlatInChart C₂ := by
  rw [J.ricciFlatInChart_iff C₁, J.ricciFlatInChart_iff C₂]

end PseudoRiemannianCoordinate2Jet

end CoordinateGerm

section KaluzaLocalProduct

/-- The displayed normal-coordinate signature condition for a five-dimensional
metric: one negative base direction, three positive base directions, a
positive circle direction, and vanishing cross terms in that frame.  This
exhibits signature `(-,+,+,+,+)` without reducing it to determinant sign. -/
def HasDisplayedKaluzaLorentzSignature
    (g : (Fin 4 ⊕ Unit) → (Fin 4 ⊕ Unit) → ℝ) : Prop :=
  g (Sum.inl 0) (Sum.inl 0) < 0 ∧
  (∀ i : Fin 4, i ≠ 0 → 0 < g (Sum.inl i) (Sum.inl i)) ∧
  0 < g (Sum.inr ()) (Sum.inr ()) ∧
  (∀ i j : Fin 4, i ≠ j → g (Sum.inl i) (Sum.inl j) = 0) ∧
  ∀ i : Fin 4,
    g (Sum.inl i) (Sum.inr ()) = 0 ∧
      g (Sum.inr ()) (Sum.inl i) = 0

/-- Actual local Kaluza product data on the Lorentzian branch.

`fields` contains the componentwise `C²` assumptions, eventual metric
symmetry, normal coordinates, radial gauge, and pointwise nondegeneracy.
The two sign fields strengthen its nonzero diagonal hypothesis to the chosen
Lorentzian signature convention. -/
structure LorentzianKaluzaLocalProductGermAt (x : BaseCoordinateSpace) where
  fields : KaluzaNormalGaugeFieldsAt x
  time_negative : fields.diagonal 0 < 0
  space_positive : ∀ i : Fin 4, i ≠ 0 → 0 < fields.diagonal i

namespace LorentzianKaluzaLocalProductGermAt

variable {x : BaseCoordinateSpace}
    (K : LorentzianKaluzaLocalProductGermAt x)

/-- The actual Kaluza metric on the local product coordinate patch. -/
noncomputable def metric : LocalProductCoordinateSpace → Matrix5 :=
  K.fields.localProductUpliftMetric

/-- Every component of the packaged local-product metric is genuinely `C²`
at the product point. -/
theorem metric_component_contDiffAt (z : ℝ) (M N : Fin 4 ⊕ Unit) :
    ContDiffAt ℝ 2 (fun p => K.metric p M N) (x, z) := by
  exact K.fields.localProductUpliftMetric_component_contDiffAt z M N

/-- The packaged metric is symmetric on a neighborhood of the product point. -/
theorem metric_eventually_symmetric (z : ℝ) :
    ∀ᶠ p in 𝓝 (x, z), ∀ M N, K.metric p M N = K.metric p N M := by
  exact K.fields.localProductUpliftMetric_eventually_symmetric z

/-- The metric is invariant under translation of the local circle coordinate.
This is the explicit circle-invariance hypothesis/result on the product
patch. -/
theorem metric_circle_invariant (y : BaseCoordinateSpace) (z z' : ℝ) :
    K.metric (y, z) = K.metric (y, z') := by
  exact K.fields.localProductUpliftMetric_circle_invariant y z z'

/-- The normal/radial-gauge product frame displays the required
five-dimensional Lorentz signature. -/
theorem metric_hasDisplayedKaluzaLorentzSignature (z : ℝ) :
    HasDisplayedKaluzaLorentzSignature (K.metric (x, z)) := by
  have hpoint : K.metric (x, z) =
      kaluzaNormalGaugePointMetric
        (kaluzaBaseWarp K.fields.phi0)
        (kaluzaFiberWarp K.fields.phi0) K.fields.diagonal := by
    funext M N
    exact K.fields.upliftMetric_apply_at M N
  rw [hpoint]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [kaluzaNormalGaugePointMetric] using
      mul_neg_of_pos_of_neg (kaluzaBaseWarp_pos K.fields.phi0)
        K.time_negative
  · intro i hi
    simpa [kaluzaNormalGaugePointMetric] using
      mul_pos (kaluzaBaseWarp_pos K.fields.phi0) (K.space_positive i hi)
  · simpa [kaluzaNormalGaugePointMetric] using
      kaluzaFiberWarp_pos K.fields.phi0
  · intro i j hij
    simp [kaluzaNormalGaugePointMetric, hij]
  · intro i
    simp [kaluzaNormalGaugePointMetric]

/-- The pseudo-Riemannian coordinate two-jet supplied by the actual `C²`
Kaluza metric at `(x,z)`. -/
noncomputable def coordinate2Jet (z : ℝ) :
    PseudoRiemannianCoordinate2Jet (Fin 4 ⊕ Unit) where
  metric := K.metric (x, z)
  inverseMetric := kaluzaNormalGaugePointInverse
    (kaluzaBaseWarp K.fields.phi0) (kaluzaFiberWarp K.fields.phi0)
      K.fields.diagonal
  metricJet1 := K.fields.localProductMetricJet1 z
  metricJet2 := K.fields.localProductMetricJet2 z
  metric_symm := by
    intro A B
    exact (K.metric_eventually_symmetric z).self_of_nhds A B
  inverseMetric_symm := by
    intro A B
    rcases A with A | A <;> rcases B with B | B
    · by_cases h : A = B
      · subst B
        rfl
      · simp [kaluzaNormalGaugePointInverse, h, Ne.symm h]
    · simp [kaluzaNormalGaugePointInverse]
    · simp [kaluzaNormalGaugePointInverse]
    · rfl
  metricJet1_symm := K.fields.localProductMetricJet1_symm z
  inverse_metric_contract := by
    have hinv (A B : Fin 4 ⊕ Unit) :
        kaluzaNormalGaugePointInverse
            (kaluzaBaseWarp K.fields.phi0)
            (kaluzaFiberWarp K.fields.phi0) K.fields.diagonal A B =
          kaluzaNormalGaugePointInverse
            (kaluzaBaseWarp K.fields.phi0)
            (kaluzaFiberWarp K.fields.phi0) K.fields.diagonal B A := by
      rcases A with A | A <;> rcases B with B | B
      · by_cases h : A = B
        · subst B
          rfl
        · simp [kaluzaNormalGaugePointInverse, h, Ne.symm h]
      · simp [kaluzaNormalGaugePointInverse]
      · simp [kaluzaNormalGaugePointInverse]
      · rfl
    intro A B
    calc
      (∑ D : Fin 4 ⊕ Unit,
          kaluzaNormalGaugePointInverse
              (kaluzaBaseWarp K.fields.phi0)
              (kaluzaFiberWarp K.fields.phi0) K.fields.diagonal A D *
            K.metric (x, z) D B) =
          ∑ D : Fin 4 ⊕ Unit,
            K.metric (x, z) B D *
              kaluzaNormalGaugePointInverse
                (kaluzaBaseWarp K.fields.phi0)
                (kaluzaFiberWarp K.fields.phi0) K.fields.diagonal D A := by
        apply Finset.sum_congr rfl
        intro D _
        rw [(K.metric_eventually_symmetric z).self_of_nhds D B]
        rw [hinv A D]
        ring
      _ = if B = A then 1 else 0 :=
        K.fields.localProductUpliftMetric_mul_pointInverse z B A
      _ = if A = B then 1 else 0 := by
        by_cases h : A = B
        · simp [h]
        · simp [h, Ne.symm h]

/-- Ricci-flatness in a chart whose overlap with the normal/radial-gauge chart
has the supplied invertible nonlinear coordinate three-jet. -/
noncomputable def RicciFlatInChart (z : ℝ)
    (C : CoordinateChangeJet3 (Fin 4 ⊕ Unit)) : Prop :=
  (K.coordinate2Jet z).RicciFlatInChart C

/-- Intrinsic local Ricci-flatness: every admissible nonlinear chart-overlap
three-jet gives a Ricci-flat coordinate representative.  Quantifying over all
invertible algebraic overlap jets is stronger than quantifying only over jets
realized by actual local charts. -/
noncomputable def IntrinsicRicciFlatAt (z : ℝ) : Prop :=
  ∀ C : CoordinateChangeJet3 (Fin 4 ⊕ Unit), K.RicciFlatInChart z C

/-- Ricci-flatness in any nonlinear chart germ is equivalent to the normal
coordinate result, hence to the extracted EMD equations. -/
theorem ricciFlatInChart_iff_emd (z : ℝ)
    (C : CoordinateChangeJet3 (Fin 4 ⊕ Unit)) :
    K.RicciFlatInChart z C ↔ K.fields.EMDEquations := by
  rw [RicciFlatInChart,
    PseudoRiemannianCoordinate2Jet.ricciFlatInChart_iff]
  exact K.fields.localProductCoordinateRicciFlat_iff_emd z

/-- **Chart independence of the actual Kaluza local product.** Any two
invertible nonlinear coordinate overlap jets give the same Ricci-flatness
answer.  Neither change is required to preserve the base/fiber split. -/
theorem ricciFlatInChart_iff_ricciFlatInChart (z : ℝ)
    (C₁ C₂ : CoordinateChangeJet3 (Fin 4 ⊕ Unit)) :
    K.RicciFlatInChart z C₁ ↔ K.RicciFlatInChart z C₂ := by
  exact (K.coordinate2Jet z).ricciFlatInChart_iff_ricciFlatInChart C₁ C₂

/-- **Intrinsic local Kaluza reduction.** For the actual componentwise `C²`,
Lorentzian, circle-invariant metric on the local product patch, intrinsic
Ricci-flatness at `(x,z)` is equivalent to the convention-fixed EMD equations
extracted in the normal/radial-gauge chart. -/
theorem intrinsicRicciFlatAt_iff_emd (z : ℝ) :
    K.IntrinsicRicciFlatAt z ↔ K.fields.EMDEquations := by
  constructor
  · intro h
    let C : CoordinateChangeJet3 (Fin 4 ⊕ Unit) := {
      toCoordinateChangeJet2 := {
        toAffineCoordinateChange := {
          jac := 1
          invJac := 1
          jac_mul_invJac := by simp
          invJac_mul_jac := by simp }
        second := fun _ _ _ => 0
        second_symm := by simp }
      third := fun _ _ _ _ => 0
      third_swap12 := by simp
      third_swap23 := by simp }
    exact (K.ricciFlatInChart_iff_emd z C).mp (h C)
  · intro h C
    exact (K.ricciFlatInChart_iff_emd z C).mpr h

/-- The intrinsic predicate is equivalently Ricci-flatness in any one chosen
admissible chart germ. -/
theorem intrinsicRicciFlatAt_iff_ricciFlatInChart (z : ℝ)
    (C : CoordinateChangeJet3 (Fin 4 ⊕ Unit)) :
    K.IntrinsicRicciFlatAt z ↔ K.RicciFlatInChart z C := by
  rw [K.intrinsicRicciFlatAt_iff_emd z, K.ricciFlatInChart_iff_emd z C]

end LorentzianKaluzaLocalProductGermAt

end KaluzaLocalProduct

end RainichKaluza
