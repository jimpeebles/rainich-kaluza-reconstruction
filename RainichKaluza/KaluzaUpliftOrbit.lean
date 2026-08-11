import RainichKaluza.IntrinsicKaluzaLocal
import RainichKaluza.ExteriorComplexion

/-!
# Exhaustive local orbit of Kaluza uplift presentations

This file classifies the presentation freedom of the convention-fixed local
Kaluza metric

`exp(c₁φ) g + exp(c₂φ) (dz + A)²`.

A product-preserving local change of circle coordinate has, at a point, a
nonzero constant fiber scale and a horizontal one-form.  The central theorem
`equivalentUnder_iff_compatible` proves that two Kaluza presentations define
the same block metric under such a change if and only if:

* their warped base pairings agree;
* their fiber warps differ by the square of the fiber scale;
* their potentials differ by exactly the horizontal coordinate shift.

Thus the familiar gauge shift, dilaton-constant/circle-radius modulus, and
fiber reversal are not merely sufficient examples: they are the complete
pointwise list inside this product-preserving class.  Translation of the
circle coordinate is invisible to the tangent pairing and is already covered
by circle invariance of the local-product metric.

The final section keeps Maxwell duality logically separate.  On an active
nonzero-coupling EMD branch the constant duality orbit is exactly the overall
sign; zero coupling and inactive scalar-source channels retain the full
circle, as proved by the existing exceptional-locus theorems.
-/

namespace RainichKaluza

section ProductPresentation

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convention-fixed data entering a pointwise Kaluza block presentation. -/
structure KaluzaUpliftPresentation where
  phi : ℝ
  baseMetric : ContinuousBilinForm E
  potential : E →L[ℝ] ℝ

/-- First-order datum of a product-preserving local circle-coordinate change.
`scale` is the nonzero constant derivative in the circle direction and
`horizontal` is the base differential of the coordinate shift. -/
structure ProductFiberCoordinateJet where
  scale : ℝ
  horizontal : E →L[ℝ] ℝ
  scale_ne_zero : scale ≠ 0

namespace ProductFiberCoordinateJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Action of the fiber-coordinate jet on a tangent vector. -/
def apply (T : ProductFiberCoordinateJet E) (X : E) (xi : ℝ) : ℝ :=
  T.scale * xi + T.horizontal X

/-- Gauge-coordinate change `z' = z - χ(x)` at the tangent-jet level. -/
def gauge (dchi : E →L[ℝ] ℝ) : ProductFiberCoordinateJet E where
  scale := 1
  horizontal := -dchi
  scale_ne_zero := one_ne_zero

/-- Reversal of the local circle coordinate. -/
def reversal : ProductFiberCoordinateJet E where
  scale := -1
  horizontal := 0
  scale_ne_zero := by norm_num

/-- Positive rescaling of the local circle coordinate induced by a constant
dilaton shift. -/
noncomputable def dilatonScale (k : ℝ) : ProductFiberCoordinateJet E where
  scale := kaluzaHalfFiberWarp k
  horizontal := 0
  scale_ne_zero := ne_of_gt (Real.exp_pos _)

end ProductFiberCoordinateJet

namespace KaluzaUpliftPresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The five-dimensional block pairing presented by `P`. -/
noncomputable def pairing (P : KaluzaUpliftPresentation E)
    (X Y : E) (xi eta : ℝ) : ℝ :=
  conventionKaluzaMetricPairing P.phi P.baseMetric P.potential X Y xi eta

/-- Equality of two presentations after a product-preserving local change of
circle coordinate.  The base coordinate is unchanged; the fiber tangent
component is transformed by `T`. -/
def EquivalentUnder (P Q : KaluzaUpliftPresentation E)
    (T : ProductFiberCoordinateJet E) : Prop :=
  ∀ X Y xi eta,
    Q.pairing X Y (T.apply X xi) (T.apply Y eta) =
      P.pairing X Y xi eta

/-- Agreement of the warped base blocks. -/
def WarpedBaseCompatible (P Q : KaluzaUpliftPresentation E) : Prop :=
  ∀ X Y,
    kaluzaBaseWarp Q.phi * Q.baseMetric X Y =
      kaluzaBaseWarp P.phi * P.baseMetric X Y

/-- Agreement of the circle block after the coordinate scale. -/
def FiberRadiusCompatible (P Q : KaluzaUpliftPresentation E)
    (T : ProductFiberCoordinateJet E) : Prop :=
  kaluzaFiberWarp Q.phi * T.scale ^ 2 = kaluzaFiberWarp P.phi

/-- Agreement of the connection one-form after the horizontal coordinate
shift and circle rescaling. -/
def ConnectionCompatible (P Q : KaluzaUpliftPresentation E)
    (T : ProductFiberCoordinateJet E) : Prop :=
  ∀ X, T.horizontal X + Q.potential X = T.scale * P.potential X

/-- **Exhaustive product-presentation theorem.** A product-preserving fiber
coordinate jet identifies two convention-fixed Kaluza block metrics exactly
when the warped base, fiber-radius, and connection conditions hold. -/
theorem equivalentUnder_iff_compatible
    (P Q : KaluzaUpliftPresentation E)
    (T : ProductFiberCoordinateJet E) :
    P.EquivalentUnder Q T ↔
      P.WarpedBaseCompatible Q ∧
      P.FiberRadiusCompatible Q T ∧
      P.ConnectionCompatible Q T := by
  constructor
  · intro h
    have hfiber := h 0 0 1 1
    have hfiber' :
        kaluzaFiberWarp Q.phi * T.scale ^ 2 =
          kaluzaFiberWarp P.phi := by
      simpa [pairing, ProductFiberCoordinateJet.apply,
        conventionKaluzaMetricPairing, kaluzaMetricPairing,
        kaluzaFiberOneForm, kaluzaGaugeNormalization, pow_two,
        mul_assoc] using hfiber
    have hconnection : P.ConnectionCompatible Q T := by
      intro X
      have hmixed := h X 0 0 1
      have hmixed' :
          kaluzaFiberWarp Q.phi *
              (T.horizontal X + Q.potential X) * T.scale =
            kaluzaFiberWarp P.phi * P.potential X := by
        simpa [pairing, ProductFiberCoordinateJet.apply,
          conventionKaluzaMetricPairing, kaluzaMetricPairing,
          kaluzaFiberOneForm, kaluzaGaugeNormalization] using hmixed
      have hzero :
          (kaluzaFiberWarp Q.phi * T.scale) *
            (T.horizontal X + Q.potential X -
              T.scale * P.potential X) = 0 := by
        rw [← hfiber'] at hmixed'
        linear_combination hmixed'
      have hcoeff : kaluzaFiberWarp Q.phi * T.scale ≠ 0 :=
        mul_ne_zero (kaluzaFiberWarp_ne_zero Q.phi) T.scale_ne_zero
      exact sub_eq_zero.mp <| (mul_eq_zero.mp hzero).resolve_left hcoeff
    refine ⟨?_, hfiber', hconnection⟩
    intro X Y
    have hbase := h X Y (-P.potential X) (-P.potential Y)
    have hX := hconnection X
    have hY := hconnection Y
    have hzX :
        -(T.scale * P.potential X) + T.horizontal X + Q.potential X = 0 := by
      rw [add_assoc, hX]
      ring
    have hzY :
        -(T.scale * P.potential Y) + T.horizontal Y + Q.potential Y = 0 := by
      rw [add_assoc, hY]
      ring
    simpa [pairing, ProductFiberCoordinateJet.apply,
      conventionKaluzaMetricPairing, kaluzaMetricPairing,
      kaluzaFiberOneForm, kaluzaGaugeNormalization, hzX, hzY] using hbase
  · rintro ⟨hbase, hfiber, hconnection⟩ X Y xi eta
    unfold pairing ProductFiberCoordinateJet.apply
      conventionKaluzaMetricPairing kaluzaMetricPairing kaluzaFiberOneForm
      kaluzaGaugeNormalization
    rw [hbase X Y]
    simp only [one_mul]
    have hX :
        T.scale * xi + T.horizontal X + Q.potential X =
          T.scale * (xi + P.potential X) := by
      rw [add_assoc, hconnection X]
      ring
    have hY :
        T.scale * eta + T.horizontal Y + Q.potential Y =
          T.scale * (eta + P.potential Y) := by
      rw [add_assoc, hconnection Y]
      ring
    rw [hX, hY, ← hfiber]
    ring

/-- Gauge shifts and their compensating circle-coordinate changes are members
of the complete product-presentation orbit. -/
theorem equivalentUnder_gauge
    (phi : ℝ) (g : ContinuousBilinForm E) (A dchi : E →L[ℝ] ℝ) :
    (KaluzaUpliftPresentation.mk phi g A).EquivalentUnder
      (KaluzaUpliftPresentation.mk phi g (gaugeShiftOneForm A dchi))
      (ProductFiberCoordinateJet.gauge dchi) := by
  rw [equivalentUnder_iff_compatible]
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    rfl
  · simp [FiberRadiusCompatible, ProductFiberCoordinateJet.gauge]
  · intro X
    simp [ProductFiberCoordinateJet.gauge, gaugeShiftOneForm]

/-- **Field-level local gauge orbit.** On an open convex patch, two
differentiable potentials with the same curvature are related by a scalar
gauge parameter, and its differential supplies at every point exactly the
fiber-coordinate jet identifying their Kaluza presentations. -/
theorem exists_localGaugeFiberCoordinate_of_sameCurvature
    {A A' : E → E →L[ℝ] ℝ} {U : Set E}
    (hconvex : Convex ℝ U) (hopen : IsOpen U)
    (hsame : HaveSameGaugeCurvatureOn A A' U)
    (phi : E → ℝ) (g : E → ContinuousBilinForm E) :
    ∃ chi : E → ℝ,
      IsScalarPotentialOn chi (A' - A) U ∧
      ∀ x ∈ U,
        (KaluzaUpliftPresentation.mk (phi x) (g x) (A x)).EquivalentUnder
          (KaluzaUpliftPresentation.mk (phi x) (g x) (A' x))
          (ProductFiberCoordinateJet.gauge (fderiv ℝ chi x)) := by
  obtain ⟨chi, hchi⟩ :=
    exists_localGaugeParameter_of_same_curvature hconvex hopen hsame
  refine ⟨chi, hchi, ?_⟩
  intro x hx
  have hd : gaugeShiftOneForm (A x) (fderiv ℝ chi x) = A' x := by
    rw [(hchi x hx).fderiv]
    unfold gaugeShiftOneForm
    ext X
    simp
  rw [← hd]
  exact equivalentUnder_gauge (phi x) (g x) (A x) (fderiv ℝ chi x)

/-- Reversing both the circle coordinate and the Maxwell potential leaves the
uplift metric unchanged.  This realizes the surviving overall Maxwell sign. -/
theorem equivalentUnder_fiberReversal
    (phi : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ) :
    (KaluzaUpliftPresentation.mk phi g A).EquivalentUnder
      (KaluzaUpliftPresentation.mk phi g (-A))
      (ProductFiberCoordinateJet.reversal (E := E)) := by
  rw [equivalentUnder_iff_compatible]
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    rfl
  · simp [FiberRadiusCompatible, ProductFiberCoordinateJet.reversal]
  · intro X
    simp [ProductFiberCoordinateJet.reversal]

/-- A constant shift of the dilaton is exactly the circle-radius/base-homothety
modulus already identified in `conventionKaluzaMetricPairing_addConstant`. -/
theorem equivalentUnder_dilatonShift
    (phi k : ℝ) (g : ContinuousBilinForm E) (A : E →L[ℝ] ℝ) :
    (KaluzaUpliftPresentation.mk (phi + k) g A).EquivalentUnder
      (KaluzaUpliftPresentation.mk phi
        (kaluzaBaseWarp k • g) (kaluzaHalfFiberWarp k • A))
      (ProductFiberCoordinateJet.dilatonScale (E := E) k) := by
  rw [equivalentUnder_iff_compatible]
  refine ⟨?_, ?_, ?_⟩
  · intro X Y
    simp only [smul_apply, smul_eq_mul]
    rw [kaluzaBaseWarp_add]
    ring
  · unfold FiberRadiusCompatible ProductFiberCoordinateJet.dilatonScale
    rw [pow_two, kaluzaHalfFiberWarp_mul_self, kaluzaFiberWarp_add]
  · intro X
    simp [ProductFiberCoordinateJet.dilatonScale]

end KaluzaUpliftPresentation

end ProductPresentation

section OrbitBranches

/-- The orientation-independent Kaluza coupling locus consists of exactly the
two scalar orientations `±√3`. -/
theorem isKaluzaCoupling_iff_eq_sqrt_three_or_neg
    (a : ℝ) :
    IsKaluzaCoupling a ↔ a = Real.sqrt 3 ∨ a = -Real.sqrt 3 := by
  constructor
  · intro ha
    rcases kaluzaCoupling_has_positive_orientation a ha with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · unfold IsKaluzaCoupling
      rw [Real.sq_sqrt (by norm_num)]
    · exact (isKaluzaCoupling_neg_iff (Real.sqrt 3)).mpr <| by
        unfold IsKaluzaCoupling
        rw [Real.sq_sqrt (by norm_num)]

/-- **Active-branch duality exhaustiveness.** For nonzero coupling and an
active scalar-source channel, a constant unit duality rotation preserves the
same EMD equations if and only if it is the overall sign. -/
theorem constantDuality_emd_iff_sign_of_active
    {One Two Three : Type*}
    [AddCommGroup One] [Module ℝ One]
    [AddCommGroup Two] [Module ℝ Two]
    [AddCommGroup Three] [Module ℝ Three]
    (wedge : OneWedgeTwo One Two Three)
    (v : One) (F0 G0 : Two) (dF0 dG0 : Three)
    (c s a : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) (ha : a ≠ 0)
    (hactive : wedge v F0 ≠ 0 ∨ wedge v G0 ≠ 0)
    (hF0 : dF0 = (a / 2) • wedge v F0)
    (hG0 : dG0 = -(a / 2) • wedge v G0) :
    (c • dF0 + s • dG0 =
        (a / 2) • wedge v (c • F0 + s • G0) ∧
      (-s) • dF0 + c • dG0 =
        -(a / 2) • wedge v ((-s) • F0 + c • G0)) ↔
      (c = 1 ∨ c = -1) ∧ s = 0 := by
  constructor
  · rintro ⟨hFrot, hGrot⟩
    exact constantDuality_eq_sign_of_emd wedge v F0 G0 dF0 dG0
      c s a hunit ha hactive hF0 hG0 hFrot hGrot
  · rintro ⟨hc, rfl⟩
    rcases hc with rfl | rfl <;> simp [hF0, hG0]

end OrbitBranches

end RainichKaluza
