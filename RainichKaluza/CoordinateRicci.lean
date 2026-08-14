import RainichKaluza.KaluzaRicciBase

/-!
# Coordinate metric germs and Ricci curvature

This file separates the differential-geometric coordinate formula from the
Kaluza ansatz.  For an arbitrary finite coordinate index type, a pointwise
inverse metric together with first and second metric coordinate jets defines
the Levi--Civita symbols, their first derivatives, and the Ricci contraction.

The final theorem identifies the convention-fixed normal-gauge Kaluza Ricci
calculation with this ansatz-independent coordinate Ricci definition.  Thus
the large block computation is not its own notion of curvature: it is an
exact specialization of the standard coordinate Levi--Civita construction.
-/

namespace RainichKaluza

/-- First coordinate jet of a metric: `dg R M N = ∂_R g_{MN}`. -/
abbrev CoordinateMetricJet1 (I : Type*) := I → I → I → ℝ

/-- Second coordinate jet of a metric:
`ddg R S M N = ∂_R∂_S g_{MN}`. -/
abbrev CoordinateMetricJet2 (I : Type*) := I → I → I → I → ℝ

section CoordinateCurvature

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Derivative of the inverse metric forced by differentiating
`g g⁻¹ = 1`: `∂_R g⁻¹ = -g⁻¹(∂_R g)g⁻¹`. -/
noncomputable def coordinateInverseMetricJet
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (R M N : I) : ℝ :=
  -∑ A : I, ∑ B : I, gInv M A * dg R A B * gInv B N

/-- Christoffel symbols of the first kind determined by a metric first jet. -/
noncomputable def coordinateChristoffelFirstKind
    (dg : CoordinateMetricJet1 I) (Q N P : I) : ℝ :=
  (dg N Q P + dg P Q N - dg Q N P) / 2

/-- Levi--Civita Christoffel symbols of the second kind at a coordinate
point. -/
noncomputable def coordinateChristoffel
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (M N P : I) : ℝ :=
  ∑ Q : I, gInv M Q * coordinateChristoffelFirstKind dg Q N P

/-- Coordinate derivative of the first-kind Christoffel symbols. -/
noncomputable def coordinateChristoffelFirstKindJet
    (ddg : CoordinateMetricJet2 I) (R Q N P : I) : ℝ :=
  (ddg R N Q P + ddg R P Q N - ddg R Q N P) / 2

/-- Product-rule coordinate derivative of the Levi--Civita symbols. -/
noncomputable def coordinateChristoffelJet
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (R M N P : I) : ℝ :=
  ∑ Q : I, (
    coordinateInverseMetricJet gInv dg R M Q *
        coordinateChristoffelFirstKind dg Q N P +
      gInv M Q * coordinateChristoffelFirstKindJet ddg R Q N P)

/-- The coordinate Ricci contraction
`Ric_NP = ∂_M Γ^M_NP - ∂_N Γ^M_MP
          + Γ^M_MQ Γ^Q_NP - Γ^M_NQ Γ^Q_MP`. -/
noncomputable def coordinateRicci
    (gInv : Matrix I I ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (N P : I) : ℝ :=
  (∑ M : I, coordinateChristoffelJet gInv dg ddg M M N P) -
    (∑ M : I, coordinateChristoffelJet gInv dg ddg N M M P) +
    (∑ Q : I, (∑ M : I, coordinateChristoffel gInv dg M M Q) *
      coordinateChristoffel gInv dg Q N P) -
    (∑ M : I, ∑ Q : I, coordinateChristoffel gInv dg M N Q *
      coordinateChristoffel gInv dg Q M P)

omit [DecidableEq I] in
theorem coordinateChristoffel_symm (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I)
    (hdg : ∀ R M N, dg R M N = dg R N M) (M N P : I) :
    coordinateChristoffel gInv dg M N P =
      coordinateChristoffel gInv dg M P N := by
  unfold coordinateChristoffel coordinateChristoffelFirstKind
  apply Finset.sum_congr rfl
  intro Q _
  rw [hdg Q N P]
  ring

end CoordinateCurvature

section KaluzaSpecialization

/-- The full five-coordinate second jet: the base-base derivative block is
the Kaluza Hessian and every derivative involving the circle direction
vanishes by circle invariance. -/
def kaluzaNormalGaugeFullMetricJet2 (u v c k₁ k₂ : ℝ)
    (d : Fin 4 → ℝ) (phi1 : OneForm4) (phi2 : Fin 4 → Fin 4 → ℝ)
    (A1 : Fin 4 → Fin 4 → ℝ) (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    CoordinateMetricJet2 (Fin 4 ⊕ Unit) :=
  fun R S M N => Sum.elim
    (fun r => kaluzaNormalGaugeDoubleJet u v c k₁ k₂ d phi1 phi2
      A1 A2 g2 r S M N)
    (fun _ => 0) R

theorem coordinateInverseMetricJet_kaluza_base
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (R : Fin 4) (M N : Fin 4 ⊕ Unit) :
    coordinateInverseMetricJet (kaluzaNormalGaugePointInverse u v d)
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
        (Sum.inl R) M N =
      kaluzaNormalGaugeInverseJet u v c k₁ k₂ d phi1 A1 R M N := by
  rfl

theorem coordinateInverseMetricJet_kaluza_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (R : Unit) (M N : Fin 4 ⊕ Unit) :
    coordinateInverseMetricJet (kaluzaNormalGaugePointInverse u v d)
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
        (Sum.inr R) M N = 0 := by
  simp [coordinateInverseMetricJet, kaluzaNormalGaugeMetricJet]

theorem coordinateChristoffelFirstKind_kaluza
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (Q N P : Fin 4 ⊕ Unit) :
    coordinateChristoffelFirstKind
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1) Q N P =
      kaluzaNormalGaugeChristoffelFirstKind u v c k₁ k₂ d phi1 A1
        Q N P := by
  rfl

theorem coordinateChristoffel_kaluza
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ) (M N P : Fin 4 ⊕ Unit) :
    coordinateChristoffel (kaluzaNormalGaugePointInverse u v d)
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1) M N P =
      kaluzaNormalGaugeChristoffel u v c k₁ k₂ d phi1 A1 M N P := by
  rfl

theorem coordinateChristoffelFirstKindJet_kaluza_base
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4) (Q N P : Fin 4 ⊕ Unit) :
    coordinateChristoffelFirstKindJet
        (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2 A1 A2 g2)
        (Sum.inl R) Q N P =
      kaluzaNormalGaugeChristoffelFirstKindJet u v c k₁ k₂ d phi1
        phi2 A1 A2 g2 R Q N P := by
  rfl

theorem coordinateChristoffelFirstKindJet_kaluza_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Unit) (Q N P : Fin 4 ⊕ Unit) :
    coordinateChristoffelFirstKindJet
        (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2 A1 A2 g2)
        (Sum.inr R) Q N P = 0 := by
  simp [coordinateChristoffelFirstKindJet, kaluzaNormalGaugeFullMetricJet2]

theorem coordinateChristoffelJet_kaluza_base
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Fin 4) (M N P : Fin 4 ⊕ Unit) :
    coordinateChristoffelJet (kaluzaNormalGaugePointInverse u v d)
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
        (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2
          A1 A2 g2)
        (Sum.inl R) M N P =
      kaluzaNormalGaugeChristoffelJet u v c k₁ k₂ d phi1 phi2 A1 A2
        g2 R M N P := by
  rfl

theorem coordinateChristoffelJet_kaluza_fiber
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (R : Unit) (M N P : Fin 4 ⊕ Unit) :
    coordinateChristoffelJet (kaluzaNormalGaugePointInverse u v d)
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
        (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2
          A1 A2 g2)
        (Sum.inr R) M N P = 0 := by
  simp [coordinateChristoffelJet,
    coordinateInverseMetricJet_kaluza_fiber,
    coordinateChristoffelFirstKindJet_kaluza_fiber]

/-- **Ansatz-independent identification.** The raw Kaluza Ricci expression is
exactly the standard coordinate Ricci contraction for the point inverse and
the full circle-invariant first and second metric jets. -/
theorem coordinateRicci_kaluzaNormalGauge
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (N P : Fin 4 ⊕ Unit) :
    coordinateRicci (kaluzaNormalGaugePointInverse u v d)
        (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
        (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2
          A1 A2 g2) N P =
      kaluzaNormalGaugeRicci u v c k₁ k₂ d phi1 phi2 A1 A2 g2 N P := by
  have hfiberDiagonal (N' P' : Fin 4 ⊕ Unit) :
      (∑ r : Unit,
        coordinateChristoffelJet (kaluzaNormalGaugePointInverse u v d)
          (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
          (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2
            A1 A2 g2)
          (Sum.inr r) (Sum.inr r) N' P') = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact coordinateChristoffelJet_kaluza_fiber u v c k₁ k₂ d phi1
      phi2 A1 A2 g2 r (Sum.inr r) N' P'
  have hfiberTrace (r : Unit) (P' : Fin 4 ⊕ Unit) :
      (∑ M : Fin 4 ⊕ Unit,
        coordinateChristoffelJet (kaluzaNormalGaugePointInverse u v d)
          (kaluzaNormalGaugeMetricJet u v c k₁ k₂ d phi1 A1)
          (kaluzaNormalGaugeFullMetricJet2 u v c k₁ k₂ d phi1 phi2
            A1 A2 g2)
          (Sum.inr r) M M P') = 0 := by
    apply Finset.sum_eq_zero
    intro M _
    exact coordinateChristoffelJet_kaluza_fiber u v c k₁ k₂ d phi1
      phi2 A1 A2 g2 r M M P'
  unfold coordinateRicci kaluzaNormalGaugeRicci
  rw [Fintype.sum_sum_type]
  rw [hfiberDiagonal]
  simp only [coordinateChristoffelJet_kaluza_base,
    coordinateChristoffel_kaluza]
  rcases N with n | _
  · simp only [coordinateChristoffelJet_kaluza_base]
    simp
  · rw [hfiberTrace]
    simp

end KaluzaSpecialization

end RainichKaluza
