import RainichKaluza.CoordinateRicci

/-!
# The first coordinate jet of Ricci curvature

This file differentiates the coordinate Ricci formula algebraically.  The
third metric jet is ordered as

`dddg R S T M N = ∂_R ∂_S ∂_T g_MN`.

At a normal-coordinate point the resulting expression reduces to the usual
normal-frame Ricci contraction applied, in each derivative direction, to the
third metric jet.  This gives the precise bridge between a formal metric
three-jet and the first prolongation of the coordinate Einstein equation.
-/

namespace RainichKaluza

/-- Third coordinate jet of a metric:
`dddg R S T M N = ∂_R∂_S∂_T g_MN`. -/
abbrev CoordinateMetricJet3 (I : Type*) := I → I → I → I → I → ℝ

section CoordinateCurvature

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Product-rule derivative, in direction `R`, of
`coordinateInverseMetricJet gInv dg S M N`.

This is the second derivative of the inverse metric forced by
`g g⁻¹ = 1`; no independent inverse-metric jet is supplied. -/
noncomputable def coordinateInverseMetricJetFirstJet
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I)
    (R S M N : I) : ℝ :=
  -∑ A : I, ∑ B : I, (
    coordinateInverseMetricJet gInv dg R M A * dg S A B * gInv B N +
    gInv M A * ddg R S A B * gInv B N +
    gInv M A * dg S A B *
      coordinateInverseMetricJet gInv dg R B N)

/-- Derivative, in direction `R`, of the first-kind Christoffel jet whose
stored derivative direction is `S`. -/
noncomputable def coordinateChristoffelFirstKindJetFirstJet
    (dddg : CoordinateMetricJet3 I) (R S Q N P : I) : ℝ :=
  (dddg R S N Q P + dddg R S P Q N - dddg R S Q N P) / 2

/-- Product-rule derivative, in direction `R`, of
`coordinateChristoffelJet gInv dg ddg S M N P`. -/
noncomputable def coordinateChristoffelJetFirstJet
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (dddg : CoordinateMetricJet3 I)
    (R S M N P : I) : ℝ :=
  ∑ Q : I, (
    coordinateInverseMetricJetFirstJet gInv dg ddg R S M Q *
        coordinateChristoffelFirstKind dg Q N P +
      coordinateInverseMetricJet gInv dg S M Q *
        coordinateChristoffelFirstKindJet ddg R Q N P +
      coordinateInverseMetricJet gInv dg R M Q *
        coordinateChristoffelFirstKindJet ddg S Q N P +
      gInv M Q *
        coordinateChristoffelFirstKindJetFirstJet dddg R S Q N P)

/-- The genuine product-rule derivative of `coordinateRicci` in direction
`R`, with the inverse-metric derivative constrained by the metric first jet.

The four lines respectively differentiate the two `∂Γ` contractions and
the two quadratic `ΓΓ` contractions in the coordinate Ricci formula. -/
noncomputable def coordinateRicciFirstJet
    (gInv : Matrix I I ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (dddg : CoordinateMetricJet3 I)
    (R N P : I) : ℝ :=
  (∑ M : I,
      coordinateChristoffelJetFirstJet gInv dg ddg dddg R M M N P) -
    (∑ M : I,
      coordinateChristoffelJetFirstJet gInv dg ddg dddg R N M M P) +
    (∑ Q : I,
      ((∑ M : I, coordinateChristoffelJet gInv dg ddg R M M Q) *
          coordinateChristoffel gInv dg Q N P +
        (∑ M : I, coordinateChristoffel gInv dg M M Q) *
          coordinateChristoffelJet gInv dg ddg R Q N P)) -
    (∑ M : I, ∑ Q : I,
      (coordinateChristoffelJet gInv dg ddg R M N Q *
          coordinateChristoffel gInv dg Q M P +
        coordinateChristoffel gInv dg M N Q *
          coordinateChristoffelJet gInv dg ddg R Q M P))

end CoordinateCurvature

set_option maxHeartbeats 2000000 in
/-- At a Minkowski normal-coordinate point, the algebraic first derivative
of the full coordinate Ricci formula is exactly the normal-frame Ricci
contraction of the third metric jet in the selected derivative direction.

In particular the common second metric jet drops out: every lower-order
product term contains the vanishing metric first jet or Christoffel symbol. -/
theorem coordinateRicciFirstJet_minkowski_zero
    (g2 : CoordinateMetricJet2 (Fin 4))
    (g3 : CoordinateMetricJet3 (Fin 4)) (r n p : Fin 4) :
    coordinateRicciFirstJet minkowskiMetric 0 g2 g3 r n p =
      normalFrameBaseRicci minkowskiSign (g3 r) n p := by
  fin_cases r <;> fin_cases n <;> fin_cases p <;>
    simp [coordinateRicciFirstJet, coordinateChristoffelJetFirstJet,
      coordinateInverseMetricJetFirstJet,
      coordinateChristoffelFirstKindJetFirstJet,
      coordinateChristoffelJet, coordinateChristoffel,
      coordinateInverseMetricJet, coordinateChristoffelFirstKind,
      coordinateChristoffelFirstKindJet, normalFrameBaseRicci,
      minkowskiMetric, minkowskiSign, Fin.sum_univ_succ] <;>
    ring

end RainichKaluza
