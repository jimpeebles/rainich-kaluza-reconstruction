import RainichKaluza.AffineCoordinateRicci

/-!
# Nonlinear coordinate jets and the inhomogeneous connection law

This file begins the nonlinear chart-transition layer above the affine Ricci
covariance theorem.  A second coordinate jet consists of an invertible first
Jacobian together with the symmetric Hessian of the old coordinates as
functions of the new coordinates.  Differentiating a covariant metric then
adds the two Jacobian-Hessian product terms to the affine first-jet pullback.

The main result below derives, rather than assumes, the inhomogeneous
Levi--Civita transformation law from that transformed metric first jet.  It is
the exact nonlinear input needed for the subsequent differentiated-connection
and Ricci cancellation theorem.
-/

namespace RainichKaluza

section NonlinearChange

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- The two-jet of a coordinate transition `x=x(y)` at a point.  `affine.jac`
is `∂xᴬ/∂yᴹ`, while `second M N A` is `∂²xᴬ/∂yᴹ∂yᴺ`. -/
structure CoordinateChangeJet2 extends AffineCoordinateChange I where
  second : I → I → I → ℝ
  second_symm : ∀ M N A, second M N A = second N M A

namespace CoordinateChangeJet2

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev affine (C : CoordinateChangeJet2 I) : AffineCoordinateChange I :=
  C.toAffineCoordinateChange

/-- One Hessian-Jacobian contribution to the derivative of a pulled-back
covariant metric. -/
noncomputable def metricJacobianTerm (C : CoordinateChangeJet2 I)
    (g : I → I → ℝ) (R M N : I) : ℝ :=
  ∑ A : I, ∑ B : I, C.second R M A * C.affine.jac N B * g A B

/-- First metric jet after a nonlinear coordinate change.  For a symmetric
metric the last two terms are precisely the derivatives of the two Jacobian
factors in `g'_{MN}=J_M^A J_N^B g_{AB}`. -/
noncomputable def transformMetricJet1 (C : CoordinateChangeJet2 I)
    (g : I → I → ℝ) (dg : CoordinateMetricJet1 I) :
    CoordinateMetricJet1 I :=
  fun R M N => C.affine.transformCovariant3 dg R M N +
    C.metricJacobianTerm g R M N + C.metricJacobianTerm g R N M

/-- Nonlinear transformation of a connection: affine `(1,2)` transport plus
the inhomogeneous coordinate-Hessian term. -/
noncomputable def transformConnection (C : CoordinateChangeJet2 I)
    (G : I → I → I → ℝ) (M N P : I) : ℝ :=
  C.affine.transformConnection G M N P +
    ∑ A : I, C.affine.invJac A M * C.second N P A

theorem metricJacobianTerm_derivative_symm
    (C : CoordinateChangeJet2 I) (g : I → I → ℝ) (R M N : I) :
    C.metricJacobianTerm g R M N = C.metricJacobianTerm g M R N := by
  unfold metricJacobianTerm
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  rw [C.second_symm]

/-- The Christoffel symbols of the first kind acquire exactly the metric
contraction of the coordinate Hessian. -/
theorem coordinateChristoffelFirstKind_transformMetricJet1
    (C : CoordinateChangeJet2 I) (g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (Q N P : I) :
    coordinateChristoffelFirstKind (C.transformMetricJet1 g dg) Q N P =
      C.affine.transformCovariant3 (coordinateChristoffelFirstKind dg)
          Q N P + C.metricJacobianTerm g N P Q := by
  change coordinateChristoffelFirstKind
      (fun R M N => C.affine.transformCovariant3 dg R M N +
        C.metricJacobianTerm g R M N + C.metricJacobianTerm g R N M)
      Q N P = _
  calc
    _ = coordinateChristoffelFirstKind
          (C.affine.transformCovariant3 dg) Q N P +
        C.metricJacobianTerm g N P Q := by
      unfold coordinateChristoffelFirstKind
      dsimp only
      rw [C.metricJacobianTerm_derivative_symm g N Q P]
      rw [C.metricJacobianTerm_derivative_symm g P Q N]
      rw [C.metricJacobianTerm_derivative_symm g P N Q]
      ring
    _ = _ := by
      rw [C.affine.coordinateChristoffelFirstKind_transform]

omit [DecidableEq I] in
private theorem sum4_third_first
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [DecidableEq I] in
private theorem sum4_last2_first
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := sum4_third_first _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

omit [DecidableEq I] in
private theorem sum3_first_last (f : I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

private theorem invJac_jac_contract_tensor
    (C : CoordinateChangeJet2 I) (T : I → I → ℝ) :
    (∑ Q : I, ∑ D : I, ∑ B : I,
      C.affine.invJac D Q * C.affine.jac Q B * T D B) =
      ∑ D : I, T D D := by
  calc
    _ = ∑ D : I, ∑ B : I, ∑ Q : I,
        C.affine.invJac D Q * C.affine.jac Q B * T D B :=
      sum3_first_last _
    _ = ∑ D : I, ∑ B : I,
        (∑ Q : I, C.affine.invJac D Q * C.affine.jac Q B) * T D B := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro B _
      rw [Finset.sum_mul]
    _ = ∑ D : I, ∑ B : I, (if D = B then 1 else 0) * T D B := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro B _
      rw [C.affine.inv_jac_contract]
    _ = _ := by simp

private theorem transformedInverse_metricJacobianTerm_contract
    (C : CoordinateChangeJet2 I) (gInv g : I → I → ℝ)
    (hg : ∀ A B, g A B = g B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (M N P : I) :
    (∑ Q : I, C.affine.transformContravariant2 gInv M Q *
      C.metricJacobianTerm g N P Q) =
      ∑ A : I, C.affine.invJac A M * C.second N P A := by
  unfold AffineCoordinateChange.transformContravariant2 metricJacobianTerm
  calc
    _ = ∑ Q : I, ∑ A : I, ∑ B : I, ∑ C' : I, ∑ D : I,
        (C.affine.invJac C' M * C.affine.invJac D Q * gInv C' D) *
          (C.second N P A * C.affine.jac Q B * g A B) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ Q : I, ∑ C' : I, ∑ D : I, ∑ A : I, ∑ B : I,
        (C.affine.invJac C' M * C.affine.invJac D Q * gInv C' D) *
          (C.second N P A * C.affine.jac Q B * g A B) := by
      apply Finset.sum_congr rfl
      intro Q _
      exact sum4_last2_first _
    _ = ∑ C' : I, ∑ Q : I, ∑ D : I, ∑ A : I, ∑ B : I,
        (C.affine.invJac C' M * C.affine.invJac D Q * gInv C' D) *
          (C.second N P A * C.affine.jac Q B * g A B) :=
      Finset.sum_comm
    _ = ∑ C' : I, ∑ A : I, ∑ Q : I, ∑ D : I, ∑ B : I,
        (C.affine.invJac C' M * C.affine.invJac D Q * gInv C' D) *
          (C.second N P A * C.affine.jac Q B * g A B) := by
      apply Finset.sum_congr rfl
      intro C' _
      exact sum4_third_first _
    _ = ∑ C' : I, ∑ A : I,
        C.affine.invJac C' M * C.second N P A *
          (∑ Q : I, ∑ D : I, ∑ B : I,
            C.affine.invJac D Q * C.affine.jac Q B *
              (gInv C' D * g A B)) := by
      apply Finset.sum_congr rfl
      intro C' _
      apply Finset.sum_congr rfl
      intro A _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = ∑ C' : I, ∑ A : I,
        C.affine.invJac C' M * C.second N P A *
          (∑ D : I, gInv C' D * g A D) := by
      apply Finset.sum_congr rfl
      intro C' _
      apply Finset.sum_congr rfl
      intro A _
      rw [invJac_jac_contract_tensor C
        (fun D B => gInv C' D * g A B)]
    _ = ∑ C' : I, ∑ A : I,
        C.affine.invJac C' M * C.second N P A *
          (∑ D : I, gInv C' D * g D A) := by
      apply Finset.sum_congr rfl
      intro C' _
      apply Finset.sum_congr rfl
      intro A _
      apply congrArg (fun r : ℝ =>
        C.affine.invJac C' M * C.second N P A * r)
      apply Finset.sum_congr rfl
      intro D _
      rw [hg A D]
    _ = ∑ C' : I, ∑ A : I,
        C.affine.invJac C' M * C.second N P A *
          (if C' = A then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro C' _
      apply Finset.sum_congr rfl
      intro A _
      rw [hInv]
    _ = _ := by simp

/-- **Nonlinear Levi--Civita coordinate law.** Recomputing the connection
from the nonlinearly transformed metric first jet gives the affine tensorial
part plus the inhomogeneous coordinate-Hessian term. -/
theorem coordinateChristoffel_transformMetricJet1
    (C : CoordinateChangeJet2 I) (gInv g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I)
    (hg : ∀ A B, g A B = g B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (M N P : I) :
    coordinateChristoffel (C.affine.transformContravariant2 gInv)
        (C.transformMetricJet1 g dg) M N P =
      C.affine.transformConnection (coordinateChristoffel gInv dg) M N P +
        ∑ A : I, C.affine.invJac A M * C.second N P A := by
  unfold coordinateChristoffel
  calc
    _ = ∑ Q : I, C.affine.transformContravariant2 gInv M Q *
        (C.affine.transformCovariant3 (coordinateChristoffelFirstKind dg)
            Q N P + C.metricJacobianTerm g N P Q) := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [C.coordinateChristoffelFirstKind_transformMetricJet1]
    _ = (∑ Q : I, C.affine.transformContravariant2 gInv M Q *
          C.affine.transformCovariant3 (coordinateChristoffelFirstKind dg)
            Q N P) +
        ∑ Q : I, C.affine.transformContravariant2 gInv M Q *
          C.metricJacobianTerm g N P Q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = C.affine.transformConnection (coordinateChristoffel gInv dg) M N P +
        ∑ Q : I, C.affine.transformContravariant2 gInv M Q *
          C.metricJacobianTerm g N P Q := by
      have hfirst :
          (∑ Q : I, C.affine.transformContravariant2 gInv M Q *
            C.affine.transformCovariant3
              (coordinateChristoffelFirstKind dg) Q N P) =
            C.affine.transformConnection
              (coordinateChristoffel gInv dg) M N P := by
        calc
          _ = coordinateChristoffel
              (C.affine.transformContravariant2 gInv)
              (C.affine.transformCovariant3 dg) M N P := by
            unfold coordinateChristoffel
            apply Finset.sum_congr rfl
            intro Q _
            rw [C.affine.coordinateChristoffelFirstKind_transform]
          _ = _ := C.affine.coordinateChristoffel_transformConnection
            gInv dg M N P
      rw [hfirst]
    _ = _ := by
      rw [C.transformedInverse_metricJacobianTerm_contract gInv g hg hInv]
      rfl

theorem coordinateChristoffel_transformConnection
    (C : CoordinateChangeJet2 I) (gInv g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I)
    (hg : ∀ A B, g A B = g B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (M N P : I) :
    coordinateChristoffel (C.affine.transformContravariant2 gInv)
        (C.transformMetricJet1 g dg) M N P =
      C.transformConnection (coordinateChristoffel gInv dg) M N P := by
  exact C.coordinateChristoffel_transformMetricJet1
    gInv g dg hg hInv M N P

theorem transformConnection_symm
    (C : CoordinateChangeJet2 I) (G : I → I → I → ℝ)
    (hG : ∀ M N P, G M N P = G M P N) (M N P : I) :
    C.transformConnection G M N P = C.transformConnection G M P N := by
  unfold transformConnection AffineCoordinateChange.transformConnection
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro A _
    calc
      _ = ∑ D : I, ∑ B : I,
          C.affine.invJac A M * C.affine.jac N B *
            C.affine.jac P D * G A B D := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        rw [hG A D B]
        ring
  · apply Finset.sum_congr rfl
    intro A _
    rw [C.second_symm N P]

end CoordinateChangeJet2

/-- The three-jet of a coordinate transition.  The two adjacent-transposition
laws make the three derivative slots of `third` fully symmetric, as required
for genuine third derivatives of a smooth chart transition. -/
structure CoordinateChangeJet3 extends CoordinateChangeJet2 I where
  third : I → I → I → I → ℝ
  third_swap12 : ∀ R S M A, third R S M A = third S R M A
  third_swap23 : ∀ R S M A, third R S M A = third R M S A

namespace CoordinateChangeJet3

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev secondJet (C : CoordinateChangeJet3 I) : CoordinateChangeJet2 I :=
  C.toCoordinateChangeJet2

abbrev affine (C : CoordinateChangeJet3 I) : AffineCoordinateChange I :=
  C.secondJet.affine

/-- Derivative of the inverse coordinate Jacobian forced by differentiating
`J K = 1`. -/
noncomputable def inverseJacobianJet (C : CoordinateChangeJet3 I)
    (R A M : I) : ℝ :=
  -∑ B : I, ∑ S : I,
    C.affine.invJac B M * C.secondJet.second R S B * C.affine.invJac A S

/-- Derivative of the affine pullback of a metric first jet. -/
noncomputable def affineMetricJet1Jet (C : CoordinateChangeJet3 I)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (R S M N : I) : ℝ :=
  C.affine.transformCovariant4 ddg R S M N +
  (∑ A : I, ∑ B : I, ∑ D : I,
    C.secondJet.second R S A * C.affine.jac M B * C.affine.jac N D *
      dg A B D) +
  (∑ A : I, ∑ B : I, ∑ D : I,
    C.affine.jac S A * C.secondJet.second R M B * C.affine.jac N D *
      dg A B D) +
  ∑ A : I, ∑ B : I, ∑ D : I,
    C.affine.jac S A * C.affine.jac M B * C.secondJet.second R N D *
      dg A B D

/-- Derivative of one `metricJacobianTerm`. -/
noncomputable def metricJacobianTermJet (C : CoordinateChangeJet3 I)
    (g : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (R S M N : I) : ℝ :=
  (∑ A : I, ∑ B : I,
    C.third R S M A * C.affine.jac N B * g A B) +
  (∑ A : I, ∑ B : I,
    C.secondJet.second S M A * C.secondJet.second R N B * g A B) +
  ∑ D : I, ∑ A : I, ∑ B : I,
    C.secondJet.second S M A * C.affine.jac N B * C.affine.jac R D *
      dg D A B

/-- Complete second metric jet under a nonlinear coordinate three-jet,
obtained by differentiating `transformMetricJet1` by the product rule. -/
noncomputable def transformMetricJet2 (C : CoordinateChangeJet3 I)
    (g : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) : CoordinateMetricJet2 I :=
  fun R S M N => C.affineMetricJet1Jet dg ddg R S M N +
    C.metricJacobianTermJet g dg R S M N +
    C.metricJacobianTermJet g dg R S N M

theorem metricJacobianTermJet_derivative_symm
    (C : CoordinateChangeJet3 I) (g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (R S M N : I) :
    C.metricJacobianTermJet g dg R S M N =
      C.metricJacobianTermJet g dg R M S N := by
  unfold metricJacobianTermJet
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [C.third_swap23 R S M A]
    · apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [C.secondJet.second_symm S M A]
  · apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    rw [C.secondJet.second_symm S M A]

/-- The differentiated first-kind symbols inherit the same cancellation
pattern as the first-kind connection itself. -/
theorem coordinateChristoffelFirstKindJet_transformMetricJet2
    (C : CoordinateChangeJet3 I) (g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (R Q N P : I) :
    coordinateChristoffelFirstKindJet (C.transformMetricJet2 g dg ddg)
        R Q N P =
      coordinateChristoffelFirstKind (C.affineMetricJet1Jet dg ddg R)
          Q N P + C.metricJacobianTermJet g dg R N P Q := by
  unfold coordinateChristoffelFirstKindJet transformMetricJet2
  change coordinateChristoffelFirstKind
      (fun S M N => C.affineMetricJet1Jet dg ddg R S M N +
        C.metricJacobianTermJet g dg R S M N +
        C.metricJacobianTermJet g dg R S N M) Q N P = _
  unfold coordinateChristoffelFirstKind
  dsimp only
  rw [C.metricJacobianTermJet_derivative_symm g dg R N Q P]
  rw [C.metricJacobianTermJet_derivative_symm g dg R P Q N]
  rw [C.metricJacobianTermJet_derivative_symm g dg R P N Q]
  ring

omit [DecidableEq I] in
private theorem sum3_first_last (f : I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum3_add3 (f g h : I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, (f a b c + g a b c + h a b c)) =
      (∑ a, ∑ b, ∑ c, f a b c) +
      (∑ a, ∑ b, ∑ c, g a b c) +
      ∑ a, ∑ b, ∑ c, h a b c := by
  simp only [Finset.sum_add_distrib]

theorem jac_inverseJacobianJet_contract
    (C : CoordinateChangeJet3 I) (R M N : I) :
    (∑ A : I, C.affine.jac M A * C.inverseJacobianJet R A N) =
      -∑ B : I, C.affine.invJac B N * C.secondJet.second R M B := by
  unfold inverseJacobianJet
  calc
    _ = -∑ A : I, ∑ B : I, ∑ S : I,
        C.affine.jac M A *
          (C.affine.invJac B N * C.secondJet.second R S B *
            C.affine.invJac A S) := by
      simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.jac M A *
          (C.affine.invJac B N * C.secondJet.second R S B *
            C.affine.invJac A S) := by
      apply congrArg Neg.neg
      exact sum3_first_last _
    _ = -∑ B : I, ∑ S : I,
        C.affine.invJac B N * C.secondJet.second R S B *
          (∑ A : I, C.affine.jac M A * C.affine.invJac A S) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = -∑ B : I, ∑ S : I,
        C.affine.invJac B N * C.secondJet.second R S B *
          (if M = S then 1 else 0) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro S _
      rw [C.affine.jac_inv_contract]
    _ = _ := by simp

/-- Differentiating `J K = 1` gives zero, with the derivative of `K`
supplied by `inverseJacobianJet`. -/
theorem inverseJacobianJet_defining
    (C : CoordinateChangeJet3 I) (R M N : I) :
    (∑ A : I, C.secondJet.second R M A * C.affine.invJac A N) +
      (∑ A : I, C.affine.jac M A * C.inverseJacobianJet R A N) = 0 := by
  rw [C.jac_inverseJacobianJet_contract]
  have h :
      (∑ A : I, C.secondJet.second R M A * C.affine.invJac A N) =
        ∑ A : I, C.affine.invJac A N * C.secondJet.second R M A := by
    apply Finset.sum_congr rfl
    intro A _
    ring
  rw [h]
  ring

/-- The bracket before multiplication by the inverse Jacobian in the
nonlinear connection law. -/
noncomputable def connectionBracket (C : CoordinateChangeJet3 I)
    (G : I → I → I → ℝ) (A N P : I) : ℝ :=
  (∑ B : I, ∑ D : I,
    C.affine.jac N B * C.affine.jac P D * G A B D) +
    C.secondJet.second N P A

/-- The part of `connectionBracket` linear in the old connection. -/
noncomputable def affineConnectionBracket (C : CoordinateChangeJet3 I)
    (G : I → I → I → ℝ) (A N P : I) : ℝ :=
  ∑ B : I, ∑ D : I,
    C.affine.jac N B * C.affine.jac P D * G A B D

/-- Product-rule derivative of `connectionBracket`. -/
noncomputable def connectionBracketJet (C : CoordinateChangeJet3 I)
    (G : I → I → I → ℝ) (H : I → I → I → I → ℝ)
    (R A N P : I) : ℝ :=
  (∑ E : I, ∑ B : I, ∑ D : I,
    C.affine.jac R E * C.affine.jac N B * C.affine.jac P D * H E A B D) +
  (∑ B : I, ∑ D : I,
    C.secondJet.second R N B * C.affine.jac P D * G A B D) +
  (∑ B : I, ∑ D : I,
    C.affine.jac N B * C.secondJet.second R P D * G A B D) +
  C.third R N P A

/-- The part of the differentiated bracket caused by differentiating its
two lower Jacobian factors. -/
noncomputable def jacobianConnectionBracketJet
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (R A N P : I) : ℝ :=
  (∑ B : I, ∑ D : I,
    C.secondJet.second R N B * C.affine.jac P D * G A B D) +
  ∑ B : I, ∑ D : I,
    C.affine.jac N B * C.secondJet.second R P D * G A B D

/-- Nonlinear transformation law for a differentiated connection, written
as the exact product rule for `K_A^M · connectionBracket_A`. -/
noncomputable def transformConnectionJet (C : CoordinateChangeJet3 I)
    (G : I → I → I → ℝ) (H : I → I → I → I → ℝ)
    (R M N P : I) : ℝ :=
  (∑ A : I, C.inverseJacobianJet R A M * C.connectionBracket G A N P) +
    ∑ A : I, C.affine.invJac A M * C.connectionBracketJet G H R A N P

/-- The pure coordinate connection generated from a zero old connection. -/
noncomputable def pureCoordinateConnection (C : CoordinateChangeJet3 I)
    (M N P : I) : ℝ :=
  ∑ A : I, C.affine.invJac A M * C.secondJet.second N P A

/-- Derivative of the pure coordinate connection. -/
noncomputable def pureCoordinateConnectionJet (C : CoordinateChangeJet3 I)
    (R M N P : I) : ℝ :=
  (∑ A : I, C.inverseJacobianJet R A M * C.secondJet.second N P A) +
    ∑ A : I, C.affine.invJac A M * C.third R N P A

/-- The terms linear in the old connection and in the nonlinear coordinate
Hessian within the differentiated connection law. -/
noncomputable def mixedCoordinateConnectionJet
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (R M N P : I) : ℝ :=
  (∑ A : I, C.inverseJacobianJet R A M *
    C.affineConnectionBracket G A N P) +
  ∑ A : I, C.affine.invJac A M *
    C.jacobianConnectionBracketJet G R A N P

theorem transformConnection_zero (C : CoordinateChangeJet3 I) (M N P : I) :
    C.secondJet.transformConnection (fun _ _ _ => 0) M N P =
      C.pureCoordinateConnection M N P := by
  simp [CoordinateChangeJet2.transformConnection,
    AffineCoordinateChange.transformConnection, pureCoordinateConnection]

theorem transformConnectionJet_zero
    (C : CoordinateChangeJet3 I) (R M N P : I) :
    C.transformConnectionJet (fun _ _ _ => 0) (fun _ _ _ _ => 0) R M N P =
      C.pureCoordinateConnectionJet R M N P := by
  simp [transformConnectionJet, connectionBracket, connectionBracketJet,
    pureCoordinateConnectionJet]

theorem transformConnection_decompose
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (M N P : I) :
    C.secondJet.transformConnection G M N P =
      C.affine.transformConnection G M N P +
        C.pureCoordinateConnection M N P := rfl

set_option maxHeartbeats 600000 in
theorem transformConnectionJet_decompose
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ) (R M N P : I) :
    C.transformConnectionJet G H R M N P =
      C.affine.transformConnectionJet H R M N P +
        C.pureCoordinateConnectionJet R M N P +
        C.mixedCoordinateConnectionJet G R M N P := by
  have hOld :
      (∑ A : I, C.affine.invJac A M *
        (∑ E : I, ∑ B : I, ∑ D : I,
          C.affine.jac R E * C.affine.jac N B * C.affine.jac P D *
            H E A B D)) =
        C.affine.transformConnectionJet H R M N P := by
    unfold AffineCoordinateChange.transformConnectionJet
      AffineCoordinateChange.transformConnection
    calc
      _ = ∑ A : I, ∑ E : I, ∑ B : I, ∑ D : I,
          C.affine.invJac A M *
            (C.affine.jac R E * C.affine.jac N B * C.affine.jac P D *
              H E A B D) := by
        simp only [Finset.mul_sum]
      _ = ∑ E : I, ∑ A : I, ∑ B : I, ∑ D : I,
          C.affine.invJac A M *
            (C.affine.jac R E * C.affine.jac N B * C.affine.jac P D *
              H E A B D) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro E _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  unfold transformConnectionJet connectionBracket connectionBracketJet
    pureCoordinateConnectionJet mixedCoordinateConnectionJet
    affineConnectionBracket jacobianConnectionBracketJet
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hOld]
  ring

theorem connectionBracket_symm
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (hG : ∀ M N P, G M N P = G M P N) (A N P : I) :
    C.connectionBracket G A N P = C.connectionBracket G A P N := by
  unfold connectionBracket
  apply congrArg₂ (· + ·)
  · calc
      _ = ∑ D : I, ∑ B : I,
          C.affine.jac N B * C.affine.jac P D * G A B D :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        rw [hG A D B]
        ring
  · exact C.secondJet.second_symm N P A

theorem connectionBracketJet_symm
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ)
    (hG : ∀ M N P, G M N P = G M P N)
    (hH : ∀ R M N P, H R M N P = H R M P N)
    (R A N P : I) :
    C.connectionBracketJet G H R A N P =
      C.connectionBracketJet G H R A P N := by
  have h0 :
      (∑ E : I, ∑ B : I, ∑ D : I,
        C.affine.jac R E * C.affine.jac N B * C.affine.jac P D *
          H E A B D) =
      ∑ E : I, ∑ B : I, ∑ D : I,
        C.affine.jac R E * C.affine.jac P B * C.affine.jac N D *
          H E A B D := by
    apply Finset.sum_congr rfl
    intro E _
    calc
      _ = ∑ D : I, ∑ B : I,
          C.affine.jac R E * C.affine.jac N B * C.affine.jac P D *
            H E A B D := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        rw [hH E A D B]
        ring
  have h1 :
      (∑ B : I, ∑ D : I,
        C.secondJet.second R N B * C.affine.jac P D * G A B D) =
      ∑ B : I, ∑ D : I,
        C.affine.jac P B * C.secondJet.second R N D * G A B D := by
    calc
      _ = ∑ D : I, ∑ B : I,
          C.secondJet.second R N B * C.affine.jac P D * G A B D :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        rw [hG A D B]
        ring
  have h2 :
      (∑ B : I, ∑ D : I,
        C.affine.jac N B * C.secondJet.second R P D * G A B D) =
      ∑ B : I, ∑ D : I,
        C.secondJet.second R P B * C.affine.jac N D * G A B D := by
    calc
      _ = ∑ D : I, ∑ B : I,
          C.affine.jac N B * C.secondJet.second R P D * G A B D :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        rw [hG A D B]
        ring
  unfold connectionBracketJet
  rw [h0, h1, h2, C.third_swap23 R N P A]
  ring

theorem transformConnectionJet_symm
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ)
    (hG : ∀ M N P, G M N P = G M P N)
    (hH : ∀ R M N P, H R M N P = H R M P N)
    (R M N P : I) :
    C.transformConnectionJet G H R M N P =
      C.transformConnectionJet G H R M P N := by
  unfold transformConnectionJet
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro A _
    rw [C.connectionBracket_symm G hG A N P]
  · apply Finset.sum_congr rfl
    intro A _
    rw [C.connectionBracketJet_symm G H hG hH R A N P]

omit [DecidableEq I] in
private theorem sum4_last2_first
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      calc
        _ = ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

/-- Product-rule derivative of the transformed inverse metric.  The first
two terms differentiate the inverse Jacobian factors; the last term is the
affine transport of the old inverse-metric derivative. -/
noncomputable def transformInverseMetricJet (C : CoordinateChangeJet3 I)
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (R M N : I) : ℝ :=
  (∑ A : I, ∑ B : I,
    C.inverseJacobianJet R A M * C.affine.invJac B N * gInv A B) +
  (∑ A : I, ∑ B : I,
    C.affine.invJac A M * C.inverseJacobianJet R B N * gInv A B) +
  C.affine.transformContravariant2Jet
    (coordinateInverseMetricJet gInv dg) R M N

private theorem transformContravariant2_symm
    (C : CoordinateChangeJet3 I) (gInv : I → I → ℝ)
    (hgInv : ∀ A B, gInv A B = gInv B A) (M N : I) :
    C.affine.transformContravariant2 gInv M N =
      C.affine.transformContravariant2 gInv N M := by
  unfold AffineCoordinateChange.transformContravariant2
  calc
    _ = ∑ B : I, ∑ A : I,
        C.affine.invJac A M * C.affine.invJac B N * gInv A B :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [hgInv B A]
      ring

private theorem metricJacobianTerm_transformedInverse_contract
    (C : CoordinateChangeJet3 I) (gInv g : I → I → ℝ)
    (hg : ∀ A B, g A B = g B A)
    (hgInv : ∀ A B, gInv A B = gInv B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (M N P : I) :
    (∑ Q : I, C.secondJet.metricJacobianTerm g N P Q *
      C.affine.transformContravariant2 gInv Q M) =
      ∑ A : I, C.affine.invJac A M * C.secondJet.second N P A := by
  calc
    _ = ∑ Q : I, C.affine.transformContravariant2 gInv M Q *
        C.secondJet.metricJacobianTerm g N P Q := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [C.transformContravariant2_symm gInv hgInv Q M]
      ring
    _ = _ := C.secondJet.transformedInverse_metricJacobianTerm_contract
      gInv g hg hInv M N P

private theorem coordinateInverseMetricJet_metricJacobianTerm
    (C : CoordinateChangeJet3 I) (gInv g : I → I → ℝ)
    (hg : ∀ A B, g A B = g B A)
    (hgInv : ∀ A B, gInv A B = gInv B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (R M N : I) :
    coordinateInverseMetricJet
        (C.affine.transformContravariant2 gInv)
        (C.secondJet.metricJacobianTerm g) R M N =
      ∑ A : I, ∑ B : I,
        C.affine.invJac A M * C.inverseJacobianJet R B N * gInv A B := by
  unfold coordinateInverseMetricJet
  calc
    _ = -∑ X : I, C.affine.transformContravariant2 gInv M X *
        (∑ Y : I, C.secondJet.metricJacobianTerm g R X Y *
          C.affine.transformContravariant2 gInv Y N) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro X _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      ring
    _ = -∑ X : I, C.affine.transformContravariant2 gInv M X *
        (∑ A : I, C.affine.invJac A N *
          C.secondJet.second R X A) := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro X _
      rw [C.metricJacobianTerm_transformedInverse_contract
        gInv g hg hgInv hInv N R X]
    _ = -∑ X : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac B M * C.affine.invJac D X * gInv B D *
          (C.affine.invJac A N * C.secondJet.second R X A) := by
      unfold AffineCoordinateChange.transformContravariant2
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro X _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      simp only [Finset.sum_mul]
    _ = -∑ B : I, ∑ D : I, ∑ A : I, ∑ X : I,
        C.affine.invJac B M * C.affine.invJac D X * gInv B D *
          (C.affine.invJac A N * C.secondJet.second R X A) := by
      apply congrArg Neg.neg
      calc
        _ = ∑ B : I, ∑ D : I, ∑ X : I, ∑ A : I,
            C.affine.invJac B M * C.affine.invJac D X * gInv B D *
              (C.affine.invJac A N * C.secondJet.second R X A) :=
          sum4_last2_first _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro B _
          apply Finset.sum_congr rfl
          intro D _
          exact Finset.sum_comm
    _ = _ := by
      unfold inverseJacobianJet
      simp only [mul_neg, neg_mul, Finset.sum_neg_distrib,
        Finset.mul_sum, Finset.sum_mul]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro X _
      ring

private theorem coordinateInverseMetricJet_metricJacobianTerm_swap
    (C : CoordinateChangeJet3 I) (gInv g : I → I → ℝ)
    (hg : ∀ A B, g A B = g B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (R M N : I) :
    coordinateInverseMetricJet
        (C.affine.transformContravariant2 gInv)
        (fun S X Y => C.secondJet.metricJacobianTerm g S Y X) R M N =
      ∑ A : I, ∑ B : I,
        C.inverseJacobianJet R A M * C.affine.invJac B N * gInv A B := by
  unfold coordinateInverseMetricJet
  calc
    _ = -∑ Y : I,
        (∑ X : I, C.affine.transformContravariant2 gInv M X *
          C.secondJet.metricJacobianTerm g R Y X) *
            C.affine.transformContravariant2 gInv Y N := by
      apply congrArg Neg.neg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro Y _
      rw [Finset.sum_mul]
    _ = -∑ Y : I,
        (∑ A : I, C.affine.invJac A M *
          C.secondJet.second R Y A) *
            C.affine.transformContravariant2 gInv Y N := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro Y _
      rw [C.secondJet.transformedInverse_metricJacobianTerm_contract
        gInv g hg hInv M R Y]
    _ = -∑ Y : I, ∑ A : I, ∑ B : I, ∑ D : I,
        (C.affine.invJac A M * C.secondJet.second R Y A) *
          (C.affine.invJac B Y * C.affine.invJac D N * gInv B D) := by
      unfold AffineCoordinateChange.transformContravariant2
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro Y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      simp only [Finset.mul_sum]
    _ = -∑ B : I, ∑ D : I, ∑ A : I, ∑ Y : I,
        (C.affine.invJac A M * C.secondJet.second R Y A) *
          (C.affine.invJac B Y * C.affine.invJac D N * gInv B D) := by
      apply congrArg Neg.neg
      calc
        _ = ∑ B : I, ∑ D : I, ∑ Y : I, ∑ A : I,
            (C.affine.invJac A M * C.secondJet.second R Y A) *
              (C.affine.invJac B Y * C.affine.invJac D N * gInv B D) :=
          sum4_last2_first _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro B _
          apply Finset.sum_congr rfl
          intro D _
          exact Finset.sum_comm
    _ = _ := by
      unfold inverseJacobianJet
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro Y _
      ring

/-- Recomputing the inverse-metric derivative from the nonlinear transformed
metric first jet gives the exact product-rule derivative of the transformed
inverse metric. -/
theorem coordinateInverseMetricJet_transformMetricJet1
    (C : CoordinateChangeJet3 I) (gInv g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I)
    (hg : ∀ A B, g A B = g B A)
    (hgInv : ∀ A B, gInv A B = gInv B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (R M N : I) :
    coordinateInverseMetricJet
        (C.affine.transformContravariant2 gInv)
        (C.secondJet.transformMetricJet1 g dg) R M N =
      C.transformInverseMetricJet gInv dg R M N := by
  change coordinateInverseMetricJet
      (C.affine.transformContravariant2 gInv)
      (fun S X Y => C.affine.transformCovariant3 dg S X Y +
        C.secondJet.metricJacobianTerm g S X Y +
        C.secondJet.metricJacobianTerm g S Y X) R M N = _
  calc
    _ = coordinateInverseMetricJet
          (C.affine.transformContravariant2 gInv)
          (C.affine.transformCovariant3 dg) R M N +
        coordinateInverseMetricJet
          (C.affine.transformContravariant2 gInv)
          (C.secondJet.metricJacobianTerm g) R M N +
        coordinateInverseMetricJet
          (C.affine.transformContravariant2 gInv)
          (fun S X Y => C.secondJet.metricJacobianTerm g S Y X) R M N := by
      unfold coordinateInverseMetricJet
      simp only [mul_add, add_mul, Finset.sum_add_distrib]
      ring
    _ = _ := by
      rw [C.affine.coordinateInverseMetricJet_transformContravariant2Jet
        gInv dg R M N]
      rw [C.coordinateInverseMetricJet_metricJacobianTerm
        gInv g hg hgInv hInv R M N]
      rw [C.coordinateInverseMetricJet_metricJacobianTerm_swap
        gInv g hg hInv R M N]
      unfold transformInverseMetricJet
      ring

/-- Product-rule transform of the derivative of a first-kind Christoffel
symbol before the nonlinear metric-Hessian contribution is added. -/
noncomputable def affineChristoffelFirstKindJet
    (C : CoordinateChangeJet3 I) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (R Q N P : I) : ℝ :=
  C.affine.transformCovariant4
      (fun E => coordinateChristoffelFirstKindJet ddg E) R Q N P +
  (∑ A : I, ∑ B : I, ∑ D : I,
    C.secondJet.second R Q A * C.affine.jac N B * C.affine.jac P D *
      coordinateChristoffelFirstKind dg A B D) +
  (∑ A : I, ∑ B : I, ∑ D : I,
    C.affine.jac Q A * C.secondJet.second R N B * C.affine.jac P D *
      coordinateChristoffelFirstKind dg A B D) +
  ∑ A : I, ∑ B : I, ∑ D : I,
    C.affine.jac Q A * C.affine.jac N B * C.secondJet.second R P D *
      coordinateChristoffelFirstKind dg A B D

set_option maxHeartbeats 800000 in
/-- The `affineMetricJet1Jet` contribution to the differentiated first-kind
symbols is the four-term product rule for its three covariant Jacobian slots
and the old first-kind derivative. -/
theorem coordinateChristoffelFirstKind_affineMetricJet1Jet
    (C : CoordinateChangeJet3 I) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I)
    (R Q N P : I) :
    coordinateChristoffelFirstKind (C.affineMetricJet1Jet dg ddg R)
        Q N P = C.affineChristoffelFirstKindJet dg ddg R Q N P := by
  let T1 : CoordinateMetricJet1 I := fun S M L =>
    ∑ A : I, ∑ B : I, ∑ D : I,
      C.secondJet.second R S A * C.affine.jac M B * C.affine.jac L D *
        dg A B D
  let T2 : CoordinateMetricJet1 I := fun S M L =>
    ∑ A : I, ∑ B : I, ∑ D : I,
      C.affine.jac S A * C.secondJet.second R M B * C.affine.jac L D *
        dg A B D
  let T3 : CoordinateMetricJet1 I := fun S M L =>
    ∑ A : I, ∑ B : I, ∑ D : I,
      C.affine.jac S A * C.affine.jac M B * C.secondJet.second R L D *
        dg A B D
  have h0 :
      coordinateChristoffelFirstKind
          (fun S M L => C.affine.transformCovariant4 ddg R S M L) Q N P =
        C.affine.transformCovariant4
          (fun E => coordinateChristoffelFirstKindJet ddg E) R Q N P := by
    exact C.affine.coordinateChristoffelFirstKindJet_transform ddg R Q N P
  have hA : T1 N Q P =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.jac Q A * C.secondJet.second R N B * C.affine.jac P D *
          dg B A D := by
    dsimp [T1]
    calc
      _ = ∑ B : I, ∑ A : I, ∑ D : I,
          C.secondJet.second R N A * C.affine.jac Q B * C.affine.jac P D *
            dg A B D := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  have hB : T2 N Q P =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.secondJet.second R Q A * C.affine.jac N B * C.affine.jac P D *
          dg B A D := by
    dsimp [T2]
    calc
      _ = ∑ B : I, ∑ A : I, ∑ D : I,
          C.affine.jac N A * C.secondJet.second R Q B * C.affine.jac P D *
            dg A B D := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  have hC : T3 N Q P =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.jac Q A * C.affine.jac N B * C.secondJet.second R P D *
          dg B A D := by
    dsimp [T3]
    calc
      _ = ∑ B : I, ∑ A : I, ∑ D : I,
          C.affine.jac N A * C.affine.jac Q B * C.secondJet.second R P D *
            dg A B D := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  have hD : T1 P Q N =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.jac Q A * C.affine.jac N B * C.secondJet.second R P D *
          dg D A B := by
    dsimp [T1]
    calc
      _ = ∑ B : I, ∑ D : I, ∑ A : I,
          C.secondJet.second R P A * C.affine.jac Q B * C.affine.jac N D *
            dg A B D := sum3_first_last _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  have hE : T2 P Q N =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.secondJet.second R Q A * C.affine.jac N B * C.affine.jac P D *
          dg D A B := by
    dsimp [T2]
    calc
      _ = ∑ B : I, ∑ D : I, ∑ A : I,
          C.affine.jac P A * C.secondJet.second R Q B * C.affine.jac N D *
            dg A B D := sum3_first_last _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  have hF : T3 P Q N =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.jac Q A * C.secondJet.second R N B * C.affine.jac P D *
          dg D A B := by
    dsimp [T3]
    calc
      _ = ∑ B : I, ∑ D : I, ∑ A : I,
          C.affine.jac P A * C.affine.jac Q B * C.secondJet.second R N D *
            dg A B D := sum3_first_last _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  change coordinateChristoffelFirstKind
      (fun S M L => C.affine.transformCovariant4 ddg R S M L +
        T1 S M L + T2 S M L + T3 S M L) Q N P = _
  calc
    _ = coordinateChristoffelFirstKind
          (fun S M L => C.affine.transformCovariant4 ddg R S M L) Q N P +
        coordinateChristoffelFirstKind T1 Q N P +
        coordinateChristoffelFirstKind T2 Q N P +
        coordinateChristoffelFirstKind T3 Q N P := by
      unfold coordinateChristoffelFirstKind
      ring
    _ = _ := by
      rw [h0]
      unfold affineChristoffelFirstKindJet coordinateChristoffelFirstKind
      rw [hA, hB, hC, hD, hE, hF]
      dsimp [T1, T2, T3]
      ring_nf
      rw [sum3_add3, sum3_add3, sum3_add3]
      simp only [Finset.sum_mul]
      ring

/-- Fully explicit differentiated first-kind transformation law.  The first
summand differentiates the affine three-Jacobian pullback; the second is the
derivative of the inhomogeneous metric-Hessian term. -/
theorem coordinateChristoffelFirstKindJet_transformMetricJet2_explicit
    (C : CoordinateChangeJet3 I) (g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (R Q N P : I) :
    coordinateChristoffelFirstKindJet (C.transformMetricJet2 g dg ddg)
        R Q N P =
      C.affineChristoffelFirstKindJet dg ddg R Q N P +
        C.metricJacobianTermJet g dg R N P Q := by
  rw [C.coordinateChristoffelFirstKindJet_transformMetricJet2]
  rw [C.coordinateChristoffelFirstKind_affineMetricJet1Jet]

private theorem pureCoordinate_inverseTrace_add_traceProduct
    (C : CoordinateChangeJet3 I) (N P : I) :
    (∑ M : I, ∑ A : I,
      C.inverseJacobianJet M A M * C.secondJet.second N P A) +
    (∑ Q : I, (∑ M : I, C.pureCoordinateConnection M M Q) *
      C.pureCoordinateConnection Q N P) = 0 := by
  have hinv :
      (∑ M : I, ∑ A : I,
        C.inverseJacobianJet M A M * C.secondJet.second N P A) =
      -∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second M S B *
          C.affine.invJac A S * C.secondJet.second N P A := by
    unfold inverseJacobianJet
    calc
      _ = -∑ M : I, ∑ A : I, ∑ B : I, ∑ S : I,
          (C.affine.invJac B M * C.secondJet.second M S B *
            C.affine.invJac A S) * C.secondJet.second N P A := by
        simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      _ = _ := by
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro M _
        exact sum3_first_last _
  have hquad :
      (∑ Q : I, (∑ M : I, C.pureCoordinateConnection M M Q) *
        C.pureCoordinateConnection Q N P) =
      ∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second M S B *
          C.affine.invJac A S * C.secondJet.second N P A := by
    unfold pureCoordinateConnection
    calc
      _ = ∑ Q : I, ∑ A : I, ∑ M : I, ∑ B : I,
          (C.affine.invJac B M * C.secondJet.second M Q B) *
            (C.affine.invJac A Q * C.secondJet.second N P A) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ M : I, ∑ B : I, ∑ Q : I, ∑ A : I,
          (C.affine.invJac B M * C.secondJet.second M Q B) *
            (C.affine.invJac A Q * C.secondJet.second N P A) :=
        sum4_last2_first _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro S _
        apply Finset.sum_congr rfl
        intro A _
        ring
  rw [hinv, hquad]
  ring

omit [DecidableEq I] in
private theorem sum3_last_first (f : I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem pureCoordinate_inverseCross_add_crossProduct
    (C : CoordinateChangeJet3 I) (N P : I) :
    (∑ M : I, ∑ A : I,
      C.inverseJacobianJet N A M * C.secondJet.second M P A) +
    (∑ M : I, ∑ Q : I, C.pureCoordinateConnection M N Q *
      C.pureCoordinateConnection Q M P) = 0 := by
  have hinv :
      (∑ M : I, ∑ A : I,
        C.inverseJacobianJet N A M * C.secondJet.second M P A) =
      -∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second N S B *
          C.affine.invJac A S * C.secondJet.second M P A := by
    unfold inverseJacobianJet
    calc
      _ = -∑ M : I, ∑ A : I, ∑ B : I, ∑ S : I,
          (C.affine.invJac B M * C.secondJet.second N S B *
            C.affine.invJac A S) * C.secondJet.second M P A := by
        simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      _ = _ := by
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro M _
        exact sum3_first_last _
  have hquad :
      (∑ M : I, ∑ Q : I, C.pureCoordinateConnection M N Q *
        C.pureCoordinateConnection Q M P) =
      ∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second N S B *
          C.affine.invJac A S * C.secondJet.second M P A := by
    unfold pureCoordinateConnection
    calc
      _ = ∑ M : I, ∑ Q : I, ∑ A : I, ∑ B : I,
          (C.affine.invJac B M * C.secondJet.second N Q B) *
            (C.affine.invJac A Q * C.secondJet.second M P A) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ M : I, ∑ B : I, ∑ Q : I, ∑ A : I,
          (C.affine.invJac B M * C.secondJet.second N Q B) *
            (C.affine.invJac A Q * C.secondJet.second M P A) := by
        apply Finset.sum_congr rfl
        intro M _
        exact sum3_last_first _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro S _
        apply Finset.sum_congr rfl
        intro A _
        ring
  rw [hinv, hquad]
  ring

private theorem pureCoordinate_thirdTrace_eq
    (C : CoordinateChangeJet3 I) (N P : I) :
    (∑ M : I, ∑ A : I, C.affine.invJac A M * C.third M N P A) =
      ∑ M : I, ∑ A : I, C.affine.invJac A M * C.third N M P A := by
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro A _
  rw [C.third_swap12]

/-- The part of the Ricci contraction bilinear in two connections, together
with an independently supplied mixed differentiated-connection term. -/
noncomputable def mixedConnectionRicci
    (G Q : I → I → I → ℝ) (L : I → I → I → I → ℝ)
    (N P : I) : ℝ :=
  (∑ M : I, L M M N P) - (∑ M : I, L N M M P) +
  (∑ S : I, (∑ M : I, G M M S) * Q S N P) +
  (∑ S : I, (∑ M : I, Q M M S) * G S N P) -
  (∑ M : I, ∑ S : I, G M N S * Q S M P) -
  (∑ M : I, ∑ S : I, Q M N S * G S M P)

omit [DecidableEq I] in
theorem connectionRicci_add_decompose
    (G Q : I → I → I → ℝ)
    (H K L : I → I → I → I → ℝ) (N P : I) :
    AffineCoordinateChange.connectionRicci
        (fun M A B => G M A B + Q M A B)
        (fun R M A B => H R M A B + K R M A B + L R M A B) N P =
      AffineCoordinateChange.connectionRicci G H N P +
      AffineCoordinateChange.connectionRicci Q K N P +
      mixedConnectionRicci G Q L N P := by
  unfold AffineCoordinateChange.connectionRicci mixedConnectionRicci
  simp only [Finset.sum_add_distrib, mul_add, add_mul]
  ring

theorem transformConnection_eq_bracket
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (M N P : I) :
    C.secondJet.transformConnection G M N P =
      ∑ A : I, C.affine.invJac A M * C.connectionBracket G A N P := by
  unfold CoordinateChangeJet2.transformConnection connectionBracket
  unfold AffineCoordinateChange.transformConnection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  ring

private theorem jac_transformContravariant2_contract
    (C : CoordinateChangeJet3 I) (gInv : I → I → ℝ) (A Q : I) :
    (∑ M : I, C.affine.jac M A *
      C.affine.transformContravariant2 gInv M Q) =
      ∑ B : I, C.affine.invJac B Q * gInv A B := by
  unfold AffineCoordinateChange.transformContravariant2
  calc
    _ = ∑ B : I, ∑ D : I, ∑ M : I,
        C.affine.invJac B M * C.affine.jac M A *
          (C.affine.invJac D Q * gInv B D) := by
      calc
        _ = ∑ M : I, ∑ B : I, ∑ D : I,
            C.affine.jac M A *
              (C.affine.invJac B M * C.affine.invJac D Q * gInv B D) := by
          apply Finset.sum_congr rfl
          intro M _
          simp only [Finset.mul_sum]
        _ = ∑ B : I, ∑ D : I, ∑ M : I,
            C.affine.jac M A *
              (C.affine.invJac B M * C.affine.invJac D Q * gInv B D) :=
          sum3_first_last _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro B _
          apply Finset.sum_congr rfl
          intro D _
          apply Finset.sum_congr rfl
          intro M _
          ring
    _ = ∑ B : I, ∑ D : I,
        (∑ M : I, C.affine.invJac B M * C.affine.jac M A) *
          (C.affine.invJac D Q * gInv B D) := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.sum_mul]
    _ = ∑ B : I, ∑ D : I, (if B = A then 1 else 0) *
        (C.affine.invJac D Q * gInv B D) := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [C.affine.inv_jac_contract]
    _ = _ := by simp

/-- Raising the nonlinearly transformed first-kind symbols while retaining
the old upper index gives exactly `connectionBracket`.  This is the undifferentiated
contraction used by the remaining second-kind product-rule proof. -/
theorem transformedFirstKind_raise_eq_connectionBracket
    (C : CoordinateChangeJet3 I) (gInv g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I)
    (hg : ∀ A B, g A B = g B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (A N P : I) :
    (∑ Q : I, (∑ B : I, C.affine.invJac B Q * gInv A B) *
      coordinateChristoffelFirstKind
        (C.secondJet.transformMetricJet1 g dg) Q N P) =
      C.connectionBracket (coordinateChristoffel gInv dg) A N P := by
  let dg' := C.secondJet.transformMetricJet1 g dg
  have hconn (M : I) :
      coordinateChristoffel (C.affine.transformContravariant2 gInv)
          dg' M N P =
        C.secondJet.transformConnection (coordinateChristoffel gInv dg)
          M N P := by
    exact C.secondJet.coordinateChristoffel_transformConnection
      gInv g dg hg hInv M N P
  calc
    _ = ∑ Q : I,
        (∑ M : I, C.affine.jac M A *
          C.affine.transformContravariant2 gInv M Q) *
            coordinateChristoffelFirstKind dg' Q N P := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [C.jac_transformContravariant2_contract gInv A Q]
    _ = ∑ M : I, C.affine.jac M A *
        coordinateChristoffel (C.affine.transformContravariant2 gInv)
          dg' M N P := by
      unfold coordinateChristoffel
      symm
      calc
        _ = ∑ M : I, ∑ E : I,
            C.affine.jac M A *
              (C.affine.transformContravariant2 gInv M E *
                coordinateChristoffelFirstKind dg' E N P) := by
          apply Finset.sum_congr rfl
          intro M _
          rw [Finset.mul_sum]
        _ = ∑ E : I, ∑ M : I,
            C.affine.jac M A *
              (C.affine.transformContravariant2 gInv M E *
                coordinateChristoffelFirstKind dg' E N P) :=
          Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro E _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro M _
          ring
    _ = ∑ M : I, C.affine.jac M A *
        C.secondJet.transformConnection (coordinateChristoffel gInv dg)
          M N P := by
      apply Finset.sum_congr rfl
      intro M _
      rw [hconn]
    _ = _ := by
      calc
        _ = ∑ M : I, C.affine.jac M A *
            (∑ E : I, C.affine.invJac E M *
              C.connectionBracket (coordinateChristoffel gInv dg) E N P) := by
          apply Finset.sum_congr rfl
          intro M _
          rw [C.transformConnection_eq_bracket]
        _ = ∑ M : I, ∑ E : I,
            C.affine.jac M A * C.affine.invJac E M *
              C.connectionBracket (coordinateChristoffel gInv dg) E N P := by
          apply Finset.sum_congr rfl
          intro M _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro E _
          ring
        _ = ∑ E : I, (∑ M : I,
            C.affine.invJac E M * C.affine.jac M A) *
              C.connectionBracket (coordinateChristoffel gInv dg) E N P := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro E _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro M _
          ring
        _ = ∑ E : I, (if E = A then 1 else 0) *
              C.connectionBracket (coordinateChristoffel gInv dg) E N P := by
          apply Finset.sum_congr rfl
          intro E _
          rw [C.affine.inv_jac_contract]
        _ = _ := by simp

theorem affineTransformConnection_eq_bracket
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (M N P : I) :
    C.affine.transformConnection G M N P =
      ∑ A : I, C.affine.invJac A M *
        C.affineConnectionBracket G A N P := by
  unfold AffineCoordinateChange.transformConnection affineConnectionBracket
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  ring

private theorem jacCovector_invContravector_contract
    (C : CoordinateChangeJet3 I) (u v : I → ℝ) :
    (∑ S : I, (∑ D : I, C.affine.jac S D * u D) *
      (∑ A : I, C.affine.invJac A S * v A)) =
      ∑ D : I, u D * v D := by
  calc
    _ = ∑ S : I, ∑ A : I, ∑ D : I,
        C.affine.jac S D * u D * (C.affine.invJac A S * v A) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ D : I, ∑ A : I, ∑ S : I,
        C.affine.invJac A S * C.affine.jac S D * (u D * v A) := by
      calc
        _ = ∑ D : I, ∑ S : I, ∑ A : I,
            C.affine.jac S D * u D *
              (C.affine.invJac A S * v A) := sum3_last_first _
        _ = ∑ D : I, ∑ A : I, ∑ S : I,
            C.affine.jac S D * u D *
              (C.affine.invJac A S * v A) := by
          apply Finset.sum_congr rfl
          intro D _
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro D _
          apply Finset.sum_congr rfl
          intro A _
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = ∑ D : I, ∑ A : I,
        (∑ S : I, C.affine.invJac A S * C.affine.jac S D) *
          (u D * v A) := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_mul]
    _ = ∑ D : I, ∑ A : I, (if A = D then 1 else 0) *
        (u D * v A) := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro A _
      rw [C.affine.inv_jac_contract]
    _ = _ := by simp

private theorem affineConnection_pureContract
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (M N R P : I) :
    (∑ S : I, C.affine.transformConnection G M N S *
      C.pureCoordinateConnection S R P) =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * C.affine.jac N B * G A B D *
          C.secondJet.second R P D := by
  have hbracket (A : I) :
      (∑ S : I, C.affineConnectionBracket G A N S *
        (∑ E : I, C.affine.invJac E S *
          C.secondJet.second R P E)) =
      ∑ B : I, C.affine.jac N B *
        (∑ S : I, (∑ D : I, C.affine.jac S D * G A B D) *
          (∑ E : I, C.affine.invJac E S *
            C.secondJet.second R P E)) := by
    unfold affineConnectionBracket
    calc
      _ = ∑ S : I, ∑ B : I,
          (∑ D : I, C.affine.jac N B * C.affine.jac S D * G A B D) *
          (∑ E : I, C.affine.invJac E S *
            C.secondJet.second R P E) := by
        simp only [Finset.sum_mul]
      _ = ∑ B : I, ∑ S : I,
          (∑ D : I, C.affine.jac N B * C.affine.jac S D * G A B D) *
          (∑ E : I, C.affine.invJac E S *
            C.secondJet.second R P E) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        calc
          _ = (∑ D : I,
              C.affine.jac N B * C.affine.jac S D * G A B D) *
              (∑ E : I, C.affine.invJac E S *
                C.secondJet.second R P E) := by
            rw [Finset.mul_sum]
          _ = (C.affine.jac N B *
              ∑ D : I, C.affine.jac S D * G A B D) *
              (∑ E : I, C.affine.invJac E S *
                C.secondJet.second R P E) := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro D _
            ring
          _ = _ := by ring
  calc
    _ = ∑ S : I,
        (∑ A : I, C.affine.invJac A M *
          C.affineConnectionBracket G A N S) *
        (∑ D : I, C.affine.invJac D S *
          C.secondJet.second R P D) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [C.affineTransformConnection_eq_bracket]
      rfl
    _ = ∑ S : I, ∑ A : I,
        C.affine.invJac A M * C.affineConnectionBracket G A N S *
          (∑ E : I, C.affine.invJac E S *
            C.secondJet.second R P E) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_mul]
    _ = ∑ A : I, ∑ S : I,
        C.affine.invJac A M * C.affineConnectionBracket G A N S *
          (∑ E : I, C.affine.invJac E S *
            C.secondJet.second R P E) := Finset.sum_comm
    _ = ∑ A : I, C.affine.invJac A M *
        (∑ S : I, C.affineConnectionBracket G A N S *
          (∑ E : I, C.affine.invJac E S *
            C.secondJet.second R P E)) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ A : I, C.affine.invJac A M *
        (∑ B : I, C.affine.jac N B *
          (∑ S : I, (∑ D : I, C.affine.jac S D * G A B D) *
            (∑ E : I, C.affine.invJac E S *
              C.secondJet.second R P E))) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [hbracket A]
    _ = ∑ A : I, ∑ B : I, C.affine.invJac A M *
        C.affine.jac N B *
          (∑ S : I, (∑ D : I, C.affine.jac S D * G A B D) *
            (∑ E : I, C.affine.invJac E S *
              C.secondJet.second R P E)) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = ∑ A : I, ∑ B : I, C.affine.invJac A M *
        C.affine.jac N B *
          (∑ D : I, G A B D * C.secondJet.second R P D) := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [C.jacCovector_invContravector_contract]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      ring

private theorem mixedInverseTrace_add_tracePureAffine
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (N P : I) :
    (∑ M : I, ∑ A : I, C.inverseJacobianJet M A M *
      C.affineConnectionBracket G A N P) +
    (∑ S : I, (∑ M : I, C.pureCoordinateConnection M M S) *
      C.affine.transformConnection G S N P) = 0 := by
  have hinv :
      (∑ M : I, ∑ A : I, C.inverseJacobianJet M A M *
        C.affineConnectionBracket G A N P) =
      -∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second M S B *
          C.affine.invJac A S * C.affineConnectionBracket G A N P := by
    unfold inverseJacobianJet
    calc
      _ = -∑ M : I, ∑ A : I, ∑ B : I, ∑ S : I,
          (C.affine.invJac B M * C.secondJet.second M S B *
            C.affine.invJac A S) * C.affineConnectionBracket G A N P := by
        simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      _ = _ := by
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro M _
        exact sum3_first_last _
  have hquad :
      (∑ S : I, (∑ M : I, C.pureCoordinateConnection M M S) *
        C.affine.transformConnection G S N P) =
      ∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second M S B *
          C.affine.invJac A S * C.affineConnectionBracket G A N P := by
    calc
      _ = ∑ S : I,
          (∑ M : I, ∑ B : I,
            C.affine.invJac B M * C.secondJet.second M S B) *
          (∑ A : I, C.affine.invJac A S *
            C.affineConnectionBracket G A N P) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [C.affineTransformConnection_eq_bracket]
        rfl
      _ = ∑ S : I, ∑ A : I, ∑ M : I, ∑ B : I,
          (C.affine.invJac B M * C.secondJet.second M S B) *
            (C.affine.invJac A S * C.affineConnectionBracket G A N P) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
          (C.affine.invJac B M * C.secondJet.second M S B) *
            (C.affine.invJac A S * C.affineConnectionBracket G A N P) :=
        sum4_last2_first _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro S _
        apply Finset.sum_congr rfl
        intro A _
        ring
  rw [hinv, hquad]
  ring

private theorem mixedInverseCross_add_pureAffineCross
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (N P : I) :
    (∑ M : I, ∑ A : I, C.inverseJacobianJet N A M *
      C.affineConnectionBracket G A M P) +
    (∑ M : I, ∑ S : I, C.pureCoordinateConnection M N S *
      C.affine.transformConnection G S M P) = 0 := by
  have hinv :
      (∑ M : I, ∑ A : I, C.inverseJacobianJet N A M *
        C.affineConnectionBracket G A M P) =
      -∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second N S B *
          C.affine.invJac A S * C.affineConnectionBracket G A M P := by
    unfold inverseJacobianJet
    calc
      _ = -∑ M : I, ∑ A : I, ∑ B : I, ∑ S : I,
          (C.affine.invJac B M * C.secondJet.second N S B *
            C.affine.invJac A S) * C.affineConnectionBracket G A M P := by
        simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
      _ = _ := by
        apply congrArg Neg.neg
        apply Finset.sum_congr rfl
        intro M _
        exact sum3_first_last _
  have hquad :
      (∑ M : I, ∑ S : I, C.pureCoordinateConnection M N S *
        C.affine.transformConnection G S M P) =
      ∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
        C.affine.invJac B M * C.secondJet.second N S B *
          C.affine.invJac A S * C.affineConnectionBracket G A M P := by
    calc
      _ = ∑ M : I, ∑ S : I,
          (∑ B : I, C.affine.invJac B M * C.secondJet.second N S B) *
          (∑ A : I, C.affine.invJac A S *
            C.affineConnectionBracket G A M P) := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro S _
        rw [C.affineTransformConnection_eq_bracket]
        rfl
      _ = ∑ M : I, ∑ S : I, ∑ A : I, ∑ B : I,
          (C.affine.invJac B M * C.secondJet.second N S B) *
            (C.affine.invJac A S * C.affineConnectionBracket G A M P) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ M : I, ∑ B : I, ∑ S : I, ∑ A : I,
          (C.affine.invJac B M * C.secondJet.second N S B) *
            (C.affine.invJac A S * C.affineConnectionBracket G A M P) := by
        apply Finset.sum_congr rfl
        intro M _
        exact sum3_last_first _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro S _
        apply Finset.sum_congr rfl
        intro A _
        ring
  rw [hinv, hquad]
  ring

private theorem jacobianMixedTrace_cancels
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (N P : I) :
    (∑ M : I, ∑ A : I, C.affine.invJac A M *
      C.jacobianConnectionBracketJet G M A N P) -
    (∑ M : I, ∑ A : I, C.affine.invJac A M *
      C.jacobianConnectionBracketJet G N A M P) +
    (∑ S : I, (∑ M : I, C.affine.transformConnection G M M S) *
      C.pureCoordinateConnection S N P) -
    (∑ M : I, ∑ S : I, C.affine.transformConnection G M N S *
      C.pureCoordinateConnection S M P) = 0 := by
  have htrace :
      (∑ S : I, (∑ M : I, C.affine.transformConnection G M M S) *
        C.pureCoordinateConnection S N P) =
      ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * C.affine.jac M B * G A B D *
          C.secondJet.second N P D := by
    calc
      _ = ∑ S : I, ∑ M : I,
          C.affine.transformConnection G M M S *
            C.pureCoordinateConnection S N P := by
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.sum_mul]
      _ = ∑ M : I, ∑ S : I,
          C.affine.transformConnection G M M S *
            C.pureCoordinateConnection S N P := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro M _
        exact C.affineConnection_pureContract G M M N P
  have hcross :
      (∑ M : I, ∑ S : I, C.affine.transformConnection G M N S *
        C.pureCoordinateConnection S M P) =
      ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * C.affine.jac N B * G A B D *
          C.secondJet.second M P D := by
    apply Finset.sum_congr rfl
    intro M _
    exact C.affineConnection_pureContract G M N M P
  have hsym :
      (∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * (C.secondJet.second M N B *
          C.affine.jac P D * G A B D)) =
      ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * (C.secondJet.second N M B *
          C.affine.jac P D * G A B D) := by
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro D _
    rw [C.secondJet.second_symm M N B]
  have hT2 :
      (∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * (C.affine.jac N B *
          C.secondJet.second M P D * G A B D)) =
      ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * C.affine.jac N B * G A B D *
          C.secondJet.second M P D := by
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro D _
    ring
  have hU2 :
      (∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * (C.affine.jac M B *
          C.secondJet.second N P D * G A B D)) =
      ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.affine.invJac A M * C.affine.jac M B * G A B D *
          C.secondJet.second N P D := by
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro D _
    ring
  rw [htrace, hcross]
  unfold jacobianConnectionBracketJet
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsym, hT2, hU2]
  ring

/-- The last nonlinear Ricci correction vanishes: every term linear in both
the old connection and the coordinate Hessian cancels. -/
theorem mixedConnectionRicci_zero
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ) (N P : I) :
    mixedConnectionRicci
      (C.affine.transformConnection G) C.pureCoordinateConnection
      (C.mixedCoordinateConnectionJet G) N P = 0 := by
  have hInvTrace := C.mixedInverseTrace_add_tracePureAffine G N P
  have hInvCross := C.mixedInverseCross_add_pureAffineCross G N P
  have hJac := C.jacobianMixedTrace_cancels G N P
  unfold mixedConnectionRicci mixedCoordinateConnectionJet
  simp only [Finset.sum_add_distrib]
  linear_combination hInvTrace - hInvCross + hJac

/-- A flat zero connection remains Ricci-flat when written through an
arbitrary nonlinear coordinate three-jet.  This is the pure inhomogeneous
Christoffel cancellation: third derivatives cancel by symmetry, while the
inverse-Jacobian derivative terms cancel the two quadratic connection terms. -/
theorem connectionRicci_pureCoordinate_zero
    (C : CoordinateChangeJet3 I) (N P : I) :
    AffineCoordinateChange.connectionRicci
      (C.secondJet.transformConnection (fun _ _ _ => 0))
      (C.transformConnectionJet (fun _ _ _ => 0) (fun _ _ _ _ => 0))
      N P = 0 := by
  have hG :
      C.secondJet.transformConnection (fun _ _ _ => 0) =
        C.pureCoordinateConnection := by
    funext M N' P'
    exact C.transformConnection_zero M N' P'
  have hH :
      C.transformConnectionJet (fun _ _ _ => 0) (fun _ _ _ _ => 0) =
        C.pureCoordinateConnectionJet := by
    funext R M N' P'
    exact C.transformConnectionJet_zero R M N' P'
  rw [hG, hH]
  unfold AffineCoordinateChange.connectionRicci pureCoordinateConnectionJet
  simp only [Finset.sum_add_distrib]
  have htrace := C.pureCoordinate_inverseTrace_add_traceProduct N P
  have hcross := C.pureCoordinate_inverseCross_add_crossProduct N P
  have hthird := C.pureCoordinate_thirdTrace_eq N P
  rw [hthird]
  linear_combination htrace - hcross

/-- Exact reduction of the nonlinear Ricci covariance problem.  The affine
Ricci pullback and the pure-coordinate curvature are already discharged; the
only remaining term is the part linear in both the old connection and the
coordinate Hessian. -/
theorem connectionRicci_transform_eq_affine_add_mixed
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ) (N P : I) :
    AffineCoordinateChange.connectionRicci
        (C.secondJet.transformConnection G)
        (C.transformConnectionJet G H) N P =
      C.affine.transformCovariant2
          (AffineCoordinateChange.connectionRicci G H) N P +
        mixedConnectionRicci
          (C.affine.transformConnection G) C.pureCoordinateConnection
          (C.mixedCoordinateConnectionJet G) N P := by
  have hG : C.secondJet.transformConnection G =
      fun M N' P' => C.affine.transformConnection G M N' P' +
        C.pureCoordinateConnection M N' P' := by
    funext M N' P'
    exact C.transformConnection_decompose G M N' P'
  have hH : C.transformConnectionJet G H =
      fun R M N' P' => C.affine.transformConnectionJet H R M N' P' +
        C.pureCoordinateConnectionJet R M N' P' +
        C.mixedCoordinateConnectionJet G R M N' P' := by
    funext R M N' P'
    exact C.transformConnectionJet_decompose G H R M N' P'
  have hpure :
      AffineCoordinateChange.connectionRicci C.pureCoordinateConnection
        C.pureCoordinateConnectionJet N P = 0 := by
    have hzero := C.connectionRicci_pureCoordinate_zero N P
    have hzG :
        C.secondJet.transformConnection (fun _ _ _ => 0) =
          C.pureCoordinateConnection := by
      funext M N' P'
      exact C.transformConnection_zero M N' P'
    have hzH :
        C.transformConnectionJet (fun _ _ _ => 0) (fun _ _ _ _ => 0) =
          C.pureCoordinateConnectionJet := by
      funext R M N' P'
      exact C.transformConnectionJet_zero R M N' P'
    rw [hzG, hzH] at hzero
    exact hzero
  rw [hG, hH]
  rw [connectionRicci_add_decompose]
  rw [C.affine.connectionRicci_transform]
  rw [hpure]
  ring

/-- **Nonlinear Ricci covariance for connection three-jets.** The complete
inhomogeneous connection law and its product-rule derivative have a Ricci
contraction equal to the covariant pullback of the old Ricci contraction. -/
theorem connectionRicci_transform
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ) (N P : I) :
    AffineCoordinateChange.connectionRicci
        (C.secondJet.transformConnection G)
        (C.transformConnectionJet G H) N P =
      C.affine.transformCovariant2
        (AffineCoordinateChange.connectionRicci G H) N P := by
  rw [C.connectionRicci_transform_eq_affine_add_mixed]
  rw [C.mixedConnectionRicci_zero]
  ring

/-- Nonlinear coordinate three-jets preserve and reflect vanishing of the
Ricci contraction formed from a connection and its product-rule derivative. -/
theorem connectionRicciFlat_transform_iff
    (C : CoordinateChangeJet3 I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ) :
    (∀ N P, AffineCoordinateChange.connectionRicci
        (C.secondJet.transformConnection G)
        (C.transformConnectionJet G H) N P = 0) ↔
      ∀ N P, AffineCoordinateChange.connectionRicci G H N P = 0 := by
  have hzero := C.affine.transformCovariant2_zero_iff
    (AffineCoordinateChange.connectionRicci G H)
  constructor
  · intro h
    apply hzero.mp
    intro N P
    rw [← C.connectionRicci_transform]
    exact h N P
  · intro h N P
    rw [C.connectionRicci_transform]
    exact hzero.mpr h N P

/-- Once a transformed metric second jet is known to induce the product-rule
connection jet, nonlinear covariance of its recomputed coordinate Ricci
tensor follows from the universal connection theorem.  This theorem isolates
the sole remaining metric-second-jet realization obligation. -/
theorem coordinateRicci_transform_of_christoffelJet
    (C : CoordinateChangeJet3 I) (gInv g : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (ddg ddg' : CoordinateMetricJet2 I)
    (hg : ∀ A B, g A B = g B A)
    (hInv : ∀ A B, (∑ D : I, gInv A D * g D B) =
      if A = B then 1 else 0)
    (hJet : coordinateChristoffelJet
        (C.affine.transformContravariant2 gInv)
        (C.secondJet.transformMetricJet1 g dg) ddg' =
      C.transformConnectionJet (coordinateChristoffel gInv dg)
        (coordinateChristoffelJet gInv dg ddg))
    (N P : I) :
    coordinateRicci (C.affine.transformContravariant2 gInv)
        (C.secondJet.transformMetricJet1 g dg) ddg' N P =
      C.affine.transformCovariant2 (coordinateRicci gInv dg ddg) N P := by
  rw [AffineCoordinateChange.coordinateRicci_eq_connectionRicci]
  have hG :
      coordinateChristoffel (C.affine.transformContravariant2 gInv)
          (C.secondJet.transformMetricJet1 g dg) =
        C.secondJet.transformConnection (coordinateChristoffel gInv dg) := by
    funext M N' P'
    exact C.secondJet.coordinateChristoffel_transformConnection
      gInv g dg hg hInv M N' P'
  rw [hG, hJet]
  rw [C.connectionRicci_transform]
  rfl

end CoordinateChangeJet3

end NonlinearChange

end RainichKaluza
