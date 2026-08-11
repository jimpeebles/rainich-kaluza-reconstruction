import RainichKaluza.CoordinateRicci

/-!
# Affine covariance of coordinate Ricci curvature

This file proves the first genuine coordinate-change theorem for the generic
coordinate curvature layer.  An invertible constant Jacobian transforms the
inverse metric and the first and second covariant metric jets in the usual
way.  The Levi--Civita symbols then obey the affine connection law and the
coordinate Ricci contraction transforms as a covariant two-tensor.

The constant-Jacobian restriction is deliberate: this is the exact affine
base case for the later nonlinear chart-transition theorem, where second and
third derivatives of the transition map generate and then cancel the
inhomogeneous Christoffel terms.
-/

namespace RainichKaluza

open Matrix

section AffineChange

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- An invertible constant coordinate Jacobian.  `jac M A` gives the old
coordinate component of the new coordinate vector `∂/∂yᴹ`; `invJac A M`
is its inverse. -/
structure AffineCoordinateChange where
  jac : Matrix I I ℝ
  invJac : Matrix I I ℝ
  jac_mul_invJac : jac * invJac = 1
  invJac_mul_jac : invJac * jac = 1

namespace AffineCoordinateChange

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private theorem sum3_add (f g : I → I → I → ℝ) :
    (∑ A : I, ∑ B : I, ∑ D : I, (f A B D + g A B D)) =
      (∑ A : I, ∑ B : I, ∑ D : I, f A B D) +
        ∑ A : I, ∑ B : I, ∑ D : I, g A B D := by
  simp only [Finset.sum_add_distrib]

omit [DecidableEq I] in
private theorem sum3_sub (f g : I → I → I → ℝ) :
    (∑ A : I, ∑ B : I, ∑ D : I, (f A B D - g A B D)) =
      (∑ A : I, ∑ B : I, ∑ D : I, f A B D) -
        ∑ A : I, ∑ B : I, ∑ D : I, g A B D := by
  simp only [Finset.sum_sub_distrib]

omit [DecidableEq I] in
private theorem sum3_div (f : I → I → I → ℝ) (r : ℝ) :
    (∑ A : I, ∑ B : I, ∑ D : I, f A B D / r) =
      (∑ A : I, ∑ B : I, ∑ D : I, f A B D) / r := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

omit [DecidableEq I] in
private theorem sum1_div (f : I → ℝ) (r : ℝ) :
    (∑ A : I, f A) / r = ∑ A : I, f A / r := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

omit [DecidableEq I] in
private theorem sum6_swap12 (f : I → I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f b a c d e g :=
  Finset.sum_comm

omit [DecidableEq I] in
private theorem sum6_swap23 (f : I → I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a c b d e g := by
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum6_swap34 (f : I → I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b d c e g := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum6_swap45 (f : I → I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c e d g := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum6_swap56 (f : I → I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d g e := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum4_swap12 (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f b a c d :=
  Finset.sum_comm

omit [DecidableEq I] in
private theorem sum4_swap23 (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a c b d := by
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum4_swap34 (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, f a b d c := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum4_last_first_middle_swap
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ a, ∑ c, ∑ b, f a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm

omit [DecidableEq I] in
private theorem sum4_rotate_first_after_third
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

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
private theorem sum4_last_first
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
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
private theorem sum4_first_last
    (f : I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

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
private theorem sum5_last2_first
    (f : I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, f a b c d e := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, ∑ e, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, ∑ e, f a b c d e := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      exact sum4_last_first (fun a b c e => f a b c d e)

omit [DecidableEq I] in
private theorem sum5_first_last
    (f : I → I → I → I → I → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, ∑ e, f a b c d e := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, ∑ a, ∑ e, f a b c d e := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm

theorem jac_inv_contract (C : AffineCoordinateChange I) (M N : I) :
    (∑ A : I, C.jac M A * C.invJac A N) = if M = N then 1 else 0 := by
  have h := congrArg (fun G : Matrix I I ℝ => G M N) C.jac_mul_invJac
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem inv_jac_contract (C : AffineCoordinateChange I) (M N : I) :
    (∑ A : I, C.invJac M A * C.jac A N) = if M = N then 1 else 0 := by
  have h := congrArg (fun G : Matrix I I ℝ => G M N) C.invJac_mul_jac
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- Affine pullback of a covariant two-tensor. -/
noncomputable def transformCovariant2 (C : AffineCoordinateChange I)
    (T : I → I → ℝ) (M N : I) : ℝ :=
  ∑ A : I, ∑ B : I, C.jac M A * C.jac N B * T A B

/-- Affine transformation of a contravariant two-tensor. -/
noncomputable def transformContravariant2 (C : AffineCoordinateChange I)
    (T : I → I → ℝ) (M N : I) : ℝ :=
  ∑ A : I, ∑ B : I, C.invJac A M * C.invJac B N * T A B

/-- Affine pullback of a covariant rank-three array. -/
noncomputable def transformCovariant3 (C : AffineCoordinateChange I)
    (T : I → I → I → ℝ) (R M N : I) : ℝ :=
  ∑ A : I, ∑ B : I, ∑ D : I,
    C.jac R A * C.jac M B * C.jac N D * T A B D

/-- Affine pullback of a covariant rank-four array. -/
noncomputable def transformCovariant4 (C : AffineCoordinateChange I)
    (T : I → I → I → I → ℝ) (R S M N : I) : ℝ :=
  ∑ A : I, C.jac R A * C.transformCovariant3 (T A) S M N

/-- Affine transformation of a derivative of a contravariant two-tensor:
one covariant derivative slot and two contravariant tensor slots. -/
noncomputable def transformContravariant2Jet
    (C : AffineCoordinateChange I) (T : I → I → I → ℝ)
    (R M N : I) : ℝ :=
  ∑ A : I, C.jac R A * C.transformContravariant2 (T A) M N

/-- Affine transformation of an array with the index pattern of a
connection: one contravariant slot followed by two covariant slots. -/
noncomputable def transformConnection (C : AffineCoordinateChange I)
    (G : I → I → I → ℝ) (M N P : I) : ℝ :=
  ∑ A : I, ∑ B : I, ∑ D : I,
    C.invJac A M * C.jac N B * C.jac P D * G A B D

/-- Affine transformation of a differentiated connection: the derivative
slot is covariant, followed by the connection's `(1,2)` index pattern. -/
noncomputable def transformConnectionJet (C : AffineCoordinateChange I)
    (H : I → I → I → I → ℝ) (R M N P : I) : ℝ :=
  ∑ A : I, C.jac R A * C.transformConnection (H A) M N P

/-- Ricci contraction formed from a connection array and its coordinate
derivative.  Separating this algebraic contraction makes the covariance
argument independent of how the connection itself was constructed. -/
noncomputable def connectionRicci (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ) (N P : I) : ℝ :=
  (∑ M : I, H M M N P) - (∑ M : I, H N M M P) +
    (∑ Q : I, (∑ M : I, G M M Q) * G Q N P) -
    (∑ M : I, ∑ Q : I, G M N Q * G Q M P)

omit [DecidableEq I] in
private theorem coordinateChristoffelFirstKind_weightedSum
    (w : I → ℝ) (T : I → CoordinateMetricJet1 I) (Q N P : I) :
    coordinateChristoffelFirstKind
        (fun R M S => ∑ A : I, w A * T A R M S) Q N P =
      ∑ A : I, w A * coordinateChristoffelFirstKind (T A) Q N P := by
  unfold coordinateChristoffelFirstKind
  change ((∑ A : I, w A * T A N Q P) +
      (∑ A : I, w A * T A P Q N) -
      (∑ A : I, w A * T A Q N P)) / 2 = _
  calc
    _ = (∑ A : I, w A *
          (T A N Q P + T A P Q N - T A Q N P)) / 2 := by
      congr 1
      symm
      calc
        _ = ∑ A : I, (w A * T A N Q P + w A * T A P Q N -
            w A * T A Q N P) := by
          apply Finset.sum_congr rfl
          intro A _
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = ∑ A : I, (w A *
          (T A N Q P + T A P Q N - T A Q N P)) / 2 :=
      sum1_div _ 2
    _ = ∑ A : I, w A *
          ((T A N Q P + T A P Q N - T A Q N P) / 2) := by
        apply Finset.sum_congr rfl
        intro A _
        ring

/-- The first-kind Christoffel symbols transform covariantly under a
constant-Jacobian coordinate change. -/
theorem coordinateChristoffelFirstKind_transform
    (C : AffineCoordinateChange I) (dg : CoordinateMetricJet1 I)
    (Q N P : I) :
    coordinateChristoffelFirstKind (C.transformCovariant3 dg) Q N P =
      C.transformCovariant3 (coordinateChristoffelFirstKind dg) Q N P := by
  unfold coordinateChristoffelFirstKind transformCovariant3
  have h1 :
      (∑ A : I, ∑ B : I, ∑ D : I,
        C.jac N A * C.jac Q B * C.jac P D * dg A B D) =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.jac Q A * C.jac N B * C.jac P D * dg B A D := by
    calc
      _ = ∑ B : I, ∑ A : I, ∑ D : I,
          C.jac N A * C.jac Q B * C.jac P D * dg A B D :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring_nf
  have h2 :
      (∑ A : I, ∑ B : I, ∑ D : I,
        C.jac P A * C.jac Q B * C.jac N D * dg A B D) =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.jac Q A * C.jac N B * C.jac P D * dg D A B := by
    calc
      _ = ∑ B : I, ∑ A : I, ∑ D : I,
          C.jac P A * C.jac Q B * C.jac N D * dg A B D :=
        Finset.sum_comm
      _ = ∑ B : I, ∑ D : I, ∑ A : I,
          C.jac P A * C.jac Q B * C.jac N D * dg A B D := by
        apply Finset.sum_congr rfl
        intro B _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
  have h3 :
      (∑ A : I, ∑ B : I, ∑ D : I,
        C.jac Q A * C.jac N B * C.jac P D * dg A B D) =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.jac Q A * C.jac N B * C.jac P D * dg A B D := rfl
  have hexpand :
      (∑ A : I, ∑ B : I, ∑ D : I,
        C.jac Q A * C.jac N B * C.jac P D *
          ((dg B A D + dg D A B - dg A B D) / 2)) =
      ((∑ A : I, ∑ B : I, ∑ D : I,
          C.jac Q A * C.jac N B * C.jac P D * dg B A D) +
        (∑ A : I, ∑ B : I, ∑ D : I,
          C.jac Q A * C.jac N B * C.jac P D * dg D A B) -
        (∑ A : I, ∑ B : I, ∑ D : I,
          C.jac Q A * C.jac N B * C.jac P D * dg A B D)) / 2 := by
    calc
      _ = ∑ A : I, ∑ B : I, ∑ D : I,
          ((C.jac Q A * C.jac N B * C.jac P D * dg B A D +
            C.jac Q A * C.jac N B * C.jac P D * dg D A B -
            C.jac Q A * C.jac N B * C.jac P D * dg A B D) / 2) := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro D _
        ring
      _ = (∑ A : I, ∑ B : I, ∑ D : I,
          (C.jac Q A * C.jac N B * C.jac P D * dg B A D +
            C.jac Q A * C.jac N B * C.jac P D * dg D A B -
            C.jac Q A * C.jac N B * C.jac P D * dg A B D)) / 2 :=
        sum3_div _ 2
      _ = _ := by
        rw [sum3_sub, sum3_add]
  rw [h1, h2, h3]
  exact hexpand.symm

/-- The derivative of the first-kind symbols also transforms covariantly
under an affine coordinate change. -/
theorem coordinateChristoffelFirstKindJet_transform
    (C : AffineCoordinateChange I) (ddg : CoordinateMetricJet2 I)
    (R Q N P : I) :
    coordinateChristoffelFirstKindJet (C.transformCovariant4 ddg) R Q N P =
      C.transformCovariant4
        (fun A => coordinateChristoffelFirstKindJet ddg A) R Q N P := by
  unfold coordinateChristoffelFirstKindJet transformCovariant4
  change coordinateChristoffelFirstKind
      (fun S M T => ∑ A : I,
        C.jac R A * C.transformCovariant3 (ddg A) S M T) Q N P =
    ∑ A : I, C.jac R A *
      C.transformCovariant3 (coordinateChristoffelFirstKind (ddg A)) Q N P
  rw [coordinateChristoffelFirstKind_weightedSum]
  apply Finset.sum_congr rfl
  intro A _
  rw [C.coordinateChristoffelFirstKind_transform]

private theorem invJac_jac_contract_tensor (C : AffineCoordinateChange I)
    (T : I → I → ℝ) :
    (∑ Q : I, ∑ B : I, ∑ D : I,
      C.invJac B Q * C.jac Q D * T B D) = ∑ B : I, T B B := by
  calc
    _ = ∑ B : I, ∑ Q : I, ∑ D : I,
        C.invJac B Q * C.jac Q D * T B D := Finset.sum_comm
    _ = ∑ B : I, ∑ D : I, ∑ Q : I,
        C.invJac B Q * C.jac Q D * T B D := by
      apply Finset.sum_congr rfl
      intro B _
      exact Finset.sum_comm
    _ = ∑ B : I, ∑ D : I,
        (∑ Q : I, C.invJac B Q * C.jac Q D) * T B D := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.sum_mul]
    _ = ∑ B : I, ∑ D : I, (if B = D then 1 else 0) * T B D := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [C.inv_jac_contract]
    _ = _ := by simp

private theorem jac_inv_contract_tensor (C : AffineCoordinateChange I)
    (T : I → I → ℝ) :
    (∑ M : I, ∑ A : I, ∑ B : I,
      C.jac M A * C.invJac B M * T A B) = ∑ A : I, T A A := by
  calc
    _ = ∑ M : I, ∑ B : I, ∑ A : I,
        C.invJac B M * C.jac M A * T A B := by
      apply Finset.sum_congr rfl
      intro M _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = _ := invJac_jac_contract_tensor C (fun B A => T A B)

private theorem transformCovariant3_swap12
    (C : AffineCoordinateChange I) (T : I → I → I → ℝ)
    (R S N : I) :
    C.transformCovariant3 (fun A B D => T B A D) R S N =
      C.transformCovariant3 T S R N := by
  unfold transformCovariant3
  calc
    _ = ∑ B : I, ∑ A : I, ∑ D : I,
        C.jac R A * C.jac S B * C.jac N D * T B A D :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      ring

private theorem jac_contravariant_contraction
    (C : AffineCoordinateChange I) (u : I → ℝ) (V : I → I → ℝ)
    (N : I) :
    (∑ Y : I, (∑ D : I, C.jac Y D * u D) *
      C.transformContravariant2 V Y N) =
      ∑ D : I, ∑ F : I, u D * C.invJac F N * V D F := by
  simp only [transformContravariant2, Finset.sum_mul, Finset.mul_sum]
  ring_nf
  calc
    _ = ∑ F : I, ∑ Y : I, ∑ E : I, ∑ D : I,
        C.jac Y D * u D * C.invJac E Y * C.invJac F N * V E F :=
      sum4_third_first _
    _ = ∑ F : I, C.invJac F N *
          (∑ Y, ∑ E, ∑ D,
            C.invJac E Y * C.jac Y D * (u D * V E F)) := by
      apply Finset.sum_congr rfl
      intro F _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      apply Finset.sum_congr rfl
      intro E _
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ∑ F : I, C.invJac F N * ∑ E, u E * V E F := by
      apply Finset.sum_congr rfl
      intro F _
      rw [invJac_jac_contract_tensor C (fun E D => u D * V E F)]
    _ = ∑ F : I, ∑ E : I, u E * C.invJac F N * V E F := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := Finset.sum_comm

private theorem transformed_inverse_firstKind_contraction
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (G : I → I → I → ℝ) (M N P : I) :
    (∑ Q : I, C.transformContravariant2 gInv M Q *
      C.transformCovariant3 G Q N P) =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.invJac A M * C.jac N B * C.jac P D *
          (∑ Q : I, gInv A Q * G Q B D) := by
  simp only [transformContravariant2, transformCovariant3,
    Finset.sum_mul, Finset.mul_sum]
  ring_nf
  rw [sum6_swap45, sum6_swap34, sum6_swap23, sum6_swap12,
    sum6_swap34, sum6_swap23, sum6_swap45, sum6_swap34, sum6_swap56]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro D _
  have hcontract := invJac_jac_contract_tensor C
    (fun Q E => gInv A Q * G E B D)
  calc
    (∑ Q, ∑ E, ∑ F,
      C.invJac A M * C.invJac E Q * gInv A E * C.jac Q F *
        C.jac N B * C.jac P D * G F B D) =
        C.invJac A M * C.jac N B * C.jac P D *
          (∑ Q, ∑ E, ∑ F,
            C.invJac E Q * C.jac Q F * (gInv A E * G F B D)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      apply Finset.sum_congr rfl
      intro E _
      apply Finset.sum_congr rfl
      intro F _
      ring
    _ = C.invJac A M * C.jac N B * C.jac P D *
          (∑ E, gInv A E * G E B D) := by rw [hcontract]
    _ = ∑ E, C.invJac A M * C.jac N B * C.jac P D *
          gInv A E * G E B D := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring

/-- The Levi--Civita symbols obey the tensorial affine connection law; the
usual inhomogeneous term is absent because the Jacobian is constant. -/
theorem coordinateChristoffel_transform
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (M N P : I) :
    coordinateChristoffel (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) M N P =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.invJac A M * C.jac N B * C.jac P D *
          coordinateChristoffel gInv dg A B D := by
  unfold coordinateChristoffel
  calc
    _ = ∑ Q : I, C.transformContravariant2 gInv M Q *
          C.transformCovariant3 (coordinateChristoffelFirstKind dg) Q N P := by
        apply Finset.sum_congr rfl
        intro Q _
        rw [C.coordinateChristoffelFirstKind_transform]
    _ = _ := C.transformed_inverse_firstKind_contraction gInv
      (coordinateChristoffelFirstKind dg) M N P

theorem coordinateChristoffel_transformConnection
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (M N P : I) :
    coordinateChristoffel (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) M N P =
      C.transformConnection (coordinateChristoffel gInv dg) M N P := by
  exact C.coordinateChristoffel_transform gInv dg M N P

/-- The derivative of the inverse metric transforms with one covariant
derivative slot and two contravariant metric slots. -/
theorem coordinateInverseMetricJet_transform
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (R M N : I) :
    coordinateInverseMetricJet (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) R M N =
      ∑ A : I, ∑ B : I, ∑ D : I,
        C.jac R A * C.invJac B M * C.invJac D N *
          coordinateInverseMetricJet gInv dg A B D := by
  have hleft (Y : I) :
      (∑ X : I, C.transformContravariant2 gInv M X *
        C.transformCovariant3 dg R X Y) =
        ∑ B : I, ∑ A : I, ∑ D : I,
          C.invJac B M * C.jac R A * C.jac Y D *
            (∑ Q : I, gInv B Q * dg A Q D) := by
    calc
      _ = ∑ X : I, C.transformContravariant2 gInv M X *
          C.transformCovariant3 (fun Q A D => dg A Q D) X R Y := by
        apply Finset.sum_congr rfl
        intro X _
        rw [C.transformCovariant3_swap12]
      _ = _ := C.transformed_inverse_firstKind_contraction gInv
        (fun Q A D => dg A Q D) M R Y
  have hpos :
      (∑ X : I, ∑ Y : I,
        C.transformContravariant2 gInv M X *
          C.transformCovariant3 dg R X Y *
          C.transformContravariant2 gInv Y N) =
        ∑ A : I, ∑ B : I, ∑ D : I,
          C.jac R A * C.invJac B M * C.invJac D N *
            (∑ Q : I, ∑ E : I,
              gInv B Q * dg A Q E * gInv E D) := by
    calc
      _ = ∑ Y : I, ∑ X : I,
          C.transformContravariant2 gInv M X *
            C.transformCovariant3 dg R X Y *
            C.transformContravariant2 gInv Y N := Finset.sum_comm
      _ = ∑ Y : I, (∑ B : I, ∑ A : I, ∑ D : I,
          C.invJac B M * C.jac R A * C.jac Y D *
            (∑ Q : I, gInv B Q * dg A Q D)) *
              C.transformContravariant2 gInv Y N := by
        apply Finset.sum_congr rfl
        intro Y _
        calc
          _ = (∑ X : I, C.transformContravariant2 gInv M X *
              C.transformCovariant3 dg R X Y) *
                C.transformContravariant2 gInv Y N := by
            rw [Finset.sum_mul]
          _ = _ := by rw [hleft]
      _ = ∑ B : I, ∑ A : I, ∑ Y : I,
          (∑ D : I, C.jac Y D *
            (C.invJac B M * C.jac R A *
              (∑ Q : I, gInv B Q * dg A Q D))) *
                C.transformContravariant2 gInv Y N := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        ring_nf
        rw [sum4_rotate_first_after_third]
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro Y _
        apply Finset.sum_congr rfl
        intro D _
        ring_nf
      _ = ∑ B : I, ∑ A : I, ∑ D : I, ∑ E : I,
          (C.invJac B M * C.jac R A *
            (∑ Q : I, gInv B Q * dg A Q D)) *
              C.invJac E N * gInv D E := by
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro A _
        exact C.jac_contravariant_contraction
          (fun D => C.invJac B M * C.jac R A *
            (∑ Q : I, gInv B Q * dg A Q D)) gInv N
      _ = ∑ A : I, ∑ B : I, ∑ E : I, ∑ D : I,
          (C.invJac B M * C.jac R A *
            (∑ Q : I, gInv B Q * dg A Q D)) *
              C.invJac E N * gInv D E := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        apply Finset.sum_congr rfl
        intro E _
        calc
          _ = ∑ D : I, C.jac R A * C.invJac B M * C.invJac E N *
              (∑ Q : I, gInv B Q * dg A Q D * gInv D E) := by
            apply Finset.sum_congr rfl
            intro D _
            rw [← Finset.sum_mul]
            ring
          _ = C.jac R A * C.invJac B M * C.invJac E N *
              (∑ D : I, ∑ Q : I,
                gInv B Q * dg A Q D * gInv D E) := by
            rw [Finset.mul_sum]
          _ = C.jac R A * C.invJac B M * C.invJac E N *
              (∑ Q : I, ∑ D : I,
                gInv B Q * dg A Q D * gInv D E) := by
            rw [Finset.sum_comm]
  unfold coordinateInverseMetricJet
  rw [hpos]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro B _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro D _
  ring

theorem coordinateInverseMetricJet_transformContravariant2Jet
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (R M N : I) :
    coordinateInverseMetricJet (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) R M N =
      C.transformContravariant2Jet
        (coordinateInverseMetricJet gInv dg) R M N := by
  rw [C.coordinateInverseMetricJet_transform]
  unfold transformContravariant2Jet transformContravariant2
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro D _
  ring

private theorem transformed_contravariantJet_covariant3_contraction
    (C : AffineCoordinateChange I) (H G : I → I → I → ℝ)
    (R M N P : I) :
    (∑ Q : I, C.transformContravariant2Jet H R M Q *
      C.transformCovariant3 G Q N P) =
      C.transformConnectionJet
        (fun A B D E => ∑ Q : I, H A B Q * G Q D E) R M N P := by
  unfold transformContravariant2Jet
  calc
    _ = ∑ Q : I, ∑ A : I,
        C.jac R A * C.transformContravariant2 (H A) M Q *
          C.transformCovariant3 G Q N P := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [Finset.sum_mul]
    _ = ∑ A : I, ∑ Q : I,
        C.jac R A * C.transformContravariant2 (H A) M Q *
          C.transformCovariant3 G Q N P := Finset.sum_comm
    _ = ∑ A : I, C.jac R A *
        (∑ Q : I, C.transformContravariant2 (H A) M Q *
          C.transformCovariant3 G Q N P) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = ∑ A : I, C.jac R A * C.transformConnection
        (fun B D E => ∑ Q : I, H A B Q * G Q D E) M N P := by
      apply Finset.sum_congr rfl
      intro A _
      rw [C.transformed_inverse_firstKind_contraction]
      rfl
    _ = _ := rfl

private theorem transformed_contravariant2_covariant4_contraction
    (C : AffineCoordinateChange I) (V : I → I → ℝ)
    (K : I → I → I → I → ℝ) (R M N P : I) :
    (∑ Q : I, C.transformContravariant2 V M Q *
      C.transformCovariant4 K R Q N P) =
      C.transformConnectionJet
        (fun A B D E => ∑ Q : I, V B Q * K A Q D E) R M N P := by
  unfold transformCovariant4
  calc
    _ = ∑ Q : I, ∑ A : I,
        C.transformContravariant2 V M Q *
          (C.jac R A * C.transformCovariant3 (K A) Q N P) := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [Finset.mul_sum]
    _ = ∑ A : I, ∑ Q : I,
        C.jac R A * C.transformContravariant2 V M Q *
          C.transformCovariant3 (K A) Q N P := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = ∑ A : I, C.jac R A *
        (∑ Q : I, C.transformContravariant2 V M Q *
          C.transformCovariant3 (K A) Q N P) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = ∑ A : I, C.jac R A * C.transformConnection
        (fun B D E => ∑ Q : I, V B Q * K A Q D E) M N P := by
      apply Finset.sum_congr rfl
      intro A _
      rw [C.transformed_inverse_firstKind_contraction]
      rfl
    _ = _ := rfl

/-- Differentiated Levi--Civita symbols obey the affine differentiated
connection law.  This is where the inverse-metric derivative and the
second metric jet are combined by the product rule. -/
theorem coordinateChristoffelJet_transformConnectionJet
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (R M N P : I) :
    coordinateChristoffelJet (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) (C.transformCovariant4 ddg) R M N P =
      C.transformConnectionJet
        (coordinateChristoffelJet gInv dg ddg) R M N P := by
  unfold coordinateChristoffelJet
  calc
    _ = (∑ Q : I,
          coordinateInverseMetricJet (C.transformContravariant2 gInv)
              (C.transformCovariant3 dg) R M Q *
            coordinateChristoffelFirstKind (C.transformCovariant3 dg) Q N P) +
        ∑ Q : I, C.transformContravariant2 gInv M Q *
          coordinateChristoffelFirstKindJet (C.transformCovariant4 ddg)
            R Q N P := by
      rw [Finset.sum_add_distrib]
    _ = (∑ Q : I,
          C.transformContravariant2Jet
              (coordinateInverseMetricJet gInv dg) R M Q *
            C.transformCovariant3 (coordinateChristoffelFirstKind dg) Q N P) +
        ∑ Q : I, C.transformContravariant2 gInv M Q *
          C.transformCovariant4
            (fun A => coordinateChristoffelFirstKindJet ddg A) R Q N P := by
      congr 1
      · apply Finset.sum_congr rfl
        intro Q _
        rw [C.coordinateInverseMetricJet_transformContravariant2Jet]
        rw [C.coordinateChristoffelFirstKind_transform]
      · apply Finset.sum_congr rfl
        intro Q _
        rw [C.coordinateChristoffelFirstKindJet_transform]
    _ = C.transformConnectionJet
          (fun A B D E => ∑ Q : I,
            coordinateInverseMetricJet gInv dg A B Q *
              coordinateChristoffelFirstKind dg Q D E) R M N P +
        C.transformConnectionJet
          (fun A B D E => ∑ Q : I, gInv B Q *
            coordinateChristoffelFirstKindJet ddg A Q D E) R M N P := by
      rw [C.transformed_contravariantJet_covariant3_contraction]
      rw [C.transformed_contravariant2_covariant4_contraction]
    _ = C.transformConnectionJet
        (fun A B D E =>
          (∑ Q : I, coordinateInverseMetricJet gInv dg A B Q *
            coordinateChristoffelFirstKind dg Q D E) +
          ∑ Q : I, gInv B Q *
            coordinateChristoffelFirstKindJet ddg A Q D E) R M N P := by
      unfold transformConnectionJet transformConnection
      simp only [mul_add, Finset.sum_add_distrib]
    _ = _ := by
      change C.transformConnectionJet _ R M N P =
        C.transformConnectionJet
          (fun A B D E => ∑ Q : I,
            (coordinateInverseMetricJet gInv dg A B Q *
                coordinateChristoffelFirstKind dg Q D E +
              gInv B Q * coordinateChristoffelFirstKindJet ddg A Q D E))
          R M N P
      apply congrArg (fun H => C.transformConnectionJet H R M N P)
      funext A B D E
      rw [Finset.sum_add_distrib]

private theorem transformConnection_trace
    (C : AffineCoordinateChange I) (G : I → I → I → ℝ) (P : I) :
    (∑ M : I, C.transformConnection G M M P) =
      ∑ D : I, C.jac P D * ∑ A : I, G A A D := by
  unfold transformConnection
  calc
    _ = ∑ D : I, ∑ M : I, ∑ A : I, ∑ B : I,
        C.invJac A M * C.jac M B * C.jac P D * G A B D :=
      sum4_last_first _
    _ = ∑ D : I, C.jac P D *
        (∑ M : I, ∑ A : I, ∑ B : I,
          C.invJac A M * C.jac M B * G A B D) := by
      apply Finset.sum_congr rfl
      intro D _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      rw [invJac_jac_contract_tensor C (fun A B => G A B D)]

set_option maxHeartbeats 800000 in
private theorem transformConnectionJet_traceDerivativeUpper
    (C : AffineCoordinateChange I) (H : I → I → I → I → ℝ)
    (N P : I) :
    (∑ M : I, C.transformConnectionJet H M M N P) =
      C.transformCovariant2 (fun D E => ∑ A : I, H A A D E) N P := by
  unfold transformConnectionJet transformConnection transformCovariant2
  simp only [Finset.mul_sum]
  calc
    _ = ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I, ∑ E : I,
        C.jac M A * C.invJac B M * C.jac N D * C.jac P E *
          H A B D E := by
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = ∑ D : I, ∑ E : I, ∑ M : I, ∑ A : I, ∑ B : I,
        C.jac M A * C.invJac B M * C.jac N D * C.jac P E *
          H A B D E := sum5_last2_first _
    _ = ∑ D : I, ∑ E : I, C.jac N D * C.jac P E *
        (∑ M : I, ∑ A : I, ∑ B : I,
          C.jac M A * C.invJac B M * H A B D E) := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro E _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro E _
      rw [jac_inv_contract_tensor C (fun A B => H A B D E)]
      rw [Finset.mul_sum]

private theorem transformConnectionJet_traceLower
    (C : AffineCoordinateChange I) (H : I → I → I → I → ℝ)
    (N P : I) :
    (∑ M : I, C.transformConnectionJet H N M M P) =
      C.transformCovariant2 (fun A E => ∑ B : I, H A B B E) N P := by
  unfold transformConnectionJet
  calc
    _ = ∑ M : I, ∑ A : I,
        C.jac N A * C.transformConnection (H A) M M P := rfl
    _ = ∑ A : I, C.jac N A *
        (∑ M : I, C.transformConnection (H A) M M P) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
    _ = ∑ A : I, C.jac N A *
        (∑ E : I, C.jac P E * ∑ B : I, H A B B E) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [C.transformConnection_trace]
    _ = _ := by
      unfold transformCovariant2
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring

set_option maxHeartbeats 800000 in
private theorem transformCovector_connection_contract
    (C : AffineCoordinateChange I) (u : I → ℝ)
    (G : I → I → I → ℝ) (N P : I) :
    (∑ Q : I, (∑ A : I, C.jac Q A * u A) *
      C.transformConnection G Q N P) =
      C.transformCovariant2
        (fun B D => ∑ A : I, u A * G A B D) N P := by
  unfold transformConnection transformCovariant2
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ Q : I, ∑ E : I, ∑ B : I, ∑ D : I, ∑ A : I,
        C.jac Q A * u A * C.invJac E Q * C.jac N B *
          C.jac P D * G E B D := by
      apply Finset.sum_congr rfl
      intro Q _
      apply Finset.sum_congr rfl
      intro E _
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = ∑ Q : I, ∑ A : I, ∑ E : I, ∑ B : I, ∑ D : I,
        C.jac Q A * u A * C.invJac E Q * C.jac N B *
          C.jac P D * G E B D := by
      apply Finset.sum_congr rfl
      intro Q _
      exact sum4_last_first (fun E B D A =>
        C.jac Q A * u A * C.invJac E Q * C.jac N B *
          C.jac P D * G E B D)
    _ = ∑ B : I, ∑ D : I, ∑ Q : I, ∑ A : I, ∑ E : I,
        C.jac Q A * u A * C.invJac E Q * C.jac N B *
          C.jac P D * G E B D := sum5_last2_first _
    _ = ∑ B : I, ∑ D : I, C.jac N B * C.jac P D *
        (∑ Q : I, ∑ A : I, ∑ E : I,
          C.jac Q A * C.invJac E Q * (u A * G E B D)) := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [jac_inv_contract_tensor C (fun A E => u A * G E B D)]
      rw [Finset.mul_sum]

private theorem transformConnection_traceProduct
    (C : AffineCoordinateChange I) (G : I → I → I → ℝ) (N P : I) :
    (∑ Q : I, (∑ M : I, C.transformConnection G M M Q) *
      C.transformConnection G Q N P) =
      C.transformCovariant2
        (fun B D => ∑ Q : I, (∑ M : I, G M M Q) * G Q B D) N P := by
  calc
    _ = ∑ Q : I, (∑ A : I, C.jac Q A * ∑ M : I, G M M A) *
        C.transformConnection G Q N P := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [C.transformConnection_trace]
    _ = _ := C.transformCovector_connection_contract
      (fun A => ∑ M : I, G M M A) G N P

private theorem jac_connection_upper_contract
    (C : AffineCoordinateChange I) (G : I → I → I → ℝ)
    (D N P : I) :
    (∑ Q : I, C.jac Q D * C.transformConnection G Q N P) =
      C.transformCovariant2 (G D) N P := by
  have h := C.transformCovector_connection_contract
    (fun A : I => if A = D then 1 else 0) G N P
  simpa using h

set_option maxHeartbeats 800000 in
private theorem transformContravector_covariant2_contract
    (C : AffineCoordinateChange I) (u : I → ℝ)
    (V : I → I → ℝ) (P : I) :
    (∑ M : I, (∑ A : I, C.invJac A M * u A) *
      C.transformCovariant2 V M P) =
      ∑ D : I, ∑ A : I, u A * C.jac P D * V A D := by
  unfold transformCovariant2
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ M : I, ∑ B : I, ∑ D : I, ∑ A : I,
        C.invJac A M * u A * C.jac M B * C.jac P D * V B D := by
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro A _
      ring

    _ = ∑ D : I, ∑ M : I, ∑ B : I, ∑ A : I,
        C.invJac A M * u A * C.jac M B * C.jac P D * V B D :=
      sum4_third_first _
    _ = ∑ D : I, ∑ M : I, ∑ A : I, ∑ B : I,
        C.invJac A M * u A * C.jac M B * C.jac P D * V B D := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro M _
      exact Finset.sum_comm
    _ = ∑ D : I, C.jac P D *
        (∑ M : I, ∑ A : I, ∑ B : I,
          C.jac M B * C.invJac A M * (u A * V B D)) := by
      apply Finset.sum_congr rfl
      intro D _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      ring
    _ = ∑ D : I, C.jac P D * ∑ A : I, u A * V A D := by
      apply Finset.sum_congr rfl
      intro D _
      congr 1
      calc
        _ = ∑ M : I, ∑ B : I, ∑ A : I,
            C.jac M B * C.invJac A M * (u A * V B D) := by
          apply Finset.sum_congr rfl
          intro M _
          exact Finset.sum_comm
        _ = _ := jac_inv_contract_tensor C
          (fun B A => u A * V B D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring

set_option maxHeartbeats 1000000 in
private theorem transformConnection_crossProduct
    (C : AffineCoordinateChange I) (G : I → I → I → ℝ) (N P : I) :
    (∑ M : I, ∑ Q : I, C.transformConnection G M N Q *
      C.transformConnection G Q M P) =
      C.transformCovariant2
        (fun B E => ∑ A : I, ∑ D : I, G A B D * G D A E) N P := by
  let G' := C.transformConnection G
  have hG (M' N' P' : I) :
      G' M' N' P' = ∑ A : I, ∑ B : I, ∑ D : I,
        C.invJac A M' * C.jac N' B * C.jac P' D * G A B D := rfl
  change (∑ M : I, ∑ Q : I, G' M N Q * G' Q M P) = _
  calc
    _ = ∑ M : I, ∑ Q : I,
        (∑ A : I, ∑ B : I, ∑ D : I,
          C.invJac A M * C.jac N B * C.jac Q D * G A B D) *
            G' Q M P := by
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro Q _
      rw [hG M N Q]
    _ = ∑ M : I, ∑ Q : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.invJac A M * C.jac N B * C.jac Q D * G A B D *
          G' Q M P := by
      simp only [Finset.sum_mul]
    _ = ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I, ∑ Q : I,
        C.invJac A M * C.jac N B * C.jac Q D * G A B D *
          G' Q M P := by
      apply Finset.sum_congr rfl
      intro M _
      exact sum4_first_last _
    _ = ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.invJac A M * C.jac N B * G A B D *
          (∑ Q : I, C.jac Q D * G' Q M P) := by
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      ring
    _ = ∑ M : I, ∑ A : I, ∑ B : I, ∑ D : I,
        C.invJac A M * C.jac N B * G A B D *
          C.transformCovariant2 (G D) M P := by
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [show (∑ Q : I, C.jac Q D * G' Q M P) =
        C.transformCovariant2 (G D) M P by
          exact C.jac_connection_upper_contract G D M P]
    _ = ∑ B : I, ∑ D : I, ∑ M : I, ∑ A : I,
        C.invJac A M * C.jac N B * G A B D *
          C.transformCovariant2 (G D) M P := sum4_last2_first _
    _ = ∑ B : I, ∑ D : I, C.jac N B *
        (∑ M : I, (∑ A : I, C.invJac A M * G A B D) *
          C.transformCovariant2 (G D) M P) := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = ∑ B : I, ∑ D : I, C.jac N B *
        (∑ E : I, ∑ A : I, G A B D * C.jac P E * G D A E) := by
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro D _
      rw [C.transformContravector_covariant2_contract
        (fun A => G A B D) (G D) P]
    _ = ∑ B : I, ∑ E : I, ∑ A : I, ∑ D : I,
        C.jac N B * (G A B D * C.jac P E * G D A E) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [Finset.mul_sum]
      exact sum3_first_last _
    _ = _ := by
      unfold transformCovariant2
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      apply Finset.sum_congr rfl
      intro E _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro D _
      ring

/-- The Ricci contraction of an affinely transformed connection and
differentiated connection is a covariant two-tensor. -/
theorem connectionRicci_transform
    (C : AffineCoordinateChange I) (G : I → I → I → ℝ)
    (H : I → I → I → I → ℝ) (N P : I) :
    connectionRicci (C.transformConnection G)
        (C.transformConnectionJet H) N P =
      C.transformCovariant2 (connectionRicci G H) N P := by
  unfold connectionRicci
  rw [C.transformConnectionJet_traceDerivativeUpper]
  rw [C.transformConnectionJet_traceLower]
  rw [C.transformConnection_traceProduct]
  rw [C.transformConnection_crossProduct]
  unfold transformCovariant2
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]

omit [DecidableEq I] in
theorem coordinateRicci_eq_connectionRicci
    (gInv : I → I → ℝ) (dg : CoordinateMetricJet1 I)
    (ddg : CoordinateMetricJet2 I) (N P : I) :
    coordinateRicci gInv dg ddg N P =
      connectionRicci (coordinateChristoffel gInv dg)
        (coordinateChristoffelJet gInv dg ddg) N P := rfl

/-- **Affine coordinate covariance of coordinate Ricci curvature.** For an
arbitrary invertible constant Jacobian, transforming the inverse metric and
the first and second covariant metric jets and then recomputing Ricci agrees
with the covariant pullback of the original Ricci array. -/
theorem coordinateRicci_transform
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I)
    (N P : I) :
    coordinateRicci (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) (C.transformCovariant4 ddg) N P =
      C.transformCovariant2 (coordinateRicci gInv dg ddg) N P := by
  rw [coordinateRicci_eq_connectionRicci]
  change connectionRicci _ _ N P =
    C.transformCovariant2
      (connectionRicci (coordinateChristoffel gInv dg)
        (coordinateChristoffelJet gInv dg ddg)) N P
  have hG :
      coordinateChristoffel (C.transformContravariant2 gInv)
          (C.transformCovariant3 dg) =
        C.transformConnection (coordinateChristoffel gInv dg) := by
    funext M N' P'
    exact C.coordinateChristoffel_transformConnection gInv dg M N' P'
  have hH :
      coordinateChristoffelJet (C.transformContravariant2 gInv)
          (C.transformCovariant3 dg) (C.transformCovariant4 ddg) =
        C.transformConnectionJet
          (coordinateChristoffelJet gInv dg ddg) := by
    funext R M N' P'
    exact C.coordinateChristoffelJet_transformConnectionJet
      gInv dg ddg R M N' P'
  rw [hG, hH]
  exact C.connectionRicci_transform
    (coordinateChristoffel gInv dg)
    (coordinateChristoffelJet gInv dg ddg) N P

theorem transformCovariant2_recover
    (C : AffineCoordinateChange I) (T : I → I → ℝ) (A B : I) :
    (∑ M : I, ∑ N : I, C.invJac A M * C.invJac B N *
      C.transformCovariant2 T M N) = T A B := by
  have hleft (N : I) :
      (∑ M : I, C.invJac A M * C.transformCovariant2 T M N) =
        ∑ D : I, C.jac N D * T A D := by
    have h := C.transformContravector_covariant2_contract
      (fun X : I => if X = A then 1 else 0) T N
    simpa using h
  calc
    _ = ∑ N : I, ∑ M : I, C.invJac A M * C.invJac B N *
        C.transformCovariant2 T M N := Finset.sum_comm
    _ = ∑ N : I, C.invJac B N *
        (∑ M : I, C.invJac A M * C.transformCovariant2 T M N) := by
      apply Finset.sum_congr rfl
      intro N _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _ = ∑ N : I, C.invJac B N *
        (∑ D : I, C.jac N D * T A D) := by
      apply Finset.sum_congr rfl
      intro N _
      rw [hleft]
    _ = ∑ N : I, ∑ D : I,
        C.invJac B N * C.jac N D * T A D := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      apply Finset.sum_congr rfl
      intro D _
      ring
    _ = ∑ D : I, ∑ N : I,
        C.invJac B N * C.jac N D * T A D := Finset.sum_comm
    _ = ∑ D : I, (∑ N : I, C.invJac B N * C.jac N D) * T A D := by
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.sum_mul]
    _ = ∑ D : I, (if B = D then 1 else 0) * T A D := by
      apply Finset.sum_congr rfl
      intro D _
      rw [C.inv_jac_contract]
    _ = _ := by simp

theorem transformCovariant2_zero_iff
    (C : AffineCoordinateChange I) (T : I → I → ℝ) :
    (∀ M N, C.transformCovariant2 T M N = 0) ↔
      ∀ A B, T A B = 0 := by
  constructor
  · intro h A B
    calc
      T A B = ∑ M : I, ∑ N : I,
          C.invJac A M * C.invJac B N *
            C.transformCovariant2 T M N :=
        (C.transformCovariant2_recover T A B).symm
      _ = 0 := by simp [h]
  · intro h M N
    unfold transformCovariant2
    simp [h]

/-- Affine changes preserve and reflect coordinate Ricci-flatness. -/
theorem coordinateRicciFlat_transform_iff
    (C : AffineCoordinateChange I) (gInv : I → I → ℝ)
    (dg : CoordinateMetricJet1 I) (ddg : CoordinateMetricJet2 I) :
    (∀ N P, coordinateRicci (C.transformContravariant2 gInv)
        (C.transformCovariant3 dg) (C.transformCovariant4 ddg) N P = 0) ↔
      ∀ N P, coordinateRicci gInv dg ddg N P = 0 := by
  have hzero := C.transformCovariant2_zero_iff
    (coordinateRicci gInv dg ddg)
  constructor
  · intro h
    apply hzero.mp
    intro N P
    rw [← C.coordinateRicci_transform]
    exact h N P
  · intro h N P
    rw [C.coordinateRicci_transform]
    exact hzero.mpr h N P

end AffineCoordinateChange

end AffineChange

end RainichKaluza
