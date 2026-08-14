import RainichKaluza.MetricFourJetFactorization
import RainichKaluza.CoordinateRicciFirstJet

/-!
# Actual first derivative of coordinate Ricci

This file proves a fixed-coordinate chain rule for the Ricci contraction.
It differentiates the inverse-metric, Christoffel, and Ricci formulas from
their genuine component fields and identifies the result with the stored
algebraic `coordinateRicciFirstJet` expression.
-/

namespace RainichKaluza

open scoped Matrix Topology ContDiff

private theorem scalarFieldCoordinateFDeriv_add
    (f g : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y + g y) z r =
      scalarFieldCoordinateFDeriv f z r + scalarFieldCoordinateFDeriv g z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f + g) z) _ = _
  rw [fderiv_add hf hg]
  rfl

private theorem scalarFieldCoordinateFDeriv_sub
    (f g : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y - g y) z r =
      scalarFieldCoordinateFDeriv f z r - scalarFieldCoordinateFDeriv g z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f - g) z) _ = _
  rw [fderiv_sub hf hg]
  rfl

private theorem scalarFieldCoordinateFDeriv_mul
    (f g : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    scalarFieldCoordinateFDeriv (fun y ↦ f y * g y) z r =
      scalarFieldCoordinateFDeriv f z r * g z +
        f z * scalarFieldCoordinateFDeriv g z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (f * g) z) _ = _
  rw [fderiv_mul hf hg]
  simp
  ring

private theorem scalarFieldCoordinateFDeriv_neg
    (f : CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4) :
    scalarFieldCoordinateFDeriv (fun y ↦ -f y) z r =
      -scalarFieldCoordinateFDeriv f z r := by
  unfold scalarFieldCoordinateFDeriv
  change (fderiv ℝ (-f) z) _ = _
  rw [fderiv_neg]
  rfl

private theorem scalarFieldCoordinateFDeriv_sum
    {I : Type*} [Fintype I]
    (f : I → CurvatureCoordinateSpace4 → ℝ)
    (z : CurvatureCoordinateSpace4) (r : Fin 4)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    scalarFieldCoordinateFDeriv (fun y ↦ ∑ i, f i y) z r =
      ∑ i, scalarFieldCoordinateFDeriv (f i) z r := by
  unfold scalarFieldCoordinateFDeriv
  rw [show (fun y ↦ ∑ i, f i y) = ∑ i, f i by
    funext y; simp]
  rw [fderiv_sum]
  simp
  exact fun i _ ↦ hf i

private theorem coordinateChristoffelFirstKind_actual_derivative
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (z : CurvatureCoordinateSpace4) (r Q N P : Fin 4)
    (hdg : ∀ R M N, DifferentiableAt ℝ (fun y ↦ dg y R M N) z)
    (hjet : ∀ R M N,
      scalarFieldCoordinateFDeriv (fun y ↦ dg y R M N) z r =
        ddg z r R M N) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) z r =
      coordinateChristoffelFirstKindJet (ddg z) r Q N P := by
  unfold coordinateChristoffelFirstKind coordinateChristoffelFirstKindJet
  change scalarFieldCoordinateFDeriv
      (fun y ↦ (dg y N Q P + dg y P Q N - dg y Q N P) / 2) z r = _
  rw [show (fun y ↦ (dg y N Q P + dg y P Q N - dg y Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((dg y N Q P + dg y P Q N) - dg y Q N P) by
    funext y; ring]
  rw [scalarFieldCoordinateFDeriv_mul,
    scalarFieldCoordinateFDeriv_sub,
    scalarFieldCoordinateFDeriv_add]
  have h1 := hjet N Q P
  have h2 := hjet P Q N
  have h3 := hjet Q N P
  unfold scalarFieldCoordinateFDeriv at h1 h2 h3
  simp [scalarFieldCoordinateFDeriv]
  rw [h1, h2, h3]
  ring
  all_goals fun_prop

private theorem coordinateInverseMetricJet_actual_derivative
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (z : CurvatureCoordinateSpace4) (r S M N : Fin 4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (hgiJet : ∀ A B,
      scalarFieldCoordinateFDeriv (fun y ↦ gInv y A B) z r =
        coordinateInverseMetricJet (gInv z) (dg z) r A B)
    (hdgJet : ∀ R A B,
      scalarFieldCoordinateFDeriv (fun y ↦ dg y R A B) z r =
        ddg z r R A B) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) S M N) z r =
      coordinateInverseMetricJetFirstJet
        (gInv z) (dg z) (ddg z) r S M N := by
  unfold coordinateInverseMetricJet coordinateInverseMetricJetFirstJet
  rw [show (fun y ↦ -∑ A, ∑ B,
      gInv y M A * dg y S A B * gInv y B N) =
      fun y ↦ -(∑ A, ∑ B,
        (gInv y M A * dg y S A B) * gInv y B N) by rfl]
  rw [scalarFieldCoordinateFDeriv_neg,
    scalarFieldCoordinateFDeriv_sum]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro A _
  rw [scalarFieldCoordinateFDeriv_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [scalarFieldCoordinateFDeriv_mul,
    scalarFieldCoordinateFDeriv_mul,
    hgiJet, hdgJet, hgiJet]
  ring
  all_goals fun_prop

private theorem coordinateChristoffel_actual_derivative
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (z : CurvatureCoordinateSpace4) (r M N P : Fin 4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (hgiJet : ∀ A B,
      scalarFieldCoordinateFDeriv (fun y ↦ gInv y A B) z r =
        coordinateInverseMetricJet (gInv z) (dg z) r A B)
    (hdgJet : ∀ R A B,
      scalarFieldCoordinateFDeriv (fun y ↦ dg y R A B) z r =
        ddg z r R A B) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateChristoffel (gInv y) (dg y) M N P) z r =
      coordinateChristoffelJet
        (gInv z) (dg z) (ddg z) r M N P := by
  have hfirstKind (Q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) z := by
    unfold coordinateChristoffelFirstKind
    rw [show (fun y ↦
        (dg y N Q P + dg y P Q N - dg y Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((dg y N Q P + dg y P Q N) - dg y Q N P) by
      funext y; ring]
    exact (((hdg N Q P).add (hdg P Q N)).sub
      (hdg Q N P)).const_mul (1 / 2 : ℝ)
  unfold coordinateChristoffel coordinateChristoffelJet
  rw [scalarFieldCoordinateFDeriv_sum
    (fun Q y ↦ gInv y M Q *
      coordinateChristoffelFirstKind (dg y) Q N P) z r
    (fun Q ↦ (hgi M Q).mul (hfirstKind Q))]
  apply Finset.sum_congr rfl
  intro Q _
  rw [scalarFieldCoordinateFDeriv_mul _ _ z r
      (hgi M Q) (hfirstKind Q), hgiJet,
    coordinateChristoffelFirstKind_actual_derivative
      dg ddg z r Q N P hdg hdgJet]

private theorem coordinateChristoffelFirstKindJet_actual_derivative
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (dddg : CoordinateMetricJet3 (Fin 4))
    (z : CurvatureCoordinateSpace4) (r S Q N P : Fin 4)
    (hddg : ∀ R T A B, DifferentiableAt ℝ
      (fun y ↦ ddg y R T A B) z)
    (hddgJet : ∀ R T A B,
      scalarFieldCoordinateFDeriv (fun y ↦ ddg y R T A B) z r =
        dddg r R T A B) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateChristoffelFirstKindJet
          (ddg y) S Q N P) z r =
      coordinateChristoffelFirstKindJetFirstJet
        dddg r S Q N P := by
  unfold coordinateChristoffelFirstKindJet
    coordinateChristoffelFirstKindJetFirstJet
  change scalarFieldCoordinateFDeriv
      (fun y ↦ (ddg y S N Q P + ddg y S P Q N -
        ddg y S Q N P) / 2) z r = _
  rw [show (fun y ↦ (ddg y S N Q P + ddg y S P Q N -
      ddg y S Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((ddg y S N Q P + ddg y S P Q N) - ddg y S Q N P) by
    funext y; ring]
  rw [scalarFieldCoordinateFDeriv_mul,
    scalarFieldCoordinateFDeriv_sub,
    scalarFieldCoordinateFDeriv_add]
  have h1 := hddgJet S N Q P
  have h2 := hddgJet S P Q N
  have h3 := hddgJet S Q N P
  unfold scalarFieldCoordinateFDeriv at h1 h2 h3
  simp [scalarFieldCoordinateFDeriv]
  rw [h1, h2, h3]
  ring
  all_goals fun_prop

theorem coordinateChristoffelJet_actual_derivative
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (dddg : CoordinateMetricJet3 (Fin 4))
    (z : CurvatureCoordinateSpace4) (r S M N P : Fin 4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (hddg : ∀ R T A B, DifferentiableAt ℝ
      (fun y ↦ ddg y R T A B) z)
    (hgiJet : ∀ A B,
      scalarFieldCoordinateFDeriv (fun y ↦ gInv y A B) z r =
        coordinateInverseMetricJet (gInv z) (dg z) r A B)
    (hdgJet : ∀ R A B,
      scalarFieldCoordinateFDeriv (fun y ↦ dg y R A B) z r =
        ddg z r R A B)
    (hddgJet : ∀ R T A B,
      scalarFieldCoordinateFDeriv (fun y ↦ ddg y R T A B) z r =
        dddg r R T A B) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateChristoffelJet
          (gInv y) (dg y) (ddg y) S M N P) z r =
      coordinateChristoffelJetFirstJet
        (gInv z) (dg z) (ddg z) dddg r S M N P := by
  have hfirstKind (Q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) z := by
    unfold coordinateChristoffelFirstKind
    rw [show (fun y ↦
        (dg y N Q P + dg y P Q N - dg y Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((dg y N Q P + dg y P Q N) - dg y Q N P) by
      funext y; ring]
    exact (((hdg N Q P).add (hdg P Q N)).sub
      (hdg Q N P)).const_mul (1 / 2 : ℝ)
  have hfirstKindJet (Q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKindJet
        (ddg y) S Q N P) z := by
    unfold coordinateChristoffelFirstKindJet
    rw [show (fun y ↦
        (ddg y S N Q P + ddg y S P Q N - ddg y S Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((ddg y S N Q P + ddg y S P Q N) - ddg y S Q N P) by
      funext y; ring]
    exact (((hddg S N Q P).add (hddg S P Q N)).sub
      (hddg S Q N P)).const_mul (1 / 2 : ℝ)
  have hinverseJet (Q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateInverseMetricJet
        (gInv y) (dg y) S M Q) z := by
    unfold coordinateInverseMetricJet
    fun_prop
  unfold coordinateChristoffelJet coordinateChristoffelJetFirstJet
  rw [scalarFieldCoordinateFDeriv_sum
    (fun Q y ↦
      coordinateInverseMetricJet (gInv y) (dg y) S M Q *
          coordinateChristoffelFirstKind (dg y) Q N P +
        gInv y M Q *
          coordinateChristoffelFirstKindJet (ddg y) S Q N P) z r
    (fun Q ↦
      (hinverseJet Q).mul (hfirstKind Q) |>.add
        ((hgi M Q).mul (hfirstKindJet Q)))]
  apply Finset.sum_congr rfl
  intro Q _
  rw [show (fun y ↦
      coordinateInverseMetricJet (gInv y) (dg y) S M Q *
          coordinateChristoffelFirstKind (dg y) Q N P +
        gInv y M Q *
          coordinateChristoffelFirstKindJet (ddg y) S Q N P) =
      (fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) S M Q) *
          (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) +
        (fun y ↦ gInv y M Q) *
          (fun y ↦ coordinateChristoffelFirstKindJet
            (ddg y) S Q N P) by rfl]
  rw [show scalarFieldCoordinateFDeriv
      (((fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) S M Q) *
          (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P)) +
        ((fun y ↦ gInv y M Q) *
          (fun y ↦ coordinateChristoffelFirstKindJet
            (ddg y) S Q N P))) z r =
      scalarFieldCoordinateFDeriv
        ((fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) S M Q) *
          (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P)) z r +
        scalarFieldCoordinateFDeriv
          ((fun y ↦ gInv y M Q) *
            (fun y ↦ coordinateChristoffelFirstKindJet
              (ddg y) S Q N P)) z r by
      exact scalarFieldCoordinateFDeriv_add _ _ z r
        ((hinverseJet Q).mul (hfirstKind Q))
        ((hgi M Q).mul (hfirstKindJet Q))]
  rw [show scalarFieldCoordinateFDeriv
      ((fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) S M Q) *
        (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P)) z r =
      scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateInverseMetricJet (gInv y) (dg y) S M Q) z r *
        coordinateChristoffelFirstKind (dg z) Q N P +
      coordinateInverseMetricJet (gInv z) (dg z) S M Q *
        scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) z r by
      exact scalarFieldCoordinateFDeriv_mul _ _ z r
        (hinverseJet Q) (hfirstKind Q)]
  rw [show scalarFieldCoordinateFDeriv
      ((fun y ↦ gInv y M Q) *
        (fun y ↦ coordinateChristoffelFirstKindJet
          (ddg y) S Q N P)) z r =
      scalarFieldCoordinateFDeriv (fun y ↦ gInv y M Q) z r *
          coordinateChristoffelFirstKindJet (ddg z) S Q N P +
        gInv z M Q * scalarFieldCoordinateFDeriv
          (fun y ↦ coordinateChristoffelFirstKindJet
            (ddg y) S Q N P) z r by
      exact scalarFieldCoordinateFDeriv_mul _ _ z r
        (hgi M Q) (hfirstKindJet Q)]
  rw [
    coordinateInverseMetricJet_actual_derivative
      gInv dg ddg z r S M Q hgi hdg hgiJet hdgJet,
    coordinateChristoffelFirstKind_actual_derivative
      dg ddg z r Q N P hdg hdgJet,
    hgiJet,
    coordinateChristoffelFirstKindJet_actual_derivative
      ddg dddg z r S Q N P hddg hddgJet]
  ring

end RainichKaluza

namespace RainichKaluza

theorem coordinateRicci_actual_derivative
    (gInv : CurvatureCoordinateSpace4 → Matrix4)
    (dg : CurvatureCoordinateSpace4 → CoordinateMetricJet1 (Fin 4))
    (ddg : CurvatureCoordinateSpace4 → CoordinateMetricJet2 (Fin 4))
    (dddg : CoordinateMetricJet3 (Fin 4))
    (z : CurvatureCoordinateSpace4) (r N P : Fin 4)
    (hgi : ∀ A B, DifferentiableAt ℝ (fun y ↦ gInv y A B) z)
    (hdg : ∀ R A B, DifferentiableAt ℝ (fun y ↦ dg y R A B) z)
    (hddg : ∀ R T A B, DifferentiableAt ℝ
      (fun y ↦ ddg y R T A B) z)
    (hgiJet : ∀ A B,
      scalarFieldCoordinateFDeriv (fun y ↦ gInv y A B) z r =
        coordinateInverseMetricJet (gInv z) (dg z) r A B)
    (hdgJet : ∀ R A B,
      scalarFieldCoordinateFDeriv (fun y ↦ dg y R A B) z r =
        ddg z r R A B)
    (hddgJet : ∀ R T A B,
      scalarFieldCoordinateFDeriv (fun y ↦ ddg y R T A B) z r =
        dddg r R T A B) :
    scalarFieldCoordinateFDeriv
        (fun y ↦ coordinateRicci (gInv y) (dg y) (ddg y) N P) z r =
      coordinateRicciFirstJet
        (gInv z) (dg z) (ddg z) dddg r N P := by
  have hfirstKind (Q N P : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKind (dg y) Q N P) z := by
    unfold coordinateChristoffelFirstKind
    rw [show (fun y ↦
        (dg y N Q P + dg y P Q N - dg y Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((dg y N Q P + dg y P Q N) - dg y Q N P) by
      funext y; ring]
    exact (((hdg N Q P).add (hdg P Q N)).sub
      (hdg Q N P)).const_mul (1 / 2 : ℝ)
  have hfirstKindJet (S Q N P : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelFirstKindJet
        (ddg y) S Q N P) z := by
    unfold coordinateChristoffelFirstKindJet
    rw [show (fun y ↦
        (ddg y S N Q P + ddg y S P Q N - ddg y S Q N P) / 2) =
      fun y ↦ (1 / 2 : ℝ) *
        ((ddg y S N Q P + ddg y S P Q N) - ddg y S Q N P) by
      funext y; ring]
    exact (((hddg S N Q P).add (hddg S P Q N)).sub
      (hddg S Q N P)).const_mul (1 / 2 : ℝ)
  have hinverseJet (S M Q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateInverseMetricJet
        (gInv y) (dg y) S M Q) z := by
    unfold coordinateInverseMetricJet
    fun_prop
  have hchristoffel (M N P : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffel (gInv y) (dg y) M N P) z := by
    unfold coordinateChristoffel
    fun_prop
  have hchristoffelJet (S M N P : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ coordinateChristoffelJet
        (gInv y) (dg y) (ddg y) S M N P) z := by
    unfold coordinateChristoffelJet
    fun_prop
  let T1 : CurvatureCoordinateSpace4 → ℝ := fun y ↦
    ∑ M, coordinateChristoffelJet
      (gInv y) (dg y) (ddg y) M M N P
  let T2 : CurvatureCoordinateSpace4 → ℝ := fun y ↦
    ∑ M, coordinateChristoffelJet
      (gInv y) (dg y) (ddg y) N M M P
  let T3 : CurvatureCoordinateSpace4 → ℝ := fun y ↦
    ∑ Q, (∑ M, coordinateChristoffel (gInv y) (dg y) M M Q) *
      coordinateChristoffel (gInv y) (dg y) Q N P
  let T4 : CurvatureCoordinateSpace4 → ℝ := fun y ↦
    ∑ M, ∑ Q, coordinateChristoffel (gInv y) (dg y) M N Q *
      coordinateChristoffel (gInv y) (dg y) Q M P
  have hT1diff : DifferentiableAt ℝ T1 z := by
    dsimp [T1]
    fun_prop
  have hT2diff : DifferentiableAt ℝ T2 z := by
    dsimp [T2]
    fun_prop
  have htraceDiff (Q : Fin 4) : DifferentiableAt ℝ
      (fun y ↦ ∑ M, coordinateChristoffel (gInv y) (dg y) M M Q) z := by
    fun_prop
  have hT3diff : DifferentiableAt ℝ T3 z := by
    dsimp [T3]
    fun_prop
  have hT4diff : DifferentiableAt ℝ T4 z := by
    dsimp [T4]
    fun_prop
  have hT1 : scalarFieldCoordinateFDeriv T1 z r =
      ∑ M, coordinateChristoffelJetFirstJet
        (gInv z) (dg z) (ddg z) dddg r M M N P := by
    dsimp [T1]
    rw [scalarFieldCoordinateFDeriv_sum]
    apply Finset.sum_congr rfl
    intro M _
    exact coordinateChristoffelJet_actual_derivative
      gInv dg ddg dddg z r M M N P hgi hdg hddg
      hgiJet hdgJet hddgJet
    intro M
    exact hchristoffelJet M M N P
  have hT2 : scalarFieldCoordinateFDeriv T2 z r =
      ∑ M, coordinateChristoffelJetFirstJet
        (gInv z) (dg z) (ddg z) dddg r N M M P := by
    dsimp [T2]
    rw [scalarFieldCoordinateFDeriv_sum]
    apply Finset.sum_congr rfl
    intro M _
    exact coordinateChristoffelJet_actual_derivative
      gInv dg ddg dddg z r N M M P hgi hdg hddg
      hgiJet hdgJet hddgJet
    intro M
    exact hchristoffelJet N M M P
  have htrace (Q : Fin 4) :
      scalarFieldCoordinateFDeriv
          (fun y ↦ ∑ M, coordinateChristoffel
            (gInv y) (dg y) M M Q) z r =
        ∑ M, coordinateChristoffelJet
          (gInv z) (dg z) (ddg z) r M M Q := by
    rw [scalarFieldCoordinateFDeriv_sum]
    apply Finset.sum_congr rfl
    intro M _
    exact coordinateChristoffel_actual_derivative
      gInv dg ddg z r M M Q hgi hdg hgiJet hdgJet
    intro M
    exact hchristoffel M M Q
  have hT3 : scalarFieldCoordinateFDeriv T3 z r =
      ∑ Q,
        ((∑ M, coordinateChristoffelJet
            (gInv z) (dg z) (ddg z) r M M Q) *
          coordinateChristoffel (gInv z) (dg z) Q N P +
        (∑ M, coordinateChristoffel (gInv z) (dg z) M M Q) *
          coordinateChristoffelJet
            (gInv z) (dg z) (ddg z) r Q N P) := by
    dsimp [T3]
    rw [scalarFieldCoordinateFDeriv_sum]
    apply Finset.sum_congr rfl
    intro Q _
    rw [scalarFieldCoordinateFDeriv_mul _ _ z r
      (htraceDiff Q) (hchristoffel Q N P), htrace]
    rw [coordinateChristoffel_actual_derivative
      gInv dg ddg z r Q N P hgi hdg hgiJet hdgJet]
    intro Q
    exact (htraceDiff Q).mul (hchristoffel Q N P)
  have hT4 : scalarFieldCoordinateFDeriv T4 z r =
      ∑ M, ∑ Q,
        (coordinateChristoffelJet
            (gInv z) (dg z) (ddg z) r M N Q *
          coordinateChristoffel (gInv z) (dg z) Q M P +
        coordinateChristoffel (gInv z) (dg z) M N Q *
          coordinateChristoffelJet
            (gInv z) (dg z) (ddg z) r Q M P) := by
    dsimp [T4]
    rw [scalarFieldCoordinateFDeriv_sum]
    apply Finset.sum_congr rfl
    intro M _
    rw [scalarFieldCoordinateFDeriv_sum]
    apply Finset.sum_congr rfl
    intro Q _
    rw [scalarFieldCoordinateFDeriv_mul _ _ z r
      (hchristoffel M N Q) (hchristoffel Q M P)]
    rw [coordinateChristoffel_actual_derivative
        gInv dg ddg z r M N Q hgi hdg hgiJet hdgJet,
      coordinateChristoffel_actual_derivative
        gInv dg ddg z r Q M P hgi hdg hgiJet hdgJet]
    intro Q
    exact (hchristoffel M N Q).mul (hchristoffel Q M P)
    intro M'
    rw [show (fun y ↦ ∑ Q,
        coordinateChristoffel (gInv y) (dg y) M' N Q *
          coordinateChristoffel (gInv y) (dg y) Q M' P) =
      ∑ Q, fun y ↦ coordinateChristoffel (gInv y) (dg y) M' N Q *
          coordinateChristoffel (gInv y) (dg y) Q M' P by rfl]
    apply DifferentiableAt.sum
    intro Q _
    exact (hchristoffel M' N Q).mul (hchristoffel Q M' P)
  unfold coordinateRicci coordinateRicciFirstJet
  change scalarFieldCoordinateFDeriv
    (fun y ↦ T1 y - T2 y + T3 y - T4 y) z r = _
  have houter : scalarFieldCoordinateFDeriv
      (fun y ↦ (T1 y - T2 y + T3 y) - T4 y) z r =
      scalarFieldCoordinateFDeriv
          (fun y ↦ T1 y - T2 y + T3 y) z r -
        scalarFieldCoordinateFDeriv T4 z r :=
    scalarFieldCoordinateFDeriv_sub _ _ z r
      ((hT1diff.sub hT2diff).add hT3diff) hT4diff
  rw [houter]
  have hadd : scalarFieldCoordinateFDeriv
      (fun y ↦ T1 y - T2 y + T3 y) z r =
      scalarFieldCoordinateFDeriv (fun y ↦ T1 y - T2 y) z r +
        scalarFieldCoordinateFDeriv T3 z r :=
    scalarFieldCoordinateFDeriv_add _ _ z r
      (hT1diff.sub hT2diff) hT3diff
  rw [hadd]
  have hsub : scalarFieldCoordinateFDeriv
      (fun y ↦ T1 y - T2 y) z r =
      scalarFieldCoordinateFDeriv T1 z r -
        scalarFieldCoordinateFDeriv T2 z r :=
    scalarFieldCoordinateFDeriv_sub _ _ z r hT1diff hT2diff
  rw [hsub, hT1, hT2, hT3, hT4]

end RainichKaluza
