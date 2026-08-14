import RainichKaluza.LorentzFrameTransport
import RainichKaluza.LocalExteriorSeed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Normal-coordinate matter-stress divergence identities

The converse program needs more than contracted Bianchi: it must turn the
divergence of the trace-reversed matter source into the scalar field
residual.  This file begins that bridge at a Minkowski normal-coordinate
point.  It treats the value `v` of the scalar covector and its coordinate
first jet `D` as independent algebraic data, so no unproved regularity or
coordinate covariance is hidden in the statements.
-/

namespace RainichKaluza

open scoped Matrix

/-- Raise a scalar covector in the selected diagonal normal frame. -/
def normalRaisedOneForm (v : OneForm4) : OneForm4 :=
  fun i => minkowskiSign i * v i

/-- Minkowski contraction `v^2` of a scalar covector. -/
noncomputable def normalScalarGradientSq (v : OneForm4) : ℝ :=
  ∑ i : Fin 4, normalRaisedOneForm v i * v i

/-- Mixed trace-reversed Einstein source of the convention-normalized scalar
term at a Minkowski normal-coordinate point:
`(1/2) v^mu v_nu - (1/4) delta^mu_nu v^2`. -/
noncomputable def normalScalarEinsteinStressMixed
    (v : OneForm4) : Matrix4 :=
  fun i j =>
    (1 / 2 : ℝ) * normalRaisedOneForm v i * v j -
      (1 / 4 : ℝ) * (if i = j then 1 else 0) * normalScalarGradientSq v

/-- Directional first variation of the mixed scalar Einstein source at
fixed Minkowski metric. -/
noncomputable def normalScalarEinsteinStressMixedFirstVariation
    (v dv : OneForm4) : Matrix4 :=
  fun i j =>
    (1 / 2 : ℝ) *
        (normalRaisedOneForm dv i * v j +
          normalRaisedOneForm v i * dv j) -
      (1 / 4 : ℝ) * (if i = j then 1 else 0) *
        (∑ k : Fin 4,
          (normalRaisedOneForm dv k * v k +
            normalRaisedOneForm v k * dv k))

/-- Coordinate divergence of the scalar stress first jet at a normal point.
The derivative direction and raised tensor index are contracted. -/
noncomputable def normalScalarEinsteinStressDivergence
    (v : OneForm4) (D : Fin 4 → OneForm4) : OneForm4 :=
  fun j => ∑ i, normalScalarEinsteinStressMixedFirstVariation v (D i) i j

/-- Normal-coordinate wave trace of the scalar Hessian. -/
noncomputable def normalScalarWaveTrace
    (D : Fin 4 → OneForm4) : ℝ :=
  ∑ i : Fin 4, normalRaisedOneForm (D i) i

/-- **Scalar Noether identity at a normal point.**  If the scalar one-form
jet is symmetric (the coordinate form of `dv = 0`), the divergence of its
trace-reversed Einstein source is exactly one half of the wave residual
times the scalar covector. -/
theorem normalScalarEinsteinStressDivergence_eq
    (v : OneForm4) (D : Fin 4 → OneForm4)
    (hD : ∀ i j, D i j = D j i) :
    normalScalarEinsteinStressDivergence v D =
      (1 / 2 * normalScalarWaveTrace D) • v := by
  funext j
  fin_cases j <;>
    simp [normalScalarEinsteinStressDivergence,
      normalScalarEinsteinStressMixedFirstVariation,
      normalScalarWaveTrace, normalRaisedOneForm, minkowskiSign,
      Fin.sum_univ_succ, hD] <;>
    ring

/-- Raise both indices of a two-form in the selected normal frame. -/
noncomputable def normalRaisedTwoForm (F : Matrix4) : Matrix4 :=
  fun i j => minkowskiSign i * minkowskiSign j * F i j

/-- Lorentz scalar `F_{mu nu} F^{mu nu}`. -/
noncomputable def normalTwoFormSq (F : Matrix4) : ℝ :=
  ∑ i, ∑ j, normalRaisedTwoForm F i j * F i j

/-- Directional first variation, at fixed normal metric, of the ordinary
mixed Maxwell stress used by the curvature seed. -/
noncomputable def normalMaxwellStressMixedFirstVariation
    (F dF : Matrix4) : Matrix4 :=
  fun i j =>
    (∑ r, normalRaisedTwoForm dF i r * F j r) +
      (∑ r, normalRaisedTwoForm F i r * dF j r) -
        (1 / 4 : ℝ) * (if i = j then 1 else 0) *
          (∑ p : Fin 4, ∑ q : Fin 4,
            (normalRaisedTwoForm dF p q * F p q +
              normalRaisedTwoForm F p q * dF p q))

/-- Raw coordinate divergence of the displayed Maxwell-stress first
variation.  Identifying this expression with the alternating-form
contraction below is the finite algebra theorem proved there. -/
noncomputable def normalMaxwellStressFirstJetDivergence
    (F : Matrix4) (D : Fin 4 → Matrix4) : OneForm4 :=
  fun j => ∑ i, normalMaxwellStressMixedFirstVariation F (D i) i j

/-- Coordinate divergence `partial_mu F^{mu rho}` of a two-form first jet. -/
noncomputable def normalTwoFormDivergence
    (D : Fin 4 → Matrix4) : OneForm4 :=
  fun r => ∑ i, normalRaisedTwoForm (D i) i r

/-- Cyclic coordinate exterior derivative of a two-form first jet. -/
def normalTwoFormExteriorFirstJet
    (D : Fin 4 → Matrix4) (i j k : Fin 4) : ℝ :=
  D i j k + D j k i + D k i j

/-- Alternating-form contraction formula for the Maxwell-stress divergence.
It displays the two off-shell terms that the Bianchi and Maxwell equations
control. -/
noncomputable def normalMaxwellStressDivergence
    (F : Matrix4) (D : Fin 4 → Matrix4) : OneForm4 :=
  fun j =>
    (∑ r, normalTwoFormDivergence D r * F j r) +
      (1 / 2 : ℝ) *
        ∑ i, ∑ r, normalRaisedTwoForm F i r *
          normalTwoFormExteriorFirstJet D i j r

/-- The raw coordinate first variation of Maxwell stress agrees with its
standard alternating-form contraction.  The only hypotheses are the honest
ones for a two-form and its directional first derivatives: `F` and every
matrix `D k` are skew. -/
theorem normalMaxwellStressFirstJetDivergence_eq
    (F : Matrix4) (D : Fin 4 → Matrix4)
    (hF : Fᵀ = -F) (hD : ∀ k, (D k)ᵀ = -D k) :
    normalMaxwellStressFirstJetDivergence F D =
      normalMaxwellStressDivergence F D := by
  have hFnorm := eq_lorentzSkewTwoForm4_of_transpose_eq_neg F hF
  have hD0 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (D 0) (hD 0)
  have hD1 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (D 1) (hD 1)
  have hD2 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (D 2) (hD 2)
  have hD3 := eq_lorentzSkewTwoForm4_of_transpose_eq_neg (D 3) (hD 3)
  funext j
  unfold normalMaxwellStressFirstJetDivergence
    normalMaxwellStressMixedFirstVariation
    normalMaxwellStressDivergence normalTwoFormDivergence
    normalTwoFormExteriorFirstJet normalRaisedTwoForm
  simp [Fin.sum_univ_succ]
  rw [hFnorm, hD0, hD1, hD2, hD3]
  fin_cases j <;>
    simp [lorentzSkewTwoForm4, minkowskiSign] <;>
    ring

/-- Coordinate form of `dF = (a/2) v wedge F` for the rescaled Maxwell
two-form at a normal point. -/
def NormalRescaledMaxwellBianchi
    (F : Matrix4) (D : Fin 4 → Matrix4) (v : OneForm4) (a : ℝ) : Prop :=
  ∀ i j k,
    normalTwoFormExteriorFirstJet D i j k =
      (a / 2) * (v i * F j k + v j * F k i + v k * F i j)

/-- Coordinate form of the weighted Maxwell equation for the rescaled field:
`partial_mu F^{mu r} = -(a/2) v_mu F^{mu r}`. -/
def NormalRescaledMaxwellDivergence
    (F : Matrix4) (D : Fin 4 → Matrix4) (v : OneForm4) (a : ℝ) : Prop :=
  ∀ r,
    normalTwoFormDivergence D r =
      -(a / 2) * ∑ i, v i * normalRaisedTwoForm F i r

/-- Algebraic contraction of the two rescaled Maxwell sources.  This is the
factor/sign calculation that turns the exterior and weighted-divergence
equations into the dilaton force on Maxwell stress. -/
theorem normalRescaledMaxwellSources_contraction
    (F : Matrix4) (v : OneForm4) (a : ℝ)
    (hF : Fᵀ = -F) (j : Fin 4) :
    (∑ r,
        (-(a / 2) * ∑ i, v i * normalRaisedTwoForm F i r) * F j r) +
      (1 / 2 : ℝ) * ∑ i, ∑ r,
        normalRaisedTwoForm F i r *
          ((a / 2) *
            (v i * F j r + v j * F r i + v r * F i j)) =
      (-a / 4 * normalTwoFormSq F) * v j := by
  rw [eq_lorentzSkewTwoForm4_of_transpose_eq_neg F hF]
  fin_cases j <;>
    simp [normalRaisedTwoForm, normalTwoFormSq,
      lorentzSkewTwoForm4, minkowskiSign,
      Fin.sum_univ_succ] <;>
    ring

/-- **Rescaled Maxwell Noether identity at a normal point.**  The two
rescaled Maxwell equations force the divergence of the ordinary stress of
`F` to be `-(a/4) F^2 v`.  Here `F` is the curvature-normalized rescaled seed
(`H` in the convention note), so this is exactly the term needed to cancel
one half of the scalar equation residual. -/
theorem normalMaxwellStressDivergence_eq_dilatonForce
    (F : Matrix4) (D : Fin 4 → Matrix4) (v : OneForm4) (a : ℝ)
    (hF : Fᵀ = -F)
    (hBianchi : NormalRescaledMaxwellBianchi F D v a)
    (hMaxwell : NormalRescaledMaxwellDivergence F D v a) :
    normalMaxwellStressDivergence F D =
      (-a / 4 * normalTwoFormSq F) • v := by
  funext j
  unfold normalMaxwellStressDivergence
  unfold NormalRescaledMaxwellDivergence at hMaxwell
  unfold NormalRescaledMaxwellBianchi at hBianchi
  simp_rw [hMaxwell, hBianchi]
  exact normalRescaledMaxwellSources_contraction F v a hF j

/-- Normal-coordinate scalar equation residual in the rescaled-seed
normalization: `box phi - (a/2) F^2`. -/
noncomputable def normalScalarEquationResidual
    (D : Fin 4 → OneForm4) (F : Matrix4) (a : ℝ) : ℝ :=
  normalScalarWaveTrace D - (a / 2) * normalTwoFormSq F

/-- **Combined matter Noether identity.**  Scalar closure and the two
rescaled Maxwell equations turn the divergence of the complete
trace-reversed matter source into one half of the scalar residual times
`v`. -/
theorem normalMatterStressDivergence_eq_scalarResidual
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F : Matrix4) (DF : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F)
    (hBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hMaxwell : NormalRescaledMaxwellDivergence F DF v a) :
    normalScalarEinsteinStressDivergence v Dv +
    normalMaxwellStressDivergence F DF =
      (1 / 2 * normalScalarEquationResidual Dv F a) • v := by
  rw [normalScalarEinsteinStressDivergence_eq v Dv hDv,
    normalMaxwellStressDivergence_eq_dilatonForce
      F DF v a hF hBianchi hMaxwell]
  funext j
  simp [normalScalarEquationResidual]
  ring

/-- **Combined matter Noether identity for the raw stress first jet.**
When every directional Maxwell jet is skew, the actual first variation of
the displayed Maxwell stress has the same scalar-residual divergence as the
alternating-form contraction. -/
theorem normalMatterStressFirstJetDivergence_eq_scalarResidual
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F : Matrix4) (DF : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hMaxwell : NormalRescaledMaxwellDivergence F DF v a) :
    normalScalarEinsteinStressDivergence v Dv +
    normalMaxwellStressFirstJetDivergence F DF =
      (1 / 2 * normalScalarEquationResidual Dv F a) • v := by
  rw [normalMaxwellStressFirstJetDivergence_eq F DF hF hDF]
  exact normalMatterStressDivergence_eq_scalarResidual
    v Dv F DF a hDv hF hBianchi hMaxwell

/-- On the active scalar branch, contracted Bianchi plus the matter Noether
identity forces the scalar equation; it is not an independent detector
hypothesis. -/
theorem normalScalarEquationResidual_eq_zero_of_matterDivergence
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F : Matrix4) (DF : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F)
    (hBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hMaxwell : NormalRescaledMaxwellDivergence F DF v a)
    (hv : v ≠ 0)
    (hdiv : normalScalarEinsteinStressDivergence v Dv +
      normalMaxwellStressDivergence F DF = 0) :
    normalScalarEquationResidual Dv F a = 0 := by
  have hNoether := normalMatterStressDivergence_eq_scalarResidual
    v Dv F DF a hDv hF hBianchi hMaxwell
  rw [hdiv] at hNoether
  have hsmul :
      (1 / 2 * normalScalarEquationResidual Dv F a) • v = 0 :=
    hNoether.symm
  obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    exact h i
  have hi := congrFun hsmul i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  rcases mul_eq_zero.mp hi with hres | hvi0
  · norm_num at hres
    exact hres
  · exact (hvi hvi0).elim

/-- On the active scalar branch, vanishing divergence of the raw displayed
scalar-plus-Maxwell stress first jet forces the scalar equation residual. -/
theorem normalScalarEquationResidual_eq_zero_of_rawMatterDivergence
    (v : OneForm4) (Dv : Fin 4 → OneForm4)
    (F : Matrix4) (DF : Fin 4 → Matrix4) (a : ℝ)
    (hDv : ∀ i j, Dv i j = Dv j i)
    (hF : Fᵀ = -F) (hDF : ∀ k, (DF k)ᵀ = -DF k)
    (hBianchi : NormalRescaledMaxwellBianchi F DF v a)
    (hMaxwell : NormalRescaledMaxwellDivergence F DF v a)
    (hv : v ≠ 0)
    (hdiv : normalScalarEinsteinStressDivergence v Dv +
      normalMaxwellStressFirstJetDivergence F DF = 0) :
    normalScalarEquationResidual Dv F a = 0 := by
  apply normalScalarEquationResidual_eq_zero_of_matterDivergence
    v Dv F DF a hDv hF hBianchi hMaxwell hv
  rw [← normalMaxwellStressFirstJetDivergence_eq F DF hF hDF]
  exact hdiv

end RainichKaluza
