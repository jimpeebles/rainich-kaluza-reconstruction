import RainichKaluza.GeometricCouplingDetector
import RainichKaluza.CoordinateRicci
import RainichKaluza.CoordinateRicciFirstJet
import RainichKaluza.MetricHodge
import RainichKaluza.InvariantActiveWedge
import RainichKaluza.PhysicalComplexionInvariant

/-!
# A formal metric-three-jet representative of the third-order shear

The channel-level shear by itself is not a theorem about complete metric
three-jets.  This file constructs an explicit common formal normal-coordinate
metric three-jet for two distinct couplings, in addition to realizing the
corresponding matter jets.

Take a canonical non-null Maxwell seed and rotate it to the balanced point
`F = (F0 + *F0) / sqrt 2`.  Its quadratic scalar invariant vanishes.  Keep
the unrotated seed and its full first jet constant, and set

`omega_a = -(a/2) Jv`.

For every constant coupling `a`, the resulting physical two-form first jet
satisfies both exterior EMD equations.  Its Maxwell stress has the same
point value for every `a`, and its complete first variation vanishes because
the only variation is tangent to the duality orbit.  Thus two different
coupling squares have identical algebraic matter data on the right-hand side
of the Einstein equation through its first derivative.

The metric jet satisfies the Einstein equation and its first prolongation,
while the matter jets satisfy the two exterior equations, the point scalar
equation, and the point/first-jet Hodge relations.  This remains a *formal
finite-jet* ambiguity: the file does not prove formal integrability to all
orders or realization by two actual local EMD solutions.  Those stronger
claims require the remaining compatibility/prolongation analysis (including
the differential Bianchi identities) and a PDE existence theorem.
-/

namespace RainichKaluza

open scoped Matrix

/-- The common coefficient at the balanced point of the Maxwell duality
circle. -/
noncomputable def balancedDualityCoefficient : ℝ := Real.sqrt 2 / 2

/-- The balanced coefficients lie on the unit circle. -/
theorem balancedDualityCoefficient_unit :
    balancedDualityCoefficient ^ 2 + balancedDualityCoefficient ^ 2 = 1 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  unfold balancedDualityCoefficient
  nlinarith

/-- The balanced coefficient is nonzero. -/
theorem balancedDualityCoefficient_ne_zero :
    balancedDualityCoefficient ≠ 0 := by
  unfold balancedDualityCoefficient
  positivity

private theorem inv_two_mul_eq_self_imp_eq_zero
    (x : ℝ) (h : (2 : ℝ)⁻¹ * x = x) : x = 0 := by
  by_contra hx
  have hcoeff : (2 : ℝ)⁻¹ = 1 :=
    mul_right_cancel₀ hx (h.trans (one_mul x).symm)
  norm_num at hcoeff

/-- Canonical physical Maxwell field at the balanced duality point. -/
noncomputable def balancedCanonicalMaxwellField (E : ℝ) : Matrix4 :=
  balancedDualityCoefficient • canonicalMaxwellTwoForm E 0 +
    balancedDualityCoefficient • canonicalHodgeStar E 0

/-- Its canonical Hodge partner. -/
noncomputable def balancedCanonicalMaxwellHodge (E : ℝ) : Matrix4 :=
  (-balancedDualityCoefficient) • canonicalMaxwellTwoForm E 0 +
    balancedDualityCoefficient • canonicalHodgeStar E 0

/-- The balanced field is the canonical form with equal electric and
magnetic amplitudes. -/
theorem balancedCanonicalMaxwellField_eq_canonical (E : ℝ) :
    balancedCanonicalMaxwellField E =
      canonicalMaxwellTwoForm
        (balancedDualityCoefficient * E)
        (balancedDualityCoefficient * E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedCanonicalMaxwellField, canonicalHodgeStar,
      canonicalMaxwellTwoForm]

/-- The displayed partner is exactly the metric Hodge dual of the balanced
Maxwell field, rather than an independent second two-form. -/
theorem coordinateMetricHodgeTwoForm4_balancedCanonicalMaxwellField
    (E : ℝ) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (balancedCanonicalMaxwellField E) =
      balancedCanonicalMaxwellHodge E := by
  rw [balancedCanonicalMaxwellField_eq_canonical,
    coordinateMetricHodgeTwoForm4_minkowski]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedCanonicalMaxwellHodge, balancedDualityCoefficient,
      canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- The balanced Hodge partner is also a canonical two-form. -/
theorem balancedCanonicalMaxwellHodge_eq_canonical (E : ℝ) :
    balancedCanonicalMaxwellHodge E =
      canonicalMaxwellTwoForm
        (-(balancedDualityCoefficient * E))
        (balancedDualityCoefficient * E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedCanonicalMaxwellHodge, canonicalHodgeStar,
      canonicalMaxwellTwoForm]

/-- The Hodge square on the balanced field is minus the identity. -/
theorem coordinateMetricHodgeTwoForm4_balancedCanonicalMaxwellHodge
    (E : ℝ) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (balancedCanonicalMaxwellHodge E) =
      -balancedCanonicalMaxwellField E := by
  rw [balancedCanonicalMaxwellHodge_eq_canonical,
    coordinateMetricHodgeTwoForm4_minkowski,
    balancedCanonicalMaxwellField_eq_canonical]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- The coupling-dependent complexion rate that makes the effective
first-order channel vanish while the physical sine component is `B=a`. -/
noncomputable def balancedComplexionRate
    (a : ℝ) (v : OneForm4) : OneForm4 :=
  (-(a / 2)) • canonicalPrincipalReflectionCovector v

/-- Full directional first jet of the balanced physical Maxwell field.  The
underlying unrotated canonical seed has zero first jet, so this is purely the
infinitesimal duality rotation. -/
noncomputable def balancedCanonicalMaxwellFirstJet
    (E a : ℝ) (v : OneForm4) : TwoFormFirstDerivative4 :=
  fun k ↦ (balancedComplexionRate a v k) •
    balancedCanonicalMaxwellHodge E

/-- Full directional first jet of the Hodge partner. -/
noncomputable def balancedCanonicalMaxwellHodgeFirstJet
    (E a : ℝ) (v : OneForm4) : TwoFormFirstDerivative4 :=
  fun k ↦ (-(balancedComplexionRate a v k)) •
    balancedCanonicalMaxwellField E

/-- Because the common metric first jet is zero, differentiating the Hodge
relation has no metric-variation term: each displayed Hodge first jet is the
metric Hodge dual of the corresponding Maxwell first jet. -/
theorem balancedCanonicalMaxwellFirstJet_hodgeCompatible
    (E a : ℝ) (v : OneForm4) (k : Fin 4) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (balancedCanonicalMaxwellFirstJet E a v k) =
      balancedCanonicalMaxwellHodgeFirstJet E a v k := by
  let r := balancedComplexionRate a v k
  have hdF : balancedCanonicalMaxwellFirstJet E a v k =
      canonicalMaxwellTwoForm
        (-(r * balancedDualityCoefficient * E))
        (r * balancedDualityCoefficient * E) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [balancedCanonicalMaxwellFirstJet,
        balancedCanonicalMaxwellHodge, canonicalHodgeStar,
        canonicalMaxwellTwoForm, r] <;> ring
  rw [hdF, coordinateMetricHodgeTwoForm4_minkowski]
  unfold balancedCanonicalMaxwellHodgeFirstJet
  rw [balancedCanonicalMaxwellField_eq_canonical]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHodgeStar, canonicalMaxwellTwoForm, r] <;> ring

/-- At the balanced point the shear-compensated effective connection is
exactly zero. -/
theorem effectiveComplexionOneForm_balanced_eq_zero
    (a : ℝ) (v : OneForm4) :
    effectiveComplexionOneForm (balancedComplexionRate a v)
      (canonicalPrincipalReflectionCovector v) a = 0 := by
  funext i
  simp [effectiveComplexionOneForm, balancedComplexionRate]

/-- Consequently the complete unrotated curvature-seed exterior jet is the
same zero pair for every coupling. -/
theorem canonicalPhysicalSeedChannels_balanced_eq_zero
    (E a : ℝ) (v : OneForm4) :
    canonicalPhysicalSeedChannels E v (balancedComplexionRate a v) 0 a =
      (0, 0) := by
  rw [canonicalPhysicalSeedChannels_eq_full]
  unfold canonicalFullComplexionCouplingChannels
  rw [effectiveComplexionOneForm_balanced_eq_zero]
  ext <;>
    simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor]

/-- Exteriorizing the displayed full first jet gives the first physical EMD
equation for every coupling. -/
theorem matrixExteriorDerivative_balancedCanonicalMaxwellFirstJet
    (E a : ℝ) (v : OneForm4) :
    matrixExteriorDerivative
        (balancedCanonicalMaxwellFirstJet E a v) =
      (a / 2) • matrixOneWedgeTwoTensor v
        (balancedCanonicalMaxwellField E) := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixExteriorDerivative, balancedCanonicalMaxwellFirstJet,
      balancedComplexionRate, balancedCanonicalMaxwellField,
      balancedCanonicalMaxwellHodge,
      canonicalPrincipalReflectionCovector, matrixOneWedgeTwoTensor,
      balancedDualityCoefficient, canonicalHodgeStar,
      canonicalMaxwellTwoForm] <;> ring

/-- Exteriorizing the displayed Hodge first jet gives the second physical
EMD equation for every coupling. -/
theorem matrixExteriorDerivative_balancedCanonicalMaxwellHodgeFirstJet
    (E a : ℝ) (v : OneForm4) :
    matrixExteriorDerivative
        (balancedCanonicalMaxwellHodgeFirstJet E a v) =
      -(a / 2) • matrixOneWedgeTwoTensor v
        (balancedCanonicalMaxwellHodge E) := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixExteriorDerivative,
      balancedCanonicalMaxwellHodgeFirstJet,
      balancedComplexionRate, balancedCanonicalMaxwellField,
      balancedCanonicalMaxwellHodge,
      canonicalPrincipalReflectionCovector, matrixOneWedgeTwoTensor,
      balancedDualityCoefficient, canonicalHodgeStar,
      canonicalMaxwellTwoForm] <;> ring

/-- **Full first-jet exterior EMD realization.**  The two directional matrix
jets above, not merely abstract three-form channels, satisfy the complete
rescaled Bianchi/weighted-Maxwell exterior pair for every `a`. -/
theorem balancedCanonicalMaxwellJet_emdExteriorClosure
    (E a : ℝ) (v : OneForm4) :
    EMDExteriorClosure matrixOneWedgeTwo v a
      (balancedCanonicalMaxwellField E)
      (balancedCanonicalMaxwellHodge E)
      (matrixExteriorDerivative
        (balancedCanonicalMaxwellFirstJet E a v))
      (matrixExteriorDerivative
        (balancedCanonicalMaxwellHodgeFirstJet E a v)) := by
  constructor
  · exact matrixExteriorDerivative_balancedCanonicalMaxwellFirstJet E a v
  · exact
      matrixExteriorDerivative_balancedCanonicalMaxwellHodgeFirstJet E a v

/-- First variation of the mixed Maxwell stress with respect to its two-form
argument at fixed inverse metric. -/
noncomputable def matrixMaxwellStressFirstVariation
    (G F dF : Matrix4) : Matrix4 :=
  let dcore := G * dF * G * F + G * F * G * dF
  (-dcore) + (1 / 4 * Matrix.trace dcore) • (1 : Matrix4)

/-- Scalar rank-one part of the point mixed Ricci source. -/
noncomputable def balancedCanonicalScalarRicciSource
    (v : OneForm4) : Matrix4 :=
  fun i j ↦ ((2 : ℝ)⁻¹ * v j) * (minkowskiMetric.mulVec v) i

/-- Point mixed Ricci source in the normalization used by the curvature
reconstruction: Maxwell stress plus `1/2 v^♯ tensor v`. -/
noncomputable def balancedCanonicalRicciSource
    (E : ℝ) (v : OneForm4) : Matrix4 :=
  matrixMaxwellStress minkowskiMetric (balancedCanonicalMaxwellField E) +
    balancedCanonicalScalarRicciSource v

/-- First directional variation of that Ricci source when the scalar Hessian
is zero.  Only the Maxwell-stress variation remains. -/
noncomputable def balancedCanonicalRicciSourceFirstJet
    (E a : ℝ) (v : OneForm4) : Fin 4 → Matrix4 :=
  fun k ↦ matrixMaxwellStressFirstVariation minkowskiMetric
    (balancedCanonicalMaxwellField E)
    (balancedCanonicalMaxwellFirstJet E a v k)

/-- The balanced Maxwell quadratic scalar invariant vanishes.  This is the
matter-side reason the point scalar equation can be chosen independently of
the coupling in this construction. -/
theorem balancedCanonicalMaxwell_quadraticInvariant_eq_zero (E : ℝ) :
    Matrix.trace
      (minkowskiMetric * balancedCanonicalMaxwellField E *
        minkowskiMetric * balancedCanonicalMaxwellField E) = 0 := by
  simp [balancedCanonicalMaxwellField, balancedDualityCoefficient,
    canonicalHodgeStar, canonicalMaxwellTwoForm, minkowskiMetric,
    Matrix.trace, Fin.sum_univ_succ]

/-- Generic-coupling scalar-equation residual in the curvature-seed
normalization: `box phi = (a/2) H^2`, with
`H^2 = -trace(G H G H)`. -/
noncomputable def genericEMDScalarJetResidual
    (a : ℝ) (phi2 : Fin 4 → Fin 4 → ℝ) (F : Matrix4) : ℝ :=
  normalFrameScalarBox minkowskiSign phi2 +
    (a / 2) * Matrix.trace (minkowskiMetric * F * minkowskiMetric * F)

/-- With zero scalar Hessian, the balanced field satisfies the scalar
equation for every coupling because its quadratic invariant vanishes. -/
theorem genericEMDScalarJetResidual_balanced_eq_zero
    (E a : ℝ) :
    genericEMDScalarJetResidual a 0
      (balancedCanonicalMaxwellField E) = 0 := by
  unfold genericEMDScalarJetResidual normalFrameScalarBox
  rw [balancedCanonicalMaxwell_quadraticInvariant_eq_zero]
  simp

/-- In particular both distinct couplings in the formal ambiguity satisfy
the scalar point equation using the same zero scalar Hessian. -/
theorem genericEMDScalarJetResidual_balanced_one_and_two
    (E : ℝ) :
    genericEMDScalarJetResidual 1 0
        (balancedCanonicalMaxwellField E) = 0 ∧
      genericEMDScalarJetResidual 2 0
        (balancedCanonicalMaxwellField E) = 0 := by
  exact ⟨genericEMDScalarJetResidual_balanced_eq_zero E 1,
    genericEMDScalarJetResidual_balanced_eq_zero E 2⟩

/-- Infinitesimal duality motion is in the exact kernel of the Maxwell-stress
first variation. -/
theorem matrixMaxwellStressFirstVariation_balanced_hodge_eq_zero (E : ℝ) :
    matrixMaxwellStressFirstVariation minkowskiMetric
      (balancedCanonicalMaxwellField E)
      (balancedCanonicalMaxwellHodge E) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixMaxwellStressFirstVariation,
      balancedCanonicalMaxwellField, balancedCanonicalMaxwellHodge,
      balancedDualityCoefficient, canonicalHodgeStar,
      canonicalMaxwellTwoForm, minkowskiMetric,
      Matrix.trace, Fin.sum_univ_succ] <;> ring

/-- Every directional first variation of the Maxwell stress is zero, even
though the physical Maxwell first jet itself depends on `a`. -/
theorem matrixMaxwellStressFirstVariation_balancedFirstJet_eq_zero
    (E a : ℝ) (v : OneForm4) (k : Fin 4) :
    matrixMaxwellStressFirstVariation minkowskiMetric
      (balancedCanonicalMaxwellField E)
      (balancedCanonicalMaxwellFirstJet E a v k) = 0 := by
  unfold balancedCanonicalMaxwellFirstJet
  have hlinear :
      matrixMaxwellStressFirstVariation minkowskiMetric
          (balancedCanonicalMaxwellField E)
          ((balancedComplexionRate a v k) •
            balancedCanonicalMaxwellHodge E) =
        (balancedComplexionRate a v k) •
          matrixMaxwellStressFirstVariation minkowskiMetric
            (balancedCanonicalMaxwellField E)
            (balancedCanonicalMaxwellHodge E) := by
    ext i j
    simp [matrixMaxwellStressFirstVariation, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_succ]
    ring
  rw [hlinear, matrixMaxwellStressFirstVariation_balanced_hodge_eq_zero]
  simp

/-- The complete mixed Ricci-source first jet is the common zero jet for
every coupling in the balanced family. -/
theorem balancedCanonicalRicciSourceFirstJet_eq_zero
    (E a : ℝ) (v : OneForm4) :
    balancedCanonicalRicciSourceFirstJet E a v = 0 := by
  funext k i j
  have h := congrArg (fun M : Matrix4 ↦ M i j)
    (matrixMaxwellStressFirstVariation_balancedFirstJet_eq_zero E a v k)
  simpa [balancedCanonicalRicciSourceFirstJet] using h

/-- On the non-null, nonzero-source branch the two displayed physical
Maxwell first jets really are different.  Their equality at the stress-jet
level is therefore a genuine kernel, not equality of the matter jets. -/
theorem balancedCanonicalMaxwellFirstJet_one_ne_two
    (E : ℝ) (v : OneForm4) (hE : E ≠ 0) (hv : v ≠ 0) :
    balancedCanonicalMaxwellFirstJet E 1 v ≠
      balancedCanonicalMaxwellFirstJet E 2 v := by
  intro hjets
  obtain ⟨k, hk⟩ := exists_oneForm4_component_ne_zero v hv
  have hentry := congrArg (fun D : TwoFormFirstDerivative4 ↦ D k 0 1) hjets
  fin_cases k <;>
    simp [balancedCanonicalMaxwellFirstJet, balancedComplexionRate,
      balancedCanonicalMaxwellHodge, balancedDualityCoefficient,
      canonicalPrincipalReflectionCovector, canonicalHodgeStar,
      canonicalMaxwellTwoForm] at hentry
  all_goals
    rcases hentry with hhalf | hzero
    · apply hk
      all_goals exact inv_two_mul_eq_self_imp_eq_zero _ hhalf
    · exact hE hzero

/-- **Realized matter-jet lower bound for the exterior/Ricci-source layer.**
Couplings `1` and `2` have different squares, but the same balanced physical
Maxwell field, the same point Maxwell stress, the same vanishing Maxwell
stress first jet, the same zero scalar Maxwell invariant, and each has a full
directional two-form first jet satisfying both EMD exterior equations.

The conclusion stops exactly before metric-three-jet realization: no metric
or claim of local PDE existence is hidden in this statement. -/
theorem balancedCanonicalMatterJets_distinctCouplingSq_sameRicciSourceJet
    (E : ℝ) (v : OneForm4) (hE : E ≠ 0) (hv : v ≠ 0) :
    (1 : ℝ) ^ 2 ≠ (2 : ℝ) ^ 2 ∧
      balancedCanonicalMaxwellFirstJet E 1 v ≠
        balancedCanonicalMaxwellFirstJet E 2 v ∧
      EMDExteriorClosure matrixOneWedgeTwo v 1
        (balancedCanonicalMaxwellField E)
        (balancedCanonicalMaxwellHodge E)
        (matrixExteriorDerivative
          (balancedCanonicalMaxwellFirstJet E 1 v))
        (matrixExteriorDerivative
          (balancedCanonicalMaxwellHodgeFirstJet E 1 v)) ∧
      EMDExteriorClosure matrixOneWedgeTwo v 2
        (balancedCanonicalMaxwellField E)
        (balancedCanonicalMaxwellHodge E)
        (matrixExteriorDerivative
          (balancedCanonicalMaxwellFirstJet E 2 v))
        (matrixExteriorDerivative
          (balancedCanonicalMaxwellHodgeFirstJet E 2 v)) ∧
      Matrix.trace
        (minkowskiMetric * balancedCanonicalMaxwellField E *
          minkowskiMetric * balancedCanonicalMaxwellField E) = 0 ∧
      balancedCanonicalRicciSourceFirstJet E 1 v =
        balancedCanonicalRicciSourceFirstJet E 2 v ∧
      ∀ k : Fin 4,
        matrixMaxwellStressFirstVariation minkowskiMetric
            (balancedCanonicalMaxwellField E)
            (balancedCanonicalMaxwellFirstJet E 1 v k) =
          matrixMaxwellStressFirstVariation minkowskiMetric
            (balancedCanonicalMaxwellField E)
            (balancedCanonicalMaxwellFirstJet E 2 v k) := by
  refine ⟨by norm_num,
    balancedCanonicalMaxwellFirstJet_one_ne_two E v hE hv,
    balancedCanonicalMaxwellJet_emdExteriorClosure E 1 v,
    balancedCanonicalMaxwellJet_emdExteriorClosure E 2 v,
    balancedCanonicalMaxwell_quadraticInvariant_eq_zero E,
    (balancedCanonicalRicciSourceFirstJet_eq_zero E 1 v).trans
      (balancedCanonicalRicciSourceFirstJet_eq_zero E 2 v).symm, ?_⟩
  intro k
  rw [matrixMaxwellStressFirstVariation_balancedFirstJet_eq_zero,
    matrixMaxwellStressFirstVariation_balancedFirstJet_eq_zero]

/-! ## Formal normal-coordinate metric three-jet realization -/

/-- Lorentz trace of a covariant rank-two tensor in the canonical frame. -/
noncomputable def minkowskiCovariantTrace (T : Matrix4) : ℝ :=
  ∑ i : Fin 4, minkowskiSign i * T i i

/-- Hessian that realizes a prescribed symmetric covariant Ricci tensor via
the conformal normal-coordinate second jet. -/
noncomputable def normalCoordinateConformalHessianOfRicci
    (T : Matrix4) : Matrix4 :=
  fun i j ↦ -T i j / 2 +
    minkowskiMetric i j * minkowskiCovariantTrace T / 12

/-- The conformal Hessian is symmetric whenever the target Ricci tensor is. -/
theorem normalCoordinateConformalHessianOfRicci_symm
    (T : Matrix4) (hT : Tᵀ = T) (i j : Fin 4) :
    normalCoordinateConformalHessianOfRicci T i j =
      normalCoordinateConformalHessianOfRicci T j i := by
  have hTij := congrArg (fun M : Matrix4 ↦ M i j) hT
  simp only [Matrix.transpose_apply] at hTij
  have heta : minkowskiMetric i j = minkowskiMetric j i := by
    fin_cases i <;> fin_cases j <;> simp [minkowskiMetric]
  simp [normalCoordinateConformalHessianOfRicci, hTij, heta]

/-- Conformal normal-coordinate metric second jet
`g_ab,cd = 2 eta_ab H_cd`. -/
noncomputable def normalCoordinateMetricJet2OfRicci
    (T : Matrix4) : CoordinateMetricJet2 (Fin 4) :=
  fun r s i j ↦ 2 * minkowskiMetric i j *
    normalCoordinateConformalHessianOfRicci T r s

/-- The constructed second jet has commuting derivative slots. -/
theorem normalCoordinateMetricJet2OfRicci_deriv_symm
    (T : Matrix4) (hT : Tᵀ = T) (r s i j : Fin 4) :
    normalCoordinateMetricJet2OfRicci T r s i j =
      normalCoordinateMetricJet2OfRicci T s r i j := by
  unfold normalCoordinateMetricJet2OfRicci
  rw [normalCoordinateConformalHessianOfRicci_symm T hT r s]

/-- The constructed second jet preserves symmetry of the metric slots. -/
theorem normalCoordinateMetricJet2OfRicci_metric_symm
    (T : Matrix4) (r s i j : Fin 4) :
    normalCoordinateMetricJet2OfRicci T r s i j =
      normalCoordinateMetricJet2OfRicci T r s j i := by
  unfold normalCoordinateMetricJet2OfRicci
  have hmetric : minkowskiMetric i j = minkowskiMetric j i := by
    fin_cases i <;> fin_cases j <;> simp [minkowskiMetric]
  rw [hmetric]

/-- **Algebraic metric-jet realization.** Every symmetric covariant tensor is
the Ricci tensor of the explicit normal-coordinate metric second jet above. -/
theorem normalFrameBaseRicci_normalCoordinateMetricJet2OfRicci
    (T : Matrix4) (hT : Tᵀ = T) (n p : Fin 4) :
    normalFrameBaseRicci minkowskiSign
      (normalCoordinateMetricJet2OfRicci T) n p = T n p := by
  have hsym := normalCoordinateConformalHessianOfRicci_symm T hT
  have h10 := hsym 1 0
  have h20 := hsym 2 0
  have h30 := hsym 3 0
  have h21 := hsym 2 1
  have h31 := hsym 3 1
  have h32 := hsym 3 2
  have hformula :
      normalFrameBaseRicci minkowskiSign
          (normalCoordinateMetricJet2OfRicci T) n p =
        -2 * normalCoordinateConformalHessianOfRicci T n p -
          minkowskiMetric n p *
            (∑ m : Fin 4, minkowskiSign m *
              normalCoordinateConformalHessianOfRicci T m m) := by
    fin_cases n <;> fin_cases p <;>
      simp [normalFrameBaseRicci, normalCoordinateMetricJet2OfRicci,
        minkowskiMetric, minkowskiSign, Fin.sum_univ_succ,
        h10, h20, h30, h21, h31, h32] <;> ring
  have htrace :
      (∑ m : Fin 4, minkowskiSign m *
          normalCoordinateConformalHessianOfRicci T m m) =
        -minkowskiCovariantTrace T / 6 := by
    simp [normalCoordinateConformalHessianOfRicci,
      minkowskiCovariantTrace, minkowskiMetric, minkowskiSign,
      Fin.sum_univ_succ]
    ring
  rw [hformula, htrace]
  unfold normalCoordinateConformalHessianOfRicci
  ring

/-- The balanced mixed Ricci source lowered with the canonical metric. -/
noncomputable def balancedCanonicalCovariantRicciSource
    (E : ℝ) (v : OneForm4) : Matrix4 :=
  minkowskiMetric * balancedCanonicalRicciSource E v

set_option maxHeartbeats 1000000 in
/-- The lowered balanced Ricci source is symmetric. -/
theorem balancedCanonicalCovariantRicciSource_transpose
    (E : ℝ) (v : OneForm4) :
    (balancedCanonicalCovariantRicciSource E v)ᵀ =
      balancedCanonicalCovariantRicciSource E v := by
  rw [balancedCanonicalCovariantRicciSource,
    balancedCanonicalRicciSource,
    balancedCanonicalMaxwellField_eq_canonical,
    matrixMaxwellStress_canonical]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balancedCanonicalScalarRicciSource,
      canonicalMaxwellStress, canonicalStressMagnitude,
      balancedDualityCoefficient, minkowskiMetric,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- The explicit common normal-coordinate metric second jet realizes the
balanced EMD Ricci source. -/
theorem balancedCanonicalFormalMetricJet2_einsteinEquation
    (E : ℝ) (v : OneForm4) (n p : Fin 4) :
    normalFrameBaseRicci minkowskiSign
        (normalCoordinateMetricJet2OfRicci
          (balancedCanonicalCovariantRicciSource E v)) n p =
      balancedCanonicalCovariantRicciSource E v n p := by
  exact normalFrameBaseRicci_normalCoordinateMetricJet2OfRicci
    _ (balancedCanonicalCovariantRicciSource_transpose E v) n p

/-- Choosing the common metric third jet to vanish realizes the common zero
first derivative of the Ricci source. -/
theorem balancedCanonicalFormalMetricJet3_einsteinFirstProlongation
    (E a : ℝ) (v : OneForm4) (r n p : Fin 4) :
    coordinateRicciFirstJet minkowskiMetric 0
        (normalCoordinateMetricJet2OfRicci
          (balancedCanonicalCovariantRicciSource E v))
        (0 : CoordinateMetricJet3 (Fin 4)) r n p =
      (minkowskiMetric * balancedCanonicalRicciSourceFirstJet E a v r) n p := by
  rw [coordinateRicciFirstJet_minkowski_zero]
  rw [balancedCanonicalRicciSourceFirstJet_eq_zero]
  simp [normalFrameBaseRicci]

/-- **Formal metric-three-jet ambiguity.**  On the non-null, nonzero-scalar
branch, the couplings `a=1` and `a=2` have different squares and different
physical Maxwell first jets, yet the same explicit normal-coordinate metric
jets `g_0=eta`, `g_1=0`, `g_2=normalCoordinateMetricJet2OfRicci T`, `g_3=0`.
Those common jets satisfy the Einstein equation and its first prolongation;
each matter jet satisfies both exterior EMD equations, and the scalar source
and scalar Hessian both vanish at the balanced duality point.

This is an algebraic/formal jet theorem, not an assertion that the jets
prolong to two local EMD solutions. -/
theorem exists_commonFormalMetricThreeJet_of_distinctBalancedCouplings
    (E : ℝ) (v : OneForm4) (hE : E ≠ 0) (hv : v ≠ 0) :
    ∃ g2 : CoordinateMetricJet2 (Fin 4),
      ∃ g3 : CoordinateMetricJet3 (Fin 4),
        (1 : ℝ) ^ 2 ≠ (2 : ℝ) ^ 2 ∧
        balancedCanonicalMaxwellFirstJet E 1 v ≠
          balancedCanonicalMaxwellFirstJet E 2 v ∧
        g2 = normalCoordinateMetricJet2OfRicci
          (balancedCanonicalCovariantRicciSource E v) ∧
        g3 = 0 ∧
        (∀ r s i j,
          g2 r s i j = g2 s r i j ∧
          g2 r s i j = g2 r s j i) ∧
        (∀ r s t i j,
          g3 r s t i j = g3 s r t i j ∧
          g3 r s t i j = g3 r t s i j ∧
          g3 r s t i j = g3 r s t j i) ∧
        (∀ n p, normalFrameBaseRicci minkowskiSign g2 n p =
          balancedCanonicalCovariantRicciSource E v n p) ∧
        (∀ a ∈ ({1, 2} : Set ℝ), ∀ r n p,
          coordinateRicciFirstJet minkowskiMetric 0 g2 g3 r n p =
            (minkowskiMetric *
              balancedCanonicalRicciSourceFirstJet E a v r) n p) ∧
        coordinateMetricHodgeTwoForm4 minkowskiMetric
            (balancedCanonicalMaxwellField E) =
          balancedCanonicalMaxwellHodge E ∧
        (∀ a ∈ ({1, 2} : Set ℝ), ∀ k,
          coordinateMetricHodgeTwoForm4 minkowskiMetric
              (balancedCanonicalMaxwellFirstJet E a v k) =
            balancedCanonicalMaxwellHodgeFirstJet E a v k) ∧
        EMDExteriorClosure matrixOneWedgeTwo v 1
          (balancedCanonicalMaxwellField E)
          (balancedCanonicalMaxwellHodge E)
          (matrixExteriorDerivative
            (balancedCanonicalMaxwellFirstJet E 1 v))
          (matrixExteriorDerivative
            (balancedCanonicalMaxwellHodgeFirstJet E 1 v)) ∧
        EMDExteriorClosure matrixOneWedgeTwo v 2
          (balancedCanonicalMaxwellField E)
          (balancedCanonicalMaxwellHodge E)
          (matrixExteriorDerivative
            (balancedCanonicalMaxwellFirstJet E 2 v))
          (matrixExteriorDerivative
            (balancedCanonicalMaxwellHodgeFirstJet E 2 v)) ∧
        genericEMDScalarJetResidual 1 0
            (balancedCanonicalMaxwellField E) = 0 ∧
        genericEMDScalarJetResidual 2 0
            (balancedCanonicalMaxwellField E) = 0 ∧
        Matrix.trace
          (minkowskiMetric * balancedCanonicalMaxwellField E *
            minkowskiMetric * balancedCanonicalMaxwellField E) = 0 := by
  refine ⟨normalCoordinateMetricJet2OfRicci
      (balancedCanonicalCovariantRicciSource E v), 0,
    by norm_num, balancedCanonicalMaxwellFirstJet_one_ne_two E v hE hv,
    rfl, rfl, ?_, ?_, ?_, ?_,
    coordinateMetricHodgeTwoForm4_balancedCanonicalMaxwellField E, ?_,
    balancedCanonicalMaxwellJet_emdExteriorClosure E 1 v,
    balancedCanonicalMaxwellJet_emdExteriorClosure E 2 v,
    genericEMDScalarJetResidual_balanced_eq_zero E 1,
    genericEMDScalarJetResidual_balanced_eq_zero E 2,
    balancedCanonicalMaxwell_quadraticInvariant_eq_zero E⟩
  · intro r s i j
    exact ⟨normalCoordinateMetricJet2OfRicci_deriv_symm _
        (balancedCanonicalCovariantRicciSource_transpose E v) r s i j,
      normalCoordinateMetricJet2OfRicci_metric_symm _ r s i j⟩
  · intros
    simp
  · intro n p
    exact balancedCanonicalFormalMetricJet2_einsteinEquation E v n p
  · intro a ha r n p
    exact balancedCanonicalFormalMetricJet3_einsteinFirstProlongation
      E a v r n p
  · intro a ha k
    exact balancedCanonicalMaxwellFirstJet_hodgeCompatible E a v k

/-! ## An active formal Kaluza-versus-non-Kaluza ambiguity

The preceding family lies on the inactive locus because its physical
complexion covector is parallel to the reflected scalar covector.  The next
construction adds one common, closed and co-closed Maxwell first-jet
perturbation.  That perturbation has a nonzero physical complexion wedge and
a common (generally nonzero) Maxwell-stress first variation.  A fully
symmetric common metric third jet realizes the resulting differentiated
Einstein source.
-/

/-- Fixed scalar covector used by the active formal ambiguity.  Its support in
both Maxwell principal planes makes the common point Ricci source have four
distinct real eigenvalues. -/
def activeAmbiguityScalarCovector : OneForm4 := ![1, 0, 2, 0]

/-- Fixed effective first-order connection.  It is transverse to the
principal reflection of `activeAmbiguityScalarCovector`. -/
def activeAmbiguityEffectiveOneForm : OneForm4 := ![0, 0, 1, 0]

/-- Balanced point Maxwell field with electric and magnetic amplitudes one. -/
def activeAmbiguityMaxwellField : Matrix4 :=
  canonicalMaxwellTwoForm 1 1

/-- Metric Hodge partner of `activeAmbiguityMaxwellField`. -/
def activeAmbiguityMaxwellHodge : Matrix4 :=
  canonicalMaxwellTwoForm (-1) 1

/-- The displayed partner is the actual Minkowski Hodge dual. -/
theorem coordinateMetricHodgeTwoForm4_activeAmbiguityMaxwellField :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        activeAmbiguityMaxwellField =
      activeAmbiguityMaxwellHodge := by
  rw [activeAmbiguityMaxwellField, activeAmbiguityMaxwellHodge,
    coordinateMetricHodgeTwoForm4_minkowski]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- Lorentzian Hodge square is minus the identity on the displayed active
curvature-normalized field. -/
theorem coordinateMetricHodgeTwoForm4_activeAmbiguityMaxwellHodge :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        activeAmbiguityMaxwellHodge =
      -activeAmbiguityMaxwellField := by
  rw [activeAmbiguityMaxwellField, activeAmbiguityMaxwellHodge,
    coordinateMetricHodgeTwoForm4_minkowski]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- Common source-free first-jet perturbation.  Its only independent nonzero
components are `C_0,12=2` and `C_2,01=-2`. -/
def activeAmbiguityCommonMaxwellFirstJet : TwoFormFirstDerivative4 :=
  ![!![0, 0, 0, 0;
       0, 0, 2, 0;
       0, -2, 0, 0;
       0, 0, 0, 0],
    (0 : Matrix4),
    !![0, -2, 0, 0;
       2, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, 0],
    (0 : Matrix4)]

/-- Hodge dual of the common perturbation.  Its only independent nonzero
components are `(*C)_0,03=-2` and `(*C)_2,23=-2`. -/
def activeAmbiguityCommonMaxwellHodgeFirstJet :
    TwoFormFirstDerivative4 :=
  ![!![0, 0, 0, -2;
       0, 0, 0, 0;
       0, 0, 0, 0;
       2, 0, 0, 0],
    (0 : Matrix4),
    !![0, 0, 0, 0;
       0, 0, 0, 0;
       0, 0, 0, -2;
       0, 0, 2, 0],
    (0 : Matrix4)]

/-- The common perturbation is closed. -/
theorem matrixExteriorDerivative_activeAmbiguityCommonMaxwellFirstJet :
    matrixExteriorDerivative activeAmbiguityCommonMaxwellFirstJet = 0 := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrixExteriorDerivative,
      activeAmbiguityCommonMaxwellFirstJet, Fin.ext_iff]

/-- The common perturbation is also co-closed. -/
theorem matrixExteriorDerivative_activeAmbiguityCommonMaxwellHodgeFirstJet :
    matrixExteriorDerivative activeAmbiguityCommonMaxwellHodgeFirstJet = 0 := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrixExteriorDerivative,
      activeAmbiguityCommonMaxwellHodgeFirstJet, Fin.ext_iff]

/-- Coupling-dependent duality shear about the balanced physical field. -/
noncomputable def activeAmbiguityShearComplexionOneForm
    (a : ℝ) : OneForm4 :=
  (-(a / 2)) • canonicalPrincipalReflectionCovector
    activeAmbiguityScalarCovector

/-- Actual physical complexion covector of the active formal Maxwell jet. -/
noncomputable def activeAmbiguityPhysicalComplexionOneForm
    (a : ℝ) : OneForm4 :=
  activeAmbiguityEffectiveOneForm +
    activeAmbiguityShearComplexionOneForm a

/-- Coupling-dependent physical Maxwell first jet: a common active
perturbation plus the stress-invisible infinitesimal duality shear. -/
noncomputable def activeAmbiguityMaxwellFirstJet
    (a : ℝ) : TwoFormFirstDerivative4 :=
  fun k => activeAmbiguityCommonMaxwellFirstJet k +
    (activeAmbiguityShearComplexionOneForm a k) •
      activeAmbiguityMaxwellHodge

/-- Corresponding Hodge first jet at the common normal-coordinate metric
first jet `g_1=0`. -/
noncomputable def activeAmbiguityMaxwellHodgeFirstJet
    (a : ℝ) : TwoFormFirstDerivative4 :=
  fun k => activeAmbiguityCommonMaxwellHodgeFirstJet k +
    (-(activeAmbiguityShearComplexionOneForm a k)) •
      activeAmbiguityMaxwellField

set_option maxHeartbeats 2000000 in
/-- Minkowski Hodge on the full six-component Lorentz two-form. -/
theorem coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew
    (e1 e2 e3 b1 b2 b3 : ℝ) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (lorentzSkewTwoForm4 e1 e2 e3 b1 b2 b3) =
      lorentzSkewTwoForm4 (-b1) (-b2) (-b3) e1 e2 e3 := by
  have hdiag : minkowskiMetric = Matrix.diagonal minkowskiSign := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minkowskiMetric, minkowskiSign]
  have hdet : Matrix.det minkowskiMetric = -1 := by
    rw [hdiag, Matrix.det_diagonal]
    simp [minkowskiSign, Fin.prod_univ_succ]
  have hinv : minkowskiMetric⁻¹ = minkowskiMetric := by
    exact Matrix.inv_eq_right_inv minkowskiMetric_sq
  ext i j
  unfold coordinateMetricHodgeTwoForm4
  rw [hdet, hinv]
  fin_cases i <;> fin_cases j <;>
    simp [leviCivitaSymbol4, lorentzSkewTwoForm4,
      minkowskiMetric, Fin.sum_univ_succ] <;> ring

/-- The common source-free perturbation is Hodge-compatible. -/
theorem activeAmbiguityCommonMaxwellFirstJet_hodgeCompatible
    (k : Fin 4) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (activeAmbiguityCommonMaxwellFirstJet k) =
      activeAmbiguityCommonMaxwellHodgeFirstJet k := by
  fin_cases k
  · simpa [activeAmbiguityCommonMaxwellFirstJet,
      activeAmbiguityCommonMaxwellHodgeFirstJet,
      lorentzSkewTwoForm4] using
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew
        0 0 0 0 0 2
  · change coordinateMetricHodgeTwoForm4 minkowskiMetric 0 = 0
    have hz : (0 : Matrix4) = lorentzSkewTwoForm4 0 0 0 0 0 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lorentzSkewTwoForm4]
    rw [hz]
    simpa using coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew
      0 0 0 0 0 0
  · simpa [activeAmbiguityCommonMaxwellFirstJet,
      activeAmbiguityCommonMaxwellHodgeFirstJet,
      lorentzSkewTwoForm4] using
      coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew
        (-2) 0 0 0 0 0
  · change coordinateMetricHodgeTwoForm4 minkowskiMetric 0 = 0
    have hz : (0 : Matrix4) = lorentzSkewTwoForm4 0 0 0 0 0 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [lorentzSkewTwoForm4]
    rw [hz]
    simpa using coordinateMetricHodgeTwoForm4_minkowski_lorentzSkew
      0 0 0 0 0 0

/-- Minkowski Hodge is additive in the two-form argument. -/
theorem coordinateMetricHodgeTwoForm4_minkowski_add
    (F H : Matrix4) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric (F + H) =
      coordinateMetricHodgeTwoForm4 minkowskiMetric F +
        coordinateMetricHodgeTwoForm4 minkowskiMetric H := by
  rw [coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement,
    coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement,
    coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement]
  ext i j
  simp [alternatingComplement4, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- Minkowski Hodge commutes with scalar multiplication. -/
theorem coordinateMetricHodgeTwoForm4_minkowski_smul
    (r : ℝ) (F : Matrix4) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric (r • F) =
      r • coordinateMetricHodgeTwoForm4 minkowskiMetric F := by
  rw [coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement,
    coordinateMetricHodgeTwoForm4_minkowski_alternatingComplement]
  ext i j
  simp [alternatingComplement4, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- The complete active Maxwell/Hodge first jets are compatible with the
common metric first jet `g_1=0`. -/
theorem activeAmbiguityMaxwellFirstJet_hodgeCompatible
    (a : ℝ) (k : Fin 4) :
    coordinateMetricHodgeTwoForm4 minkowskiMetric
        (activeAmbiguityMaxwellFirstJet a k) =
      activeAmbiguityMaxwellHodgeFirstJet a k := by
  rw [activeAmbiguityMaxwellFirstJet,
    activeAmbiguityMaxwellHodgeFirstJet,
    coordinateMetricHodgeTwoForm4_minkowski_add,
    activeAmbiguityCommonMaxwellFirstJet_hodgeCompatible,
    coordinateMetricHodgeTwoForm4_minkowski_smul,
    coordinateMetricHodgeTwoForm4_activeAmbiguityMaxwellHodge]
  ext i j
  simp

/-- Exterior derivative is additive on directional two-form jets. -/
theorem matrixExteriorDerivative_add
    (D K : TwoFormFirstDerivative4) :
    matrixExteriorDerivative (D + K) =
      matrixExteriorDerivative D + matrixExteriorDerivative K := by
  ext k i j
  simp [matrixExteriorDerivative]
  ring

/-- The active physical Maxwell jet satisfies the first exterior EMD
equation for every coupling. -/
theorem matrixExteriorDerivative_activeAmbiguityMaxwellFirstJet
    (a : ℝ) :
    matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet a) =
      (a / 2) • matrixOneWedgeTwoTensor
        activeAmbiguityScalarCovector activeAmbiguityMaxwellField := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixExteriorDerivative, activeAmbiguityMaxwellFirstJet,
      activeAmbiguityCommonMaxwellFirstJet,
      activeAmbiguityShearComplexionOneForm,
      activeAmbiguityScalarCovector, activeAmbiguityMaxwellField,
      activeAmbiguityMaxwellHodge,
      canonicalPrincipalReflectionCovector, canonicalMaxwellTwoForm,
      matrixOneWedgeTwoTensor]

/-- The active Hodge jet satisfies the second exterior EMD equation for every
coupling. -/
theorem matrixExteriorDerivative_activeAmbiguityMaxwellHodgeFirstJet
    (a : ℝ) :
    matrixExteriorDerivative
        (activeAmbiguityMaxwellHodgeFirstJet a) =
      -(a / 2) • matrixOneWedgeTwoTensor
        activeAmbiguityScalarCovector activeAmbiguityMaxwellHodge := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixExteriorDerivative,
      activeAmbiguityMaxwellHodgeFirstJet,
      activeAmbiguityCommonMaxwellHodgeFirstJet,
      activeAmbiguityShearComplexionOneForm,
      activeAmbiguityScalarCovector, activeAmbiguityMaxwellField,
      activeAmbiguityMaxwellHodge,
      canonicalPrincipalReflectionCovector, canonicalMaxwellTwoForm,
      matrixOneWedgeTwoTensor] <;> ring

/-- Complete exterior EMD realization of the active formal Maxwell jet. -/
theorem activeAmbiguityMaxwellJet_emdExteriorClosure (a : ℝ) :
    EMDExteriorClosure matrixOneWedgeTwo
      activeAmbiguityScalarCovector a
      activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
      (matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet a))
      (matrixExteriorDerivative
        (activeAmbiguityMaxwellHodgeFirstJet a)) := by
  exact ⟨matrixExteriorDerivative_activeAmbiguityMaxwellFirstJet a,
    matrixExteriorDerivative_activeAmbiguityMaxwellHodgeFirstJet a⟩

/-- Fixed-metric first variation of the trace pairing
`trace(G F G H)`. -/
noncomputable def coordinateTwoFormTracePairingFirstVariation
    (G F H dF dH : Matrix4) : ℝ :=
  Matrix.trace (G * dF * G * H + G * F * G * dH)

/-- Raw numerator contribution to the normalized double-angle cosine first
jet.  Since the point cosine is zero, the quotient correction vanishes. -/
noncomputable def activeAmbiguityRawDoubleAngleCosineFirstJet
    (a : ℝ) : OneForm4 :=
  fun k => coordinateTwoFormTracePairingFirstVariation minkowskiMetric
    activeAmbiguityMaxwellField activeAmbiguityMaxwellField
    (activeAmbiguityMaxwellFirstJet a k)
    (activeAmbiguityMaxwellFirstJet a k) / 4

/-- Raw numerator contribution to the normalized double-angle sine first
jet, before differentiating its `1/q` normalization. -/
noncomputable def activeAmbiguityRawDoubleAngleSineFirstJet
    (a : ℝ) : OneForm4 :=
  fun k => -coordinateTwoFormTracePairingFirstVariation minkowskiMetric
    activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
    (activeAmbiguityMaxwellFirstJet a k)
    (activeAmbiguityMaxwellHodgeFirstJet a k) / 4

/-- First jet of the positive Maxwell-stress magnitude `q`, reconstructed
from the `00` mixed-stress component.  The shear contribution vanishes. -/
noncomputable def activeAmbiguityStressMagnitudeFirstJet : OneForm4 :=
  fun k => -(matrixMaxwellStressFirstVariation minkowskiMetric
    activeAmbiguityMaxwellField
    (activeAmbiguityCommonMaxwellFirstJet k) 0 0)

/-- Genuine quotient-corrected first jet of the physical double-angle
cosine `C=N_C/(4q)`.  At the balanced point `C=0`, this equals the raw
numerator contribution. -/
noncomputable def activeAmbiguityDoubleAngleCosineFirstJet
    (a : ℝ) : OneForm4 :=
  activeAmbiguityRawDoubleAngleCosineFirstJet a

/-- Genuine quotient-corrected first jet of the physical double-angle sine
`S=N_S/(4q)`.  At the balanced point `S=1,q=1`, this is the raw numerator
contribution minus `dq`. -/
noncomputable def activeAmbiguityDoubleAngleSineFirstJet
    (a : ℝ) : OneForm4 :=
  activeAmbiguityRawDoubleAngleSineFirstJet a -
    activeAmbiguityStressMagnitudeFirstJet

/-- Choice-free physical double-angle reconstruction applied directly to
the active formal Maxwell first jet. -/
noncomputable def activeAmbiguityPhysicalComplexionFromDoubleAngleJet
    (a : ℝ) : OneForm4 :=
  physicalComplexionOneFormFromDoubleAngle
    (physicalMaxwellDoubleAngleCosine minkowskiMetric
      activeAmbiguityMaxwellField 1)
    (physicalMaxwellDoubleAngleSine minkowskiMetric
      activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge 1)
    (activeAmbiguityDoubleAngleCosineFirstJet a)
    (activeAmbiguityDoubleAngleSineFirstJet a)

set_option maxHeartbeats 1000000 in
/-- The physical double-angle contractions recover exactly the displayed
complexion covector; activity is therefore a property of the Maxwell jet,
not an independently assigned label. -/
theorem activeAmbiguityPhysicalComplexionFromDoubleAngleJet_eq
    (a : ℝ) :
    activeAmbiguityPhysicalComplexionFromDoubleAngleJet a =
      activeAmbiguityPhysicalComplexionOneForm a := by
  funext k
  fin_cases k <;>
    simp [activeAmbiguityPhysicalComplexionFromDoubleAngleJet,
      physicalMaxwellDoubleAngleCosine,
      physicalMaxwellDoubleAngleSine,
      coordinateTwoFormTracePairing,
      activeAmbiguityDoubleAngleCosineFirstJet,
      activeAmbiguityDoubleAngleSineFirstJet,
      activeAmbiguityRawDoubleAngleCosineFirstJet,
      activeAmbiguityRawDoubleAngleSineFirstJet,
      activeAmbiguityStressMagnitudeFirstJet,
      matrixMaxwellStressFirstVariation,
      coordinateTwoFormTracePairingFirstVariation,
      physicalComplexionOneFormFromDoubleAngle,
      activeAmbiguityPhysicalComplexionOneForm,
      activeAmbiguityEffectiveOneForm,
      activeAmbiguityMaxwellFirstJet,
      activeAmbiguityMaxwellHodgeFirstJet,
      activeAmbiguityCommonMaxwellFirstJet,
      activeAmbiguityCommonMaxwellHodgeFirstJet,
      activeAmbiguityShearComplexionOneForm,
      activeAmbiguityScalarCovector,
      activeAmbiguityMaxwellField, activeAmbiguityMaxwellHodge,
      canonicalPrincipalReflectionCovector, canonicalMaxwellTwoForm,
      minkowskiMetric, Matrix.trace,
      Fin.sum_univ_succ] <;> ring

/-- The physically reconstructed complexion is active, uniformly in the
coupling: component `(0,2)` of its wedge with `Jv` is exactly one. -/
theorem activeAmbiguityPhysicalComplexion_wedge_component
    (a : ℝ) :
    oneFormWedgeOneComponent
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet a)
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) 0 2 = 1 := by
  rw [activeAmbiguityPhysicalComplexionFromDoubleAngleJet_eq]
  simp [oneFormWedgeOneComponent,
    activeAmbiguityPhysicalComplexionOneForm,
    activeAmbiguityEffectiveOneForm,
    activeAmbiguityShearComplexionOneForm,
    activeAmbiguityScalarCovector,
    canonicalPrincipalReflectionCovector]

/-- Hence the active-wedge condition holds for every coupling in this
family. -/
theorem activeAmbiguityPhysicalComplexion_covectorWedgeActive
    (a : ℝ) :
    CovectorWedgeActive
      (activeAmbiguityPhysicalComplexionFromDoubleAngleJet a)
      (canonicalPrincipalReflectionCovector
        activeAmbiguityScalarCovector) := by
  refine ⟨0, 2, ?_⟩
  rw [activeAmbiguityPhysicalComplexion_wedge_component]
  norm_num

/-! ## Exact first-channel ambiguity and one-order-later separation -/

/-- The raw first-order channel shared by the whole active ambiguity family.
It has the explicit detector output `A=0` and `eta=e₂`. -/
noncomputable def activeAmbiguityCommonFirstOrderChannels :
    ThreeTensor4 × ThreeTensor4 :=
  canonicalComplexionCouplingChannels (Real.sqrt 2)
    activeAmbiguityScalarCovector activeAmbiguityEffectiveOneForm 0

/-- One fixed finite component choice valid throughout the active family:
source component `0` and wedge component `(0,2)`. -/
def activeAmbiguityFourthOrderChoice : FourthOrderComponentChoice :=
  (0, (0, 2))

/-- The coupling-dependent physical complexion and sine component have the
same effective first-order connection `e₂`.  This is the shear cancellation
that makes the `a=sqrt 3` and `a=1` first channels identical. -/
theorem activeAmbiguityPhysicalEffectiveOneForm_eq
    (a : ℝ) :
    effectiveComplexionOneForm
        (activeAmbiguityPhysicalComplexionOneForm a)
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) a =
      activeAmbiguityEffectiveOneForm := by
  funext i
  fin_cases i <;>
    simp [effectiveComplexionOneForm,
      activeAmbiguityPhysicalComplexionOneForm,
      activeAmbiguityShearComplexionOneForm,
      activeAmbiguityEffectiveOneForm, activeAmbiguityScalarCovector,
      canonicalPrincipalReflectionCovector]

/-- Every coupling in the active family produces exactly the same complete
first-order channel, not merely the same selected components. -/
theorem activeAmbiguityPhysicalSeedChannels_eq_common
    (a : ℝ) :
    canonicalPhysicalSeedChannels (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityPhysicalComplexionOneForm a) 0 a =
      activeAmbiguityCommonFirstOrderChannels := by
  rw [canonicalPhysicalSeedChannels_eq_full]
  unfold canonicalFullComplexionCouplingChannels
    activeAmbiguityCommonFirstOrderChannels
  rw [activeAmbiguityPhysicalEffectiveOneForm_eq]

/-- The common raw channel explicitly reconstructs `eta=e₂`. -/
theorem activeAmbiguityCommonFirstOrderChannels_effective_eq :
    canonicalEffectiveOneFormFromChannels (Real.sqrt 2)
        activeAmbiguityCommonFirstOrderChannels = ![0, 0, 1, 0] := by
  change canonicalEffectiveOneFormFromChannels (Real.sqrt 2)
      activeAmbiguityCommonFirstOrderChannels =
    activeAmbiguityEffectiveOneForm
  apply canonicalEffectiveOneFormFromChannels_eq
    (Real.sqrt 2) (by positivity)
    activeAmbiguityScalarCovector activeAmbiguityEffectiveOneForm 0
    activeAmbiguityCommonFirstOrderChannels
  rfl

/-- The common raw channel explicitly reconstructs the balanced cosine
component `A=0` from the nonzero scalar source component `0`. -/
theorem activeAmbiguityCommonFirstOrderChannels_cosine_eq_zero :
    canonicalCosineCandidateFromChannels (Real.sqrt 2)
        activeAmbiguityScalarCovector
        activeAmbiguityCommonFirstOrderChannels 0 = 0 := by
  apply canonicalCosineCandidateFromChannels_eq
    (Real.sqrt 2) (by positivity)
    activeAmbiguityScalarCovector activeAmbiguityEffectiveOneForm 0
    activeAmbiguityCommonFirstOrderChannels rfl 0
  norm_num [activeAmbiguityScalarCovector]

/-- The active Maxwell field has mixed stress
`diag(-1,-1,1,1)`.  This identifies the principal reflection used below with
the cotangent action of the actual Maxwell stress, rather than an independently
assigned canonical covector. -/
theorem activeAmbiguityMaxwellStress_eq_canonicalResidual :
    matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField =
      canonicalMaxwellResidual 1 := by
  rw [activeAmbiguityMaxwellField, matrixMaxwellStress_canonical]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [canonicalMaxwellStress, canonicalStressMagnitude,
      canonicalMaxwellResidual]

/-- Component `(0,2)` of the physical-complexion wedge with the *actual
Maxwell-stress cotangent action* is one. -/
theorem activeAmbiguityPhysicalComplexion_maxwellStressWedge_component
    (a : ℝ) :
    oneFormWedgeOneComponent
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet a)
        (mixedEndomorphismCovectorAction
          (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
          activeAmbiguityScalarCovector) 0 2 = 1 := by
  rw [activeAmbiguityMaxwellStress_eq_canonicalResidual,
    mixedEndomorphismCovectorAction_canonicalMaxwellResidual]
  simpa using activeAmbiguityPhysicalComplexion_wedge_component a

/-- Activity is therefore derived from the canonical Maxwell stress and the
choice-free physical double-angle jet, uniformly in the coupling. -/
theorem activeAmbiguityPhysicalComplexion_maxwellStressActive
    (a : ℝ) :
    IsCoordinateMaxwellStressActiveWedge
      (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
      (activeAmbiguityPhysicalComplexionFromDoubleAngleJet a)
      activeAmbiguityScalarCovector := by
  unfold IsCoordinateMaxwellStressActiveWedge CovectorWedgeActive
  refine ⟨0, 2, ?_⟩
  rw [activeAmbiguityPhysicalComplexion_maxwellStressWedge_component]
  norm_num

/-- The selected effective-channel wedge denominator is exactly one. -/
theorem activeAmbiguityEffectiveOneForm_wedge_component :
    oneFormWedgeOneComponent activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) 0 2 = 1 := by
  change (0 : ℝ) * 2 - 1 * (-1) = 1
  norm_num

/-- The first jet of the physical double-angle cosine is `-2 omega`. -/
theorem activeAmbiguityDoubleAngleCosineFirstJet_eq
    (a : ℝ) :
    activeAmbiguityDoubleAngleCosineFirstJet a =
      (-2 : ℝ) • activeAmbiguityPhysicalComplexionOneForm a := by
  funext k
  fin_cases k <;>
    simp [activeAmbiguityDoubleAngleCosineFirstJet,
      activeAmbiguityRawDoubleAngleCosineFirstJet,
      coordinateTwoFormTracePairingFirstVariation,
      activeAmbiguityPhysicalComplexionOneForm,
      activeAmbiguityEffectiveOneForm,
      activeAmbiguityMaxwellFirstJet,
      activeAmbiguityCommonMaxwellFirstJet,
      activeAmbiguityShearComplexionOneForm,
      activeAmbiguityScalarCovector, activeAmbiguityMaxwellField,
      activeAmbiguityMaxwellHodge,
      canonicalPrincipalReflectionCovector, canonicalMaxwellTwoForm,
      minkowskiMetric, Matrix.trace, Fin.sum_univ_succ] <;> ring

/-- At the balanced point `A=a C=0`; for constant `a`, its one-order-later
derivative is `dA=a dC`. -/
noncomputable def activeAmbiguityCosineCouplingFirstDerivative
    (a : ℝ) : OneForm4 :=
  a • activeAmbiguityDoubleAngleCosineFirstJet a

/-- The displayed derivative obeys the constant-coupling identity
`dA=-2a omega`. -/
theorem activeAmbiguityCosineCouplingFirstDerivative_eq
    (a : ℝ) :
    activeAmbiguityCosineCouplingFirstDerivative a =
      (-2 * a) • activeAmbiguityPhysicalComplexionOneForm a := by
  rw [activeAmbiguityCosineCouplingFirstDerivative,
    activeAmbiguityDoubleAngleCosineFirstJet_eq, smul_smul]
  congr 1
  ring

/-- The one-order-later constant-coupling equation holds with hidden sine
component `B=a`. -/
theorem activeAmbiguityNextOrderSineCouplingEquation
    (a : ℝ) :
    nextOrderSineCouplingEquation
        (activeAmbiguityCosineCouplingFirstDerivative a)
        activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) a = 0 := by
  apply nextOrderSineCouplingEquation_eq_zero
    (activeAmbiguityCosineCouplingFirstDerivative a)
    activeAmbiguityEffectiveOneForm
    (canonicalPrincipalReflectionCovector activeAmbiguityScalarCovector)
    (activeAmbiguityPhysicalComplexionOneForm a) a
  · exact activeAmbiguityCosineCouplingFirstDerivative_eq a
  · exact (activeAmbiguityPhysicalEffectiveOneForm_eq a).symm

/-- The explicit nondegenerate quotient at component `(0,2)` recovers the
formerly hidden signed sine component exactly: `B=a`. -/
theorem activeAmbiguityNextOrderSineQuotient_eq
    (a : ℝ) :
    sineCouplingFromNextOrderComponent
        (activeAmbiguityCosineCouplingFirstDerivative a)
        activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) 0 2 = a := by
  apply sineCouplingFromNextOrderComponent_eq _ _ _ a
    (activeAmbiguityNextOrderSineCouplingEquation a)
  rw [activeAmbiguityEffectiveOneForm_wedge_component]
  norm_num

/-- The fixed finite component choice is accepted for every member of the
formal active family. -/
theorem activeAmbiguityFourthOrderChannelCandidate
    (a : ℝ) :
    IsFourthOrderChannelCandidate (Real.sqrt 2)
      activeAmbiguityScalarCovector
      (activeAmbiguityCosineCouplingFirstDerivative a)
      activeAmbiguityCommonFirstOrderChannels
      activeAmbiguityFourthOrderChoice := by
  unfold activeAmbiguityFourthOrderChoice
  apply isFourthOrderChannelCandidate_of_compatible
    (Real.sqrt 2) (by positivity)
    activeAmbiguityScalarCovector activeAmbiguityEffectiveOneForm
    (activeAmbiguityCosineCouplingFirstDerivative a) 0 a
    activeAmbiguityCommonFirstOrderChannels rfl 0 0 2
  · norm_num [activeAmbiguityScalarCovector]
  · exact activeAmbiguityNextOrderSineCouplingEquation a
  · rw [activeAmbiguityEffectiveOneForm_wedge_component]
    norm_num

/-- Although the first-order channel is common, the complete fourth-order
constructor returns the physical square `a²`. -/
theorem activeAmbiguityFourthOrderCouplingSqCandidate_eq
    (a : ℝ) :
    fourthOrderCouplingSqCandidate (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityCosineCouplingFirstDerivative a)
        activeAmbiguityCommonFirstOrderChannels
        activeAmbiguityFourthOrderChoice = a ^ 2 := by
  unfold fourthOrderCouplingSqCandidate fourthOrderSineCandidate
    activeAmbiguityFourthOrderChoice
  rw [activeAmbiguityCommonFirstOrderChannels_cosine_eq_zero,
    show canonicalEffectiveOneFormFromChannels (Real.sqrt 2)
        activeAmbiguityCommonFirstOrderChannels =
        activeAmbiguityEffectiveOneForm by
      simpa [activeAmbiguityEffectiveOneForm] using
        activeAmbiguityCommonFirstOrderChannels_effective_eq,
    activeAmbiguityNextOrderSineQuotient_eq]
  simp [couplingSqFromDoubleAngleComponents]

/-- **Exact finite-jet separation package.**  The Kaluza coupling
`a=sqrt 3` and control coupling `a=1` have the same *complete* first-order
channel with `(A,eta)=(0,e₂)`.  Their physical double-angle jets are active
under the actual Maxwell-stress action.  One order later the exact equation
and quotient recover `B=sqrt 3` versus `B=1`, so the squared-coupling detector
outputs `3` versus `1`. -/
theorem activeAmbiguity_kaluza_vs_one_firstChannel_ambiguous_nextOrder_separates :
    canonicalPhysicalSeedChannels (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityPhysicalComplexionOneForm (Real.sqrt 3))
        0 (Real.sqrt 3) = activeAmbiguityCommonFirstOrderChannels ∧
      canonicalPhysicalSeedChannels (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityPhysicalComplexionOneForm 1) 0 1 =
          activeAmbiguityCommonFirstOrderChannels ∧
      canonicalEffectiveOneFormFromChannels (Real.sqrt 2)
          activeAmbiguityCommonFirstOrderChannels = ![0, 0, 1, 0] ∧
      canonicalCosineCandidateFromChannels (Real.sqrt 2)
          activeAmbiguityScalarCovector
          activeAmbiguityCommonFirstOrderChannels 0 = 0 ∧
      IsCoordinateMaxwellStressActiveWedge
        (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet (Real.sqrt 3))
        activeAmbiguityScalarCovector ∧
      IsCoordinateMaxwellStressActiveWedge
        (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet 1)
        activeAmbiguityScalarCovector ∧
      nextOrderSineCouplingEquation
        (activeAmbiguityCosineCouplingFirstDerivative (Real.sqrt 3))
        activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector activeAmbiguityScalarCovector)
        (Real.sqrt 3) = 0 ∧
      nextOrderSineCouplingEquation
        (activeAmbiguityCosineCouplingFirstDerivative 1)
        activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector activeAmbiguityScalarCovector)
        1 = 0 ∧
      sineCouplingFromNextOrderComponent
        (activeAmbiguityCosineCouplingFirstDerivative (Real.sqrt 3))
        activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector activeAmbiguityScalarCovector)
        0 2 = Real.sqrt 3 ∧
      sineCouplingFromNextOrderComponent
        (activeAmbiguityCosineCouplingFirstDerivative 1)
        activeAmbiguityEffectiveOneForm
        (canonicalPrincipalReflectionCovector activeAmbiguityScalarCovector)
        0 2 = 1 ∧
      fourthOrderCouplingSqCandidate (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityCosineCouplingFirstDerivative (Real.sqrt 3))
        activeAmbiguityCommonFirstOrderChannels
        activeAmbiguityFourthOrderChoice = 3 ∧
      fourthOrderCouplingSqCandidate (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityCosineCouplingFirstDerivative 1)
        activeAmbiguityCommonFirstOrderChannels
        activeAmbiguityFourthOrderChoice = 1 := by
  refine ⟨activeAmbiguityPhysicalSeedChannels_eq_common _,
    activeAmbiguityPhysicalSeedChannels_eq_common _,
    activeAmbiguityCommonFirstOrderChannels_effective_eq,
    activeAmbiguityCommonFirstOrderChannels_cosine_eq_zero,
    activeAmbiguityPhysicalComplexion_maxwellStressActive _,
    activeAmbiguityPhysicalComplexion_maxwellStressActive _,
    activeAmbiguityNextOrderSineCouplingEquation _,
    activeAmbiguityNextOrderSineCouplingEquation _,
    activeAmbiguityNextOrderSineQuotient_eq _,
    activeAmbiguityNextOrderSineQuotient_eq _, ?_, ?_⟩
  · exact (activeAmbiguityFourthOrderCouplingSqCandidate_eq
      (Real.sqrt 3)).trans (Real.sq_sqrt (by norm_num))
  · simpa using activeAmbiguityFourthOrderCouplingSqCandidate_eq 1

/-- Common mixed Maxwell-stress first jet induced by the active perturbation. -/
noncomputable def activeAmbiguityCommonMaxwellStressFirstJet :
    Fin 4 → Matrix4 :=
  fun k => matrixMaxwellStressFirstVariation minkowskiMetric
    activeAmbiguityMaxwellField
    (activeAmbiguityCommonMaxwellFirstJet k)

/-- Full mixed Ricci-source first jet for coupling `a`, with common scalar
Hessian zero. -/
noncomputable def activeAmbiguityRicciSourceFirstJet
    (a : ℝ) : Fin 4 → Matrix4 :=
  fun k => matrixMaxwellStressFirstVariation minkowskiMetric
    activeAmbiguityMaxwellField (activeAmbiguityMaxwellFirstJet a k)

/-- Maxwell-stress first variation is additive in the varying two-form. -/
theorem matrixMaxwellStressFirstVariation_add
    (G F D K : Matrix4) :
    matrixMaxwellStressFirstVariation G F (D + K) =
      matrixMaxwellStressFirstVariation G F D +
        matrixMaxwellStressFirstVariation G F K := by
  ext i j
  simp [matrixMaxwellStressFirstVariation, Matrix.mul_apply,
    Matrix.trace, Fin.sum_univ_succ]
  ring

/-- Maxwell-stress first variation is homogeneous in the varying two-form. -/
theorem matrixMaxwellStressFirstVariation_smul
    (G F D : Matrix4) (r : ℝ) :
    matrixMaxwellStressFirstVariation G F (r • D) =
      r • matrixMaxwellStressFirstVariation G F D := by
  ext i j
  simp [matrixMaxwellStressFirstVariation, Matrix.mul_apply,
    Matrix.trace, Fin.sum_univ_succ]
  ring

/-- Infinitesimal duality rotation of the active balanced field is in the
exact Maxwell-stress kernel. -/
theorem matrixMaxwellStressFirstVariation_activeHodge_eq_zero :
    matrixMaxwellStressFirstVariation minkowskiMetric
      activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixMaxwellStressFirstVariation,
      activeAmbiguityMaxwellField, activeAmbiguityMaxwellHodge,
      canonicalMaxwellTwoForm, minkowskiMetric,
      Matrix.trace, Fin.sum_univ_succ]

/-- The coupling-dependent duality shear is in the stress kernel, so the
complete Ricci-source first jet is the same for every coupling. -/
theorem activeAmbiguityRicciSourceFirstJet_eq_common
    (a : ℝ) :
    activeAmbiguityRicciSourceFirstJet a =
      activeAmbiguityCommonMaxwellStressFirstJet := by
  funext k
  rw [activeAmbiguityRicciSourceFirstJet,
    activeAmbiguityCommonMaxwellStressFirstJet,
    activeAmbiguityMaxwellFirstJet,
    matrixMaxwellStressFirstVariation_add,
    matrixMaxwellStressFirstVariation_smul,
    matrixMaxwellStressFirstVariation_activeHodge_eq_zero]
  simp

/-- Point mixed Ricci source of the active ambiguity. -/
noncomputable def activeAmbiguityRicciSource : Matrix4 :=
  matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField +
    balancedCanonicalScalarRicciSource activeAmbiguityScalarCovector

/-- Covariant form of the common point Ricci source. -/
noncomputable def activeAmbiguityCovariantRicciSource : Matrix4 :=
  minkowskiMetric * activeAmbiguityRicciSource

/-- The active covariant Ricci source is symmetric. -/
theorem activeAmbiguityCovariantRicciSource_transpose :
    activeAmbiguityCovariantRicciSourceᵀ =
      activeAmbiguityCovariantRicciSource := by
  rw [activeAmbiguityCovariantRicciSource,
    activeAmbiguityRicciSource, activeAmbiguityMaxwellField,
    matrixMaxwellStress_canonical]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedCanonicalScalarRicciSource,
      activeAmbiguityScalarCovector, canonicalMaxwellStress,
      canonicalStressMagnitude, minkowskiMetric, Matrix.mul_apply,
      Matrix.vecMul_apply, Matrix.vecMul_apply_eq_sum, dotProduct,
      Fin.sum_univ_succ]

/-- Covariant common Ricci-source first jet.  Metric lowering contributes no
extra term because the common metric first jet is zero. -/
noncomputable def activeAmbiguityCommonCovariantRicciSourceFirstJet :
    Fin 4 → Matrix4 :=
  fun r => minkowskiMetric * activeAmbiguityCommonMaxwellStressFirstJet r

/-- Explicit fully symmetric metric third jet realizing the common active
Ricci-source derivative.  Conditions on derivative slots encode the four
nonzero symmetric multi-indices `000`, `002`, and `112`. -/
def activeAmbiguityFormalMetricJet3 :
    CoordinateMetricJet3 (Fin 4) :=
  fun r s t i j =>
    if r = 0 ∧ s = 0 ∧ t = 0 ∧
        ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) then -4
    else if
        ((r = 0 ∧ s = 0 ∧ t = 2) ∨
          (r = 0 ∧ s = 2 ∧ t = 0) ∨
          (r = 2 ∧ s = 0 ∧ t = 0)) ∧ i = 1 ∧ j = 1 then 8
    else if
        ((r = 0 ∧ s = 0 ∧ t = 2) ∨
          (r = 0 ∧ s = 2 ∧ t = 0) ∨
          (r = 2 ∧ s = 0 ∧ t = 0)) ∧ i = 3 ∧ j = 3 then -4
    else if
        ((r = 1 ∧ s = 1 ∧ t = 2) ∨
          (r = 1 ∧ s = 2 ∧ t = 1) ∨
          (r = 2 ∧ s = 1 ∧ t = 1)) ∧ i = 2 ∧ j = 2 then 4
    else 0

set_option maxHeartbeats 2000000 in
/-- The explicit third jet has fully commuting derivative slots and symmetric
metric slots. -/
theorem activeAmbiguityFormalMetricJet3_symmetries
    (r s t i j : Fin 4) :
    activeAmbiguityFormalMetricJet3 r s t i j =
        activeAmbiguityFormalMetricJet3 s r t i j ∧
      activeAmbiguityFormalMetricJet3 r s t i j =
        activeAmbiguityFormalMetricJet3 r t s i j ∧
      activeAmbiguityFormalMetricJet3 r s t i j =
        activeAmbiguityFormalMetricJet3 r s t j i := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;>
    fin_cases i <;> fin_cases j <;>
      norm_num [activeAmbiguityFormalMetricJet3, Fin.ext_iff]

set_option maxHeartbeats 2000000 in
/-- The explicit common metric third jet realizes the complete common
covariant Ricci-source first jet. -/
theorem activeAmbiguityFormalMetricJet3_einsteinFirstProlongation
    (r n p : Fin 4) :
    coordinateRicciFirstJet minkowskiMetric 0
        activeAmbiguityFormalMetricJet2
        activeAmbiguityFormalMetricJet3 r n p =
      activeAmbiguityCommonCovariantRicciSourceFirstJet r n p := by
  rw [coordinateRicciFirstJet_minkowski_zero]
  fin_cases r <;> fin_cases n <;> fin_cases p <;>
    simp [normalFrameBaseRicci,
      activeAmbiguityFormalMetricJet3,
      activeAmbiguityCommonCovariantRicciSourceFirstJet,
      activeAmbiguityCommonMaxwellStressFirstJet,
      matrixMaxwellStressFirstVariation,
      activeAmbiguityCommonMaxwellFirstJet,
      activeAmbiguityMaxwellField, canonicalMaxwellTwoForm,
      minkowskiMetric, minkowskiSign, Matrix.mul_apply,
      Matrix.trace, Matrix.one_apply,
      Fin.sum_univ_succ] <;> ring

/-- Common metric second jet realizing the active point Ricci source. -/
noncomputable def activeAmbiguityFormalMetricJet2 :
    CoordinateMetricJet2 (Fin 4) :=
  normalCoordinateMetricJet2OfRicci activeAmbiguityCovariantRicciSource

/-- Einstein equation for the common active metric second jet. -/
theorem activeAmbiguityFormalMetricJet2_einsteinEquation
    (n p : Fin 4) :
    normalFrameBaseRicci minkowskiSign activeAmbiguityFormalMetricJet2 n p =
      activeAmbiguityCovariantRicciSource n p := by
  exact normalFrameBaseRicci_normalCoordinateMetricJet2OfRicci _
    activeAmbiguityCovariantRicciSource_transpose n p

/-- The active balanced field has zero quadratic invariant. -/
theorem activeAmbiguityMaxwell_quadraticInvariant_eq_zero :
    Matrix.trace
      (minkowskiMetric * activeAmbiguityMaxwellField *
        minkowskiMetric * activeAmbiguityMaxwellField) = 0 := by
  norm_num [activeAmbiguityMaxwellField, canonicalMaxwellTwoForm,
    minkowskiMetric, Matrix.trace, Fin.sum_univ_succ]

/-- The common zero scalar Hessian satisfies the scalar point equation for
every coupling in the active family. -/
theorem genericEMDScalarJetResidual_activeAmbiguity_eq_zero
    (a : ℝ) :
    genericEMDScalarJetResidual a 0 activeAmbiguityMaxwellField = 0 := by
  unfold genericEMDScalarJetResidual normalFrameScalarBox
  rw [activeAmbiguityMaxwell_quadraticInvariant_eq_zero]
  simp

/-- The coupling is faithfully recorded in the matter first jet even though
it is absent from the common formal metric three-jet. -/
theorem activeAmbiguityMaxwellFirstJet_injective :
    Function.Injective activeAmbiguityMaxwellFirstJet := by
  intro a b hab
  have hentry := congrArg
    (fun D : TwoFormFirstDerivative4 => D 0 0 1) hab
  simp [activeAmbiguityMaxwellFirstJet,
    activeAmbiguityCommonMaxwellFirstJet,
    activeAmbiguityShearComplexionOneForm,
    activeAmbiguityScalarCovector, activeAmbiguityMaxwellHodge,
    canonicalPrincipalReflectionCovector, canonicalMaxwellTwoForm] at hentry
  linarith

/-- **A continuum of active couplings over one formal metric three-jet.**
For every real coupling `a`, the same fixed normal-coordinate metric jets
`g₀=eta`, `g₁=0`, `activeAmbiguityFormalMetricJet2`, and
`activeAmbiguityFormalMetricJet3` support the displayed truncated EMD data.
The physical matter jet is active and satisfies the point equations and first
Einstein/Ricci prolongation.  Its complete first channel is the common
`(A,eta)=(0,e₂)` channel, while the next-order finite detector returns `a²`.

This is a finite formal-jet statement, not an all-order integrability or local
PDE-existence theorem. -/
theorem activeAmbiguity_commonFormalMetricThreeJet_for_every_coupling
    (a : ℝ) :
    IsCoordinateMaxwellStressActiveWedge
        (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet a)
        activeAmbiguityScalarCovector ∧
      (∀ r s i j,
        activeAmbiguityFormalMetricJet2 r s i j =
            activeAmbiguityFormalMetricJet2 s r i j ∧
          activeAmbiguityFormalMetricJet2 r s i j =
            activeAmbiguityFormalMetricJet2 r s j i) ∧
      (∀ r s t i j,
        activeAmbiguityFormalMetricJet3 r s t i j =
            activeAmbiguityFormalMetricJet3 s r t i j ∧
          activeAmbiguityFormalMetricJet3 r s t i j =
            activeAmbiguityFormalMetricJet3 r t s i j ∧
          activeAmbiguityFormalMetricJet3 r s t i j =
            activeAmbiguityFormalMetricJet3 r s t j i) ∧
      (∀ n p,
        normalFrameBaseRicci minkowskiSign
            activeAmbiguityFormalMetricJet2 n p =
          activeAmbiguityCovariantRicciSource n p) ∧
      (∀ r n p,
        coordinateRicciFirstJet minkowskiMetric 0
            activeAmbiguityFormalMetricJet2
            activeAmbiguityFormalMetricJet3 r n p =
          (minkowskiMetric * activeAmbiguityRicciSourceFirstJet a r) n p) ∧
      coordinateMetricHodgeTwoForm4 minkowskiMetric
          activeAmbiguityMaxwellField = activeAmbiguityMaxwellHodge ∧
      (∀ k,
        coordinateMetricHodgeTwoForm4 minkowskiMetric
            (activeAmbiguityMaxwellFirstJet a k) =
          activeAmbiguityMaxwellHodgeFirstJet a k) ∧
      EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector a
        activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
        (matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet a))
        (matrixExteriorDerivative
          (activeAmbiguityMaxwellHodgeFirstJet a)) ∧
      genericEMDScalarJetResidual a 0 activeAmbiguityMaxwellField = 0 ∧
      canonicalPhysicalSeedChannels (Real.sqrt 2)
          activeAmbiguityScalarCovector
          (activeAmbiguityPhysicalComplexionOneForm a) 0 a =
        activeAmbiguityCommonFirstOrderChannels ∧
      IsFourthOrderChannelCandidate (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityCosineCouplingFirstDerivative a)
        activeAmbiguityCommonFirstOrderChannels
        activeAmbiguityFourthOrderChoice ∧
      fourthOrderCouplingSqCandidate (Real.sqrt 2)
        activeAmbiguityScalarCovector
        (activeAmbiguityCosineCouplingFirstDerivative a)
        activeAmbiguityCommonFirstOrderChannels
        activeAmbiguityFourthOrderChoice = a ^ 2 := by
  refine ⟨activeAmbiguityPhysicalComplexion_maxwellStressActive a, ?_,
    activeAmbiguityFormalMetricJet3_symmetries, ?_, ?_,
    coordinateMetricHodgeTwoForm4_activeAmbiguityMaxwellField,
    activeAmbiguityMaxwellFirstJet_hodgeCompatible a,
    activeAmbiguityMaxwellJet_emdExteriorClosure a,
    genericEMDScalarJetResidual_activeAmbiguity_eq_zero a,
    activeAmbiguityPhysicalSeedChannels_eq_common a,
    activeAmbiguityFourthOrderChannelCandidate a,
    activeAmbiguityFourthOrderCouplingSqCandidate_eq a⟩
  · intro r s i j
    exact ⟨normalCoordinateMetricJet2OfRicci_deriv_symm _
        activeAmbiguityCovariantRicciSource_transpose r s i j,
      normalCoordinateMetricJet2OfRicci_metric_symm _ r s i j⟩
  · exact activeAmbiguityFormalMetricJet2_einsteinEquation
  · intro r n p
    rw [activeAmbiguityRicciSourceFirstJet_eq_common]
    exact activeAmbiguityFormalMetricJet3_einsteinFirstProlongation r n p

/-- The Kaluza coupling and the non-Kaluza control produce genuinely
different physical Maxwell first jets. -/
theorem activeAmbiguityMaxwellFirstJet_sqrtThree_ne_one :
    activeAmbiguityMaxwellFirstJet (Real.sqrt 3) ≠
      activeAmbiguityMaxwellFirstJet 1 := by
  intro h
  have hentry := congrArg
    (fun D : TwoFormFirstDerivative4 => D 0 0 1) h
  have hsqrtSq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNe : Real.sqrt 3 ≠ 1 := by
    intro hs
    rw [hs] at hsqrtSq
    norm_num at hsqrtSq
  apply hsqrtNe
  simp [activeAmbiguityMaxwellFirstJet,
    activeAmbiguityCommonMaxwellFirstJet,
    activeAmbiguityShearComplexionOneForm,
    activeAmbiguityScalarCovector, activeAmbiguityMaxwellHodge,
    canonicalPrincipalReflectionCovector, canonicalMaxwellTwoForm] at hentry
  linarith

/-- **Active formal metric-three-jet ambiguity at the Kaluza coupling.**
The Kaluza value `a=sqrt 3` and the non-Kaluza value `a=1` have distinct
coupling squares and distinct physically active Maxwell first jets, but share
one explicit formal normal-coordinate metric three-jet.  Both satisfy the
Einstein equation and its first prolongation, point/first-jet Hodge
compatibility, both exterior EMD equations, and the scalar point equation.

This remains a finite formal-jet theorem; it does not assert all-order formal
integrability or existence of two local EMD solutions. -/
theorem exists_activeCommonFormalMetricThreeJet_kaluza_vs_one :
    (Real.sqrt 3) ^ 2 ≠ (1 : ℝ) ^ 2 ∧
      activeAmbiguityMaxwellFirstJet (Real.sqrt 3) ≠
        activeAmbiguityMaxwellFirstJet 1 ∧
      CovectorWedgeActive
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet
          (Real.sqrt 3))
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) ∧
      CovectorWedgeActive
        (activeAmbiguityPhysicalComplexionFromDoubleAngleJet 1)
        (canonicalPrincipalReflectionCovector
          activeAmbiguityScalarCovector) ∧
      (∀ r s i j,
        activeAmbiguityFormalMetricJet2 r s i j =
            activeAmbiguityFormalMetricJet2 s r i j ∧
          activeAmbiguityFormalMetricJet2 r s i j =
            activeAmbiguityFormalMetricJet2 r s j i) ∧
      (∀ r s t i j,
        activeAmbiguityFormalMetricJet3 r s t i j =
            activeAmbiguityFormalMetricJet3 s r t i j ∧
          activeAmbiguityFormalMetricJet3 r s t i j =
            activeAmbiguityFormalMetricJet3 r t s i j ∧
          activeAmbiguityFormalMetricJet3 r s t i j =
            activeAmbiguityFormalMetricJet3 r s t j i) ∧
      (∀ n p,
        normalFrameBaseRicci minkowskiSign
            activeAmbiguityFormalMetricJet2 n p =
          activeAmbiguityCovariantRicciSource n p) ∧
      (∀ a ∈ ({Real.sqrt 3, 1} : Set ℝ), ∀ r n p,
        coordinateRicciFirstJet minkowskiMetric 0
            activeAmbiguityFormalMetricJet2
            activeAmbiguityFormalMetricJet3 r n p =
          (minkowskiMetric * activeAmbiguityRicciSourceFirstJet a r) n p) ∧
      coordinateMetricHodgeTwoForm4 minkowskiMetric
          activeAmbiguityMaxwellField = activeAmbiguityMaxwellHodge ∧
      (∀ a ∈ ({Real.sqrt 3, 1} : Set ℝ), ∀ k,
        coordinateMetricHodgeTwoForm4 minkowskiMetric
            (activeAmbiguityMaxwellFirstJet a k) =
          activeAmbiguityMaxwellHodgeFirstJet a k) ∧
      EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector
        (Real.sqrt 3) activeAmbiguityMaxwellField
        activeAmbiguityMaxwellHodge
        (matrixExteriorDerivative
          (activeAmbiguityMaxwellFirstJet (Real.sqrt 3)))
        (matrixExteriorDerivative
          (activeAmbiguityMaxwellHodgeFirstJet (Real.sqrt 3))) ∧
      EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector
        1 activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
        (matrixExteriorDerivative (activeAmbiguityMaxwellFirstJet 1))
        (matrixExteriorDerivative
          (activeAmbiguityMaxwellHodgeFirstJet 1)) ∧
      genericEMDScalarJetResidual (Real.sqrt 3) 0
          activeAmbiguityMaxwellField = 0 ∧
      genericEMDScalarJetResidual 1 0 activeAmbiguityMaxwellField = 0 := by
  have hsqrtSq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  refine ⟨?_, activeAmbiguityMaxwellFirstJet_sqrtThree_ne_one,
    activeAmbiguityPhysicalComplexion_covectorWedgeActive _,
    activeAmbiguityPhysicalComplexion_covectorWedgeActive _, ?_, ?_, ?_,
    ?_, coordinateMetricHodgeTwoForm4_activeAmbiguityMaxwellField, ?_,
    activeAmbiguityMaxwellJet_emdExteriorClosure _,
    activeAmbiguityMaxwellJet_emdExteriorClosure _,
    genericEMDScalarJetResidual_activeAmbiguity_eq_zero _,
    genericEMDScalarJetResidual_activeAmbiguity_eq_zero _⟩
  · rw [hsqrtSq]
    norm_num
  · intro r s i j
    exact ⟨normalCoordinateMetricJet2OfRicci_deriv_symm _
        activeAmbiguityCovariantRicciSource_transpose r s i j,
      normalCoordinateMetricJet2OfRicci_metric_symm _ r s i j⟩
  · exact activeAmbiguityFormalMetricJet3_symmetries
  · exact activeAmbiguityFormalMetricJet2_einsteinEquation
  · intro a ha r n p
    rw [activeAmbiguityRicciSourceFirstJet_eq_common]
    exact activeAmbiguityFormalMetricJet3_einsteinFirstProlongation r n p
  · intro a ha k
    exact activeAmbiguityMaxwellFirstJet_hodgeCompatible a k

end RainichKaluza
