import RainichKaluza.KaluzaRicciMixed

/-!
# The base Kaluza Ricci block

This file completes the normal-gauge coordinate Ricci calculation by reducing
the base--base block to the four-dimensional Einstein equation.
-/

namespace RainichKaluza

open Matrix

/-- Four-dimensional Ricci tensor in a diagonal normal frame, expressed using
the second metric jet. -/
noncomputable def normalFrameBaseRicci
    (d : Fin 4 → ℝ) (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (n p : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ m : Fin 4, (d m)⁻¹ *
    (g2 m n m p + g2 m p m n - g2 m m n p - g2 n p m m)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- **Base--base Ricci block.** For genuine symmetric second jets, the raw
five-dimensional Ricci contraction splits into the base Ricci tensor, scalar
warp terms, and the Maxwell quadratic term. -/
theorem kaluzaNormalGaugeRicci_base_base
    (u v c k₁ k₂ : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu)
    (n p : Fin 4) :
    kaluzaNormalGaugeRicci u v c k₁ k₂ d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inl p) =
      normalFrameBaseRicci d g2 n p -
        (k₁ + k₂ / 2) * phi2 n p -
        (k₁ / 2) * Matrix.diagonal d n p *
          (∑ m : Fin 4, (d m)⁻¹ * phi2 m m) +
        (k₁ ^ 2 / 2 + k₁ * k₂ / 2 - k₂ ^ 2 / 4) *
          phi1 n * phi1 p -
        (k₁ ^ 2 / 2 + k₁ * k₂ / 4) * Matrix.diagonal d n p *
          (∑ m : Fin 4, (d m)⁻¹ * phi1 m * phi1 m) -
        (v * c ^ 2 * u⁻¹ / 2) *
          (∑ q : Fin 4, (d q)⁻¹ *
            (A1 n q - A1 q n) * (A1 p q - A1 q p)) := by
  unfold kaluzaNormalGaugeRicci normalFrameBaseRicci
  fin_cases n <;> fin_cases p <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_four,
      kaluzaNormalGaugeChristoffelJet, kaluzaNormalGaugeChristoffelFirstKindJet,
      kaluzaNormalGaugeChristoffelFirstKind,
      kaluzaNormalGaugeInverseJet, kaluzaNormalGaugePointInverse,
      kaluzaNormalGaugeDoubleJet, kaluzaNormalGaugeMetricJet2,
      kaluzaNormalGaugeMetricJet, kaluzaNormalGaugeChristoffel,
      Matrix.diagonal_apply, hg2metric,
      hphi2 0 1, hphi2 0 2, hphi2 0 3, hphi2 1 2, hphi2 1 3, hphi2 2 3,
      hg2deriv 0 1, hg2deriv 0 2, hg2deriv 0 3,
      hg2deriv 1 2, hg2deriv 1 3, hg2deriv 2 3] <;>
    field_simp [hu, hv, hd] <;>
    ring

/-- Scalar d'Alembertian in a diagonal normal frame. -/
noncomputable def normalFrameScalarBox
    (d : Fin 4 → ℝ) (phi2 : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ m : Fin 4, (d m)⁻¹ * phi2 m m

/-- The contraction `F_{nq}F_p{}^q` in a diagonal normal frame, with
`F_{nq}=A1 n q-A1 q n`. -/
noncomputable def normalFrameMaxwellContraction
    (d : Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (n p : Fin 4) : ℝ :=
  ∑ q : Fin 4, (d q)⁻¹ *
    (A1 n q - A1 q n) * (A1 p q - A1 q p)

/-- The contraction `F_{mq}F^{mq}` in a diagonal normal frame. -/
noncomputable def normalFrameMaxwellNormSq
    (d : Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ m : Fin 4, ∑ q : Fin 4, (d m)⁻¹ * (d q)⁻¹ *
    ((A1 m q - A1 q m) * (A1 m q - A1 q m))

/-- Convention-fixed trace-reversed Einstein-equation residual in a diagonal
normal frame:

`R_np - 1/2 ∂_nφ∂_pφ - e^(√3φ)/2 (F_nq F_p{}^q - g_np F²/4)`. -/
noncomputable def conventionEinsteinEquationResidual
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (A1 : Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (n p : Fin 4) : ℝ :=
  normalFrameBaseRicci d g2 n p - phi1 n * phi1 p / 2 -
    Real.exp (Real.sqrt 3 * phi0) / 2 *
      (normalFrameMaxwellContraction d A1 n p -
        Matrix.diagonal d n p * normalFrameMaxwellNormSq d A1 / 4)

/-- At the derived Kaluza convention, the base--base Ricci block is the
four-dimensional Ricci tensor plus the scalar and Maxwell terms with their
exact EMD coefficients. -/
theorem conventionKaluzaRicci_base_base
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu)
    (n p : Fin 4) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inl p) =
      normalFrameBaseRicci d g2 n p +
        (Real.sqrt 3)⁻¹ / 2 * Matrix.diagonal d n p *
          normalFrameScalarBox d phi2 -
        phi1 n * phi1 p / 2 -
        Real.exp (Real.sqrt 3 * phi0) / 2 *
          normalFrameMaxwellContraction d A1 n p := by
  rw [kaluzaNormalGaugeRicci_base_base _ _ _ _ _ d phi1 phi2 A1 A2 g2
    (kaluzaBaseWarp_ne_zero phi0) (kaluzaFiberWarp_ne_zero phi0) hd
    hphi2 hg2deriv hg2metric n p]
  have hframe := kaluzaWarpExponents_einsteinFrame
  have hsum := kaluzaWarpExponents_conformal_sum
  have hsq := kaluzaBaseWarpExponent_sq
  have hratio := conventionKaluzaWarpRatio phi0
  have hphi :
      kaluzaBaseWarpExponent ^ 2 / 2 +
          kaluzaBaseWarpExponent * kaluzaFiberWarpExponent / 2 -
          kaluzaFiberWarpExponent ^ 2 / 4 = -(1 / 2 : ℝ) := by
    rw [hframe]
    ring_nf
    rw [hsq]
    norm_num
  have hgrad :
      kaluzaBaseWarpExponent ^ 2 / 2 +
          kaluzaBaseWarpExponent * kaluzaFiberWarpExponent / 4 = 0 := by
    rw [hframe]
    ring
  have hbox : -kaluzaBaseWarpExponent / 2 = (Real.sqrt 3)⁻¹ / 2 := by
    unfold kaluzaBaseWarpExponent
    ring
  have hmax :
      kaluzaFiberWarp phi0 * kaluzaGaugeNormalization ^ 2 *
          (kaluzaBaseWarp phi0)⁻¹ / 2 =
        Real.exp (Real.sqrt 3 * phi0) / 2 := by
    unfold kaluzaGaugeNormalization
    linear_combination hratio / 2
  unfold normalFrameScalarBox normalFrameMaxwellContraction
  rw [hsum, hphi, hgrad, hmax]
  linear_combination
    (Matrix.diagonal d n p *
      (∑ m : Fin 4, (d m)⁻¹ * phi2 m m)) * hbox

/-- **Triangular reduction identity.** The convention-fixed base Ricci block
is exactly the four-dimensional Einstein residual plus
`g_np/(2√3)` times the scalar residual.  Thus the fifth diagonal equation
supplies precisely the trace correction needed by the base equation. -/
theorem conventionKaluzaRicci_base_base_eq_einstein_add_scalar
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu)
    (n p : Fin 4) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inl p) =
      conventionEinsteinEquationResidual phi0 d phi1 A1 g2 n p +
        (Real.sqrt 3)⁻¹ / 2 * Matrix.diagonal d n p *
          conventionScalarEquationResidual phi0 d phi2 A1 := by
  rw [conventionKaluzaRicci_base_base phi0 d phi1 phi2 A1 A2 g2 hd
    hphi2 hg2deriv hg2metric n p]
  unfold conventionEinsteinEquationResidual conventionScalarEquationResidual
    normalFrameScalarBox normalFrameMaxwellContraction
    normalFrameMaxwellNormSq
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hsqrt]
  ring

/-- Once the scalar equation holds, the base Ricci block is exactly the
four-dimensional Einstein residual. -/
theorem conventionKaluzaRicci_base_base_of_scalarEquation
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu)
    (hscalar : conventionScalarEquationResidual phi0 d phi2 A1 = 0)
    (n p : Fin 4) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inl p) =
      conventionEinsteinEquationResidual phi0 d phi1 A1 g2 n p := by
  rw [conventionKaluzaRicci_base_base_eq_einstein_add_scalar phi0 d phi1
    phi2 A1 A2 g2 hd hphi2 hg2deriv hg2metric n p, hscalar, mul_zero,
    add_zero]

/-- Under the scalar equation, vanishing of a base Ricci component is
equivalent to vanishing of the corresponding EMD Einstein residual. -/
theorem conventionKaluzaRicci_base_base_eq_zero_iff
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu)
    (hscalar : conventionScalarEquationResidual phi0 d phi2 A1 = 0)
    (n p : Fin 4) :
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inl p) = 0 ↔
      conventionEinsteinEquationResidual phi0 d phi1 A1 g2 n p = 0 := by
  rw [conventionKaluzaRicci_base_base_of_scalarEquation phi0 d phi1 phi2 A1
    A2 g2 hd hphi2 hg2deriv hg2metric hscalar n p]

/-- Vanishing of the upper normal-gauge Ricci block system.  The base
quantifier is deliberately left over all ordered pairs, so this intermediate
definition hides no base-block symmetry argument. -/
noncomputable def ConventionKaluzaRicciBlocksVanish
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ n p : Fin 4,
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inl p) = 0) ∧
  (∀ n : Fin 4,
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (Sum.inl n) (Sum.inr ()) = 0) ∧
  kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
      kaluzaGaugeNormalization kaluzaBaseWarpExponent
      kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
      (Sum.inr ()) (Sum.inr ()) = 0

/-- The convention-fixed four-dimensional EMD equation system in a diagonal
normal frame: Einstein, weighted Maxwell, and scalar residuals all vanish. -/
noncomputable def ConventionEMDNormalFrameEquations
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ n p : Fin 4,
    conventionEinsteinEquationResidual phi0 d phi1 A1 g2 n p = 0) ∧
  (∀ n : Fin 4, conventionWeightedMaxwellResidual d phi1 A1 A2 n = 0) ∧
  conventionScalarEquationResidual phi0 d phi2 A1 = 0

/-- **Normal-frame Kaluza reduction theorem.** Under the symmetry conditions
that make the input arrays genuine scalar and metric second jets, vanishing
of the upper five-dimensional Ricci block system is equivalent to the full
convention-fixed four-dimensional Einstein--Maxwell--dilaton system.

This is an exact forward-and-converse statement at the coordinate-jet layer;
the downstream field and intrinsic-local layers package it for smooth fields,
normal coordinates, and chart-independent local products with a circle. -/
theorem conventionKaluzaRicciBlocksVanish_iff_emd
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu) :
    ConventionKaluzaRicciBlocksVanish phi0 d phi1 phi2 A1 A2 g2 ↔
      ConventionEMDNormalFrameEquations phi0 d phi1 phi2 A1 A2 g2 := by
  unfold ConventionKaluzaRicciBlocksVanish
    ConventionEMDNormalFrameEquations
  constructor
  · rintro ⟨hbase, hmixed, hfiber⟩
    have hscalar : conventionScalarEquationResidual phi0 d phi2 A1 = 0 :=
      (conventionKaluzaRicci_fiber_fiber_eq_zero_iff phi0 d phi1 phi2 A1 A2
        g2 hd).mp hfiber
    refine ⟨?_, ?_, hscalar⟩
    · intro n p
      exact (conventionKaluzaRicci_base_base_eq_zero_iff phi0 d phi1 phi2 A1
        A2 g2 hd hphi2 hg2deriv hg2metric hscalar n p).mp (hbase n p)
    · intro n
      exact (conventionKaluzaRicci_base_fiber_eq_zero_iff phi0 d phi1 phi2
        A1 A2 g2 hd n).mp (hmixed n)
  · rintro ⟨hEinstein, hMaxwell, hscalar⟩
    refine ⟨?_, ?_, ?_⟩
    · intro n p
      exact (conventionKaluzaRicci_base_base_eq_zero_iff phi0 d phi1 phi2 A1
        A2 g2 hd hphi2 hg2deriv hg2metric hscalar n p).mpr
          (hEinstein n p)
    · intro n
      exact (conventionKaluzaRicci_base_fiber_eq_zero_iff phi0 d phi1 phi2
        A1 A2 g2 hd n).mpr (hMaxwell n)
    · exact (conventionKaluzaRicci_fiber_fiber_eq_zero_iff phi0 d phi1 phi2
        A1 A2 g2 hd).mpr hscalar

/-- Pointwise Ricci-flatness of the full convention-fixed Kaluza coordinate
jet, with both orders of every mixed component included. -/
noncomputable def ConventionKaluzaRicciFlatAt
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ N P : Fin 4 ⊕ Unit,
    kaluzaNormalGaugeRicci (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
      kaluzaGaugeNormalization kaluzaBaseWarpExponent
      kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2 N P = 0

/-- **Full pointwise Kaluza reduction theorem.** For genuine commuting scalar,
gauge, and metric second jets, the complete `5×5` convention-fixed Kaluza
Ricci tensor vanishes if and only if the normal-frame four-dimensional
Einstein--Maxwell--dilaton equations hold. -/
theorem conventionKaluzaRicciFlatAt_iff_emd
    (phi0 : ℝ) (d : Fin 4 → ℝ) (phi1 : OneForm4)
    (phi2 : Fin 4 → Fin 4 → ℝ) (A1 : Fin 4 → Fin 4 → ℝ)
    (A2 : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (g2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (hphi2 : ∀ a b, phi2 a b = phi2 b a)
    (hA2 : ∀ a b mu, A2 a b mu = A2 b a mu)
    (hg2deriv : ∀ a b mu nu, g2 a b mu nu = g2 b a mu nu)
    (hg2metric : ∀ a b mu nu, g2 a b mu nu = g2 a b nu mu) :
    ConventionKaluzaRicciFlatAt phi0 d phi1 phi2 A1 A2 g2 ↔
      ConventionEMDNormalFrameEquations phi0 d phi1 phi2 A1 A2 g2 := by
  rw [← conventionKaluzaRicciBlocksVanish_iff_emd phi0 d phi1 phi2 A1 A2 g2
    hd hphi2 hg2deriv hg2metric]
  constructor
  · intro hflat
    exact ⟨
      fun n p => hflat (Sum.inl n) (Sum.inl p),
      fun n => hflat (Sum.inl n) (Sum.inr ()),
      hflat (Sum.inr ()) (Sum.inr ())⟩
  · rintro ⟨hbase, hmixed, hfiber⟩ N P
    rcases N with n | _ <;> rcases P with p | _
    · exact hbase n p
    · exact hmixed n
    · rw [kaluzaNormalGaugeRicci_fiber_base_eq_base_fiber
        (kaluzaBaseWarp phi0) (kaluzaFiberWarp phi0)
        kaluzaGaugeNormalization kaluzaBaseWarpExponent
        kaluzaFiberWarpExponent d phi1 phi2 A1 A2 g2
        (kaluzaBaseWarp_ne_zero phi0) (kaluzaFiberWarp_ne_zero phi0) hd hA2 p]
      exact hmixed p
    · exact hfiber

end RainichKaluza
