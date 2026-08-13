import RainichKaluza.ThirdOrderMatterJetAmbiguity

/-!
# Exact finite-jet identifiability threshold

This file packages the algebraic transition behind the third-to-fourth-order
detector in two sharp statements.

First, on the intrinsic branch where the canonical Maxwell amplitude `E` and
scalar covector `v` are nonzero, every fiber of the *complete* first-order
channel map is exactly one affine real-shear orbit.  Thus the shear exhibited
in `GeometricCouplingDetector` is the whole ambiguity, not merely one source
of nonuniqueness.

Second, on the explicit active formal-metric-three-jet family, the fixed
fourth-order channel separates two couplings precisely up to the unavoidable
overall sign: its outputs agree exactly when `a = b` or `a = -b`.
-/

namespace RainichKaluza

/-- The affine shear on the pair consisting of the physical complexion
one-form and the hidden sine-coupling component.  Its effective one-form
`omega + (B / 2) Jv` is unchanged. -/
noncomputable def canonicalFirstOrderChannelShear
    (v : OneForm4) (tau : ℝ) (p : OneForm4 × ℝ) : OneForm4 × ℝ :=
  (p.1 - (tau / 2) • canonicalPrincipalReflectionCovector v,
    p.2 + tau)

/-- Zero shear is the identity. -/
@[simp] theorem canonicalFirstOrderChannelShear_zero
    (v : OneForm4) (p : OneForm4 × ℝ) :
    canonicalFirstOrderChannelShear v 0 p = p := by
  apply Prod.ext
  · funext i
    simp [canonicalFirstOrderChannelShear]
  · simp [canonicalFirstOrderChannelShear]

/-- Successive shears add their real parameters. -/
theorem canonicalFirstOrderChannelShear_add
    (v : OneForm4) (tau sigma : ℝ) (p : OneForm4 × ℝ) :
    canonicalFirstOrderChannelShear v sigma
        (canonicalFirstOrderChannelShear v tau p) =
      canonicalFirstOrderChannelShear v (tau + sigma) p := by
  apply Prod.ext
  · funext i
    simp [canonicalFirstOrderChannelShear]
    ring
  · simp [canonicalFirstOrderChannelShear]
    ring

/-- The affine shear action is free: its parameter is already visible in the
second component. -/
theorem canonicalFirstOrderChannelShear_parameter_unique
    (v : OneForm4) (tau sigma : ℝ) (p : OneForm4 × ℝ)
    (h : canonicalFirstOrderChannelShear v tau p =
      canonicalFirstOrderChannelShear v sigma p) :
    tau = sigma := by
  have hsecond := congrArg Prod.snd h
  simpa [canonicalFirstOrderChannelShear] using hsecond

/-- **Exact classification of complete first-order channel fibers.**  Fix a
non-null canonical Maxwell seed (`E != 0`) and a nonzero scalar covector
(`v != 0`).  Two full first-order inputs have identical complete channel
pairs if and only if their cosine components agree and their
`(complexion,sine)` pairs differ by one—and, by freeness, a unique—real
affine shear.

No fourth-order equation is used here.  The hypotheses are exactly those
needed by the existing injectivity theorem for the effective pair `(eta,A)`;
without them, additional channel degeneracies may occur. -/
theorem canonicalFullComplexionCouplingChannels_eq_iff_shearOrbit
    (E : ℝ) (hE : E ≠ 0) (v : OneForm4) (hv : v ≠ 0)
    (omega omega' : OneForm4) (A A' B B' : ℝ) :
    canonicalFullComplexionCouplingChannels E v omega' A' B' =
        canonicalFullComplexionCouplingChannels E v omega A B ↔
      A' = A ∧ ∃ tau : ℝ,
        (omega', B') =
          canonicalFirstOrderChannelShear v tau (omega, B) := by
  constructor
  · intro hchannels
    have heffective :
        effectiveComplexionOneForm omega'
              (canonicalPrincipalReflectionCovector v) B' =
            effectiveComplexionOneForm omega
              (canonicalPrincipalReflectionCovector v) B ∧
          A' = A :=
      canonicalComplexionCouplingChannels_injective E hE v hv
        (effectiveComplexionOneForm omega'
          (canonicalPrincipalReflectionCovector v) B')
        (effectiveComplexionOneForm omega
          (canonicalPrincipalReflectionCovector v) B)
        A' A (by
          simpa [canonicalFullComplexionCouplingChannels] using hchannels)
    refine ⟨heffective.2, B' - B, ?_⟩
    apply Prod.ext
    · funext i
      have hi := congrFun heffective.1 i
      simp [effectiveComplexionOneForm,
        canonicalFirstOrderChannelShear] at hi ⊢
      linarith
    · simp [canonicalFirstOrderChannelShear]
  · rintro ⟨hA, ⟨tau, hshear⟩⟩
    have homega := congrArg Prod.fst hshear
    have hB := congrArg Prod.snd hshear
    simp [canonicalFirstOrderChannelShear] at homega hB
    rw [hA, homega, hB]
    exact canonicalFullComplexionCouplingChannels_shear_invariant
      E v omega A B tau

/-- **Sharp fourth-order separation on the active ambiguity family.**  The
fixed fourth-order coupling-square outputs for parameters `a` and `b` agree
if and only if the physical couplings agree up to overall sign.  In
particular, the fourth-order channel removes the full continuous first-order
shear ambiguity while retaining exactly the orientation-free `a^2`
ambiguity that the detector is designed to retain.

This is a theorem about the explicit active formal finite-jet family.  It is
not an all-order PDE-integrability or local-solution-existence statement. -/
theorem activeAmbiguityFourthOrderCouplingSqCandidates_eq_iff
    (a b : ℝ) :
    fourthOrderCouplingSqCandidate (Real.sqrt 2)
          activeAmbiguityScalarCovector
          (activeAmbiguityCosineCouplingFirstDerivative a)
          activeAmbiguityCommonFirstOrderChannels
          activeAmbiguityFourthOrderChoice =
        fourthOrderCouplingSqCandidate (Real.sqrt 2)
          activeAmbiguityScalarCovector
          (activeAmbiguityCosineCouplingFirstDerivative b)
          activeAmbiguityCommonFirstOrderChannels
          activeAmbiguityFourthOrderChoice ↔
      a = b ∨ a = -b := by
  rw [activeAmbiguityFourthOrderCouplingSqCandidate_eq,
    activeAmbiguityFourthOrderCouplingSqCandidate_eq]
  exact sq_eq_sq_iff_eq_or_eq_neg

end RainichKaluza
