import RainichKaluza.ReconstructionEquation

/-!
# Formal claim boundary

These structures name hypotheses required by later stages. Fields of type
`Prop` are assumption slots, not axioms and not evidence that nature realizes
the assumptions.
-/

namespace RainichKaluza

/-- Branch restrictions needed before a generic reconstruction theorem can be
stated without conflating null and degenerate cases. -/
structure GenericBranchAssumptions where
  ricciTrace_nonzero : Prop
  maxwell_nonnull : Prop
  scalarGradient_nonnull : Prop
  protectedPair_simple : Prop
  lorentzian_signature_compatible : Prop

/-- Obligations needed to upgrade an algebraic fingerprint into a local
metric-only reconstruction theorem. -/
structure LocalReconstructionObligations where
  rankOneTensor_exists : Prop
  rankOneTensor_unique_up_to_sign : Prop
  scalarOneForm_closed : Prop
  residualStress_isMaxwell : Prop
  maxwellDifferentialConditions : Prop
  scalarFieldEquation : Prop

/-- Obligations deliberately excluded from the first algebraic Lean layer. -/
structure GeometricProvenanceObligations where
  followsFromSqrtThreeEMD : Prop
  followsFromFiveDimensionalVacuumReduction : Prop
  frameAndNormalizationMatched : Prop
  globalTopologyControlled : Prop

end RainichKaluza
