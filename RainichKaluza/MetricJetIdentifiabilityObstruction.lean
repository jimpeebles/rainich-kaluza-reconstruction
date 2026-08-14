import RainichKaluza.GenericActiveThirdOrderAmbiguity

/-!
# Metric-jet identifiability obstruction

This file isolates the elementary but important logical step behind a
solution-germ lower bound.  Once two solutions with different coupling
squares have the same metric jet, no rule on that jet space can identify the
coupling square on both solutions.

The generic theorem is independent of EMD and of any regularity or covariance
chosen for the candidate rule.  The final specialization records the already
proved *finite formal-jet* collision.  Promoting its hypotheses from formal
jets to actual analytic EMD solution germs remains exactly the involutivity /
Cartan--Kähler frontier; this file does not assume that upgrade.
-/

namespace RainichKaluza

/-- A rule on `Jet` identifies the square of a parameter on a class of
objects when it returns that square on every object in the class. -/
def IdentifiesParameterSquareOn {Object Jet : Type*}
    (jet : Object → Jet) (parameter : Object → ℝ) (rule : Jet → ℝ) : Prop :=
  ∀ object, rule (jet object) = (parameter object) ^ 2

/-- **Collision obstruction.**  Equal observed jets with unequal parameter
squares rule out every set-theoretic identifier on the jet space.  Thus the
conclusion automatically applies to continuous, smooth, algebraic, natural,
or coordinate-covariant differential rules as special cases. -/
theorem no_parameterSquare_identifier_of_jet_collision
    {Object Jet : Type*} (jet : Object → Jet) (parameter : Object → ℝ)
    {left right : Object}
    (hjet : jet left = jet right)
    (hsq : (parameter left) ^ 2 ≠ (parameter right) ^ 2) :
    ¬ ∃ rule : Jet → ℝ, IdentifiesParameterSquareOn jet parameter rule := by
  rintro ⟨rule, hrule⟩
  apply hsq
  calc
    (parameter left) ^ 2 = rule (jet left) := (hrule left).symm
    _ = rule (jet right) := congrArg rule hjet
    _ = (parameter right) ^ 2 := hrule right

/-- The fixed normal-coordinate metric three-jet used by the active ambiguity
family. -/
abbrev ActiveAmbiguityMetricThreeJet4 :=
  Matrix4 × CoordinateMetricJet1 (Fin 4) ×
    CoordinateMetricJet2 (Fin 4) × CoordinateMetricJet3 (Fin 4)

/-- A certified member of the compiled active formal EMD-jet family.  The
fields retain the scientifically relevant equation-jet facts needed to make
the observation collision non-vacuous. -/
structure ActiveAmbiguityFormalEMDJetDatum where
  coupling : ℝ
  simpleSpectrum :
    (-1 : ℝ) ≠ 1 ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (-1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvalueMinus ∧
      (1 : ℝ) ≠ activeAmbiguityScalarEigenvaluePlus ∧
      activeAmbiguityScalarEigenvalueMinus ≠
        activeAmbiguityScalarEigenvaluePlus
  active :
    IsCoordinateMaxwellStressActiveWedge
      (matrixMaxwellStress minkowskiMetric activeAmbiguityMaxwellField)
      (activeAmbiguityPhysicalComplexionFromDoubleAngleJet coupling)
      activeAmbiguityScalarCovector
  einsteinPoint : ∀ n p,
    normalFrameBaseRicci minkowskiSign activeAmbiguityFormalMetricJet2 n p =
      activeAmbiguityCovariantRicciSource n p
  einsteinFirst : ∀ r n p,
    coordinateRicciFirstJet minkowskiMetric 0
        activeAmbiguityFormalMetricJet2 activeAmbiguityFormalMetricJet3
        r n p =
      (minkowskiMetric * activeAmbiguityRicciSourceFirstJet coupling r) n p
  exterior :
    EMDExteriorClosure matrixOneWedgeTwo activeAmbiguityScalarCovector
      coupling activeAmbiguityMaxwellField activeAmbiguityMaxwellHodge
      (matrixExteriorDerivative
        (activeAmbiguityMaxwellFirstJet coupling))
      (matrixExteriorDerivative
        (activeAmbiguityMaxwellHodgeFirstJet coupling))
  scalarPoint :
    genericEMDScalarJetResidual coupling 0 activeAmbiguityMaxwellField = 0

/-- The compiled finite identities supply one certified formal datum for
every real coupling. -/
noncomputable def ActiveAmbiguityFormalEMDJetDatum.ofCoupling
    (a : ℝ) : ActiveAmbiguityFormalEMDJetDatum where
  coupling := a
  simpleSpectrum := activeAmbiguityRicciSource_four_roots_pairwise_distinct
  active := activeAmbiguityPhysicalComplexion_maxwellStressActive a
  einsteinPoint := activeAmbiguityFormalMetricJet2_einsteinEquation
  einsteinFirst := by
    intro r n p
    rw [activeAmbiguityRicciSourceFirstJet_eq_common]
    exact activeAmbiguityFormalMetricJet3_einsteinFirstProlongation r n p
  exterior := activeAmbiguityMaxwellJet_emdExteriorClosure a
  scalarPoint := genericEMDScalarJetResidual_activeAmbiguity_eq_zero a

/-- The common metric three-jet observed from every certified member of the
explicit active formal family. -/
noncomputable def activeAmbiguityMetricThreeJet4
    (_datum : ActiveAmbiguityFormalEMDJetDatum) :
    ActiveAmbiguityMetricThreeJet4 :=
  (minkowskiMetric, 0, activeAmbiguityFormalMetricJet2,
    activeAmbiguityFormalMetricJet3)

/-- Every member of the explicit active family has the same displayed metric
three-jet. -/
theorem activeAmbiguityMetricThreeJet4_eq
    (left right : ActiveAmbiguityFormalEMDJetDatum) :
    activeAmbiguityMetricThreeJet4 left =
      activeAmbiguityMetricThreeJet4 right :=
  rfl

/-- **Finite formal-jet non-identifiability.**  No function of the common
metric three-jet can return `a²` for every member of the explicit active
simple-spectrum formal family.

This is a theorem about the compiled finite EMD equation jets.  It becomes a
solution-space order-three impossibility theorem only after the separate
analytic EMD realization proposition is established. -/
theorem no_couplingSquare_identifier_on_activeFormalMetricThreeJet :
    ¬ ∃ rule : ActiveAmbiguityMetricThreeJet4 → ℝ,
      IdentifiesParameterSquareOn activeAmbiguityMetricThreeJet4
        ActiveAmbiguityFormalEMDJetDatum.coupling rule := by
  apply no_parameterSquare_identifier_of_jet_collision
    activeAmbiguityMetricThreeJet4
    ActiveAmbiguityFormalEMDJetDatum.coupling
    (left := ActiveAmbiguityFormalEMDJetDatum.ofCoupling 1)
    (right := ActiveAmbiguityFormalEMDJetDatum.ofCoupling 2)
  · exact activeAmbiguityMetricThreeJet4_eq _ _
  · norm_num [ActiveAmbiguityFormalEMDJetDatum.ofCoupling]

end RainichKaluza
