import RainichKaluza.FourthOrderMetricDetector
import RainichKaluza.PolynomialMetricJetRealization

/-!
# Fixed-coordinate four-jet dependency boundary

This file separates two finite dependency statements that were previously
implicit in the construction of the actual-metric detector.

* `FixedCoordinateMetricFourJet4` is the literal nested-coordinate-`fderiv`
  package of a metric through order four.  Equality of its order-two
  truncation already fixes the complete algebraic Ricci entrance.
* `CurvatureSeedOperationalFirstJet4` is the exact finite first-jet payload
  consumed by the fourth-order curvature-seed channel.  Both channel
  acceptance and its numerical output factor definitionally through this
  payload.

The remaining theorem needed for a complete primitive metric-four-jet
factorization is deliberately exposed rather than hidden: one must prove,
under the appropriate `C^4` and nondegeneracy hypotheses, that equality of
`FixedCoordinateMetricFourJet4` forces equality of the derived operational
payloads (principal coframe, positive curvature magnitude, reconstructed
scalar covector, and their indicated derivatives).  That is a chain-rule
prolongation theorem through matrix inverse, square roots, normalized
eigenprobes, and the channel quotient.  No neighborhood-germ equality is
used in the results below.
-/

namespace RainichKaluza

open scoped Matrix Topology

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

/-- Actual fourth nested coordinate derivative of the metric components.
The leftmost derivative index is the outermost `fderiv`. -/
noncomputable def actualCoordinateMetricJet4Field4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix4 :=
  fun r s t u i j => scalarFieldCoordinateFDeriv
    (fun y => actualCoordinateMetricJet3Field4 g y s t u i j) z r

/-- Literal fixed-coordinate metric component jet through four nested
Frechet derivatives.  This is a finite package; it contains no metric germ
and no derived curvature fields. -/
structure FixedCoordinateMetricFourJet4 where
  metric : Matrix4
  first : Fin 4 → Matrix4
  second : Fin 4 → Fin 4 → Matrix4
  third : Fin 4 → Fin 4 → Fin 4 → Matrix4
  fourth : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix4

/-- The order-two truncation that already determines every algebraic Ricci
quantity used at the detector entrance. -/
structure FixedCoordinateMetricTwoJet4 where
  metric : Matrix4
  first : Fin 4 → Matrix4
  second : Fin 4 → Fin 4 → Matrix4

/-- Forget the third and fourth derivative slots. -/
def FixedCoordinateMetricFourJet4.truncateTwo
    (J : FixedCoordinateMetricFourJet4) : FixedCoordinateMetricTwoJet4 where
  metric := J.metric
  first := J.first
  second := J.second

/-- Extract the literal nested component four-jet of an actual metric field
at one point. -/
noncomputable def FixedCoordinateMetricFourJet4.ofField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : FixedCoordinateMetricFourJet4 where
  metric := coordinateMetricMatrixField4 g z
  first := actualCoordinateMetricJet1Field4 g z
  second := actualCoordinateMetricJet2Field4 g z
  third := actualCoordinateMetricJet3Field4 g z
  fourth := actualCoordinateMetricJet4Field4 g z

/-- Extract only the literal component two-jet of a metric field. -/
noncomputable def FixedCoordinateMetricTwoJet4.ofField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : FixedCoordinateMetricTwoJet4 :=
  (FixedCoordinateMetricFourJet4.ofField g z).truncateTwo

/-- Equality of literal fixed-coordinate metric two-jets at a point. -/
def SameFixedCoordinateMetricTwoJetAt4
    (g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  FixedCoordinateMetricTwoJet4.ofField g z =
    FixedCoordinateMetricTwoJet4.ofField g' z

/-- Pure coordinate Ricci tensor evaluated on a finite metric two-jet. -/
noncomputable def FixedCoordinateMetricTwoJet4.ricciCovariant
    (J : FixedCoordinateMetricTwoJet4) : Matrix4 :=
  fun i j => coordinateRicci (J.metric⁻¹ : Matrix4) J.first J.second i j

/-- Regression lock for the finite-jet evaluator's use of matrix inversion.
Without the explicit `Matrix4` type, Lean can select entrywise inversion on
the underlying function type. -/
theorem FixedCoordinateMetricTwoJet4.ricciCovariant_uses_matrixInverse
    (J : FixedCoordinateMetricTwoJet4) :
    J.ricciCovariant = fun i j =>
      coordinateRicci (J.metric⁻¹ : Matrix4) J.first J.second i j := by
  rfl

theorem FixedCoordinateMetricTwoJet4.ricciCovariant_ofField
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    (FixedCoordinateMetricTwoJet4.ofField g z).ricciCovariant =
      actualCoordinateRicciCovariantField4 g z := by
  rfl

/-- Pure mixed Ricci endomorphism evaluated on a finite metric two-jet. -/
noncomputable def FixedCoordinateMetricTwoJet4.mixedRicci
    (J : FixedCoordinateMetricTwoJet4) : Matrix4 :=
  J.metric⁻¹ * J.ricciCovariant

/-- Pure characteristic data of the finite-jet mixed Ricci endomorphism. -/
noncomputable def FixedCoordinateMetricTwoJet4.characteristicData
    (J : FixedCoordinateMetricTwoJet4) : CharacteristicData :=
  CharacteristicData.ofEndomorphism (Matrix.toLin' J.mixedRicci)

noncomputable def FixedCoordinateMetricTwoJet4.qSq
    (J : FixedCoordinateMetricTwoJet4) : ℝ :=
  reconstructedQSq J.characteristicData

noncomputable def FixedCoordinateMetricTwoJet4.discriminant
    (J : FixedCoordinateMetricTwoJet4) : ℝ :=
  J.characteristicData.e1 ^ 2 +
    4 * reconstructedResidualConstant J.characteristicData

noncomputable def FixedCoordinateMetricTwoJet4.rootA
    (J : FixedCoordinateMetricTwoJet4) : ℝ :=
  (J.characteristicData.e1 - Real.sqrt J.discriminant) / 2

noncomputable def FixedCoordinateMetricTwoJet4.rootB
    (J : FixedCoordinateMetricTwoJet4) : ℝ :=
  (J.characteristicData.e1 + Real.sqrt J.discriminant) / 2

noncomputable def FixedCoordinateMetricTwoJet4.protectedRoot
    (J : FixedCoordinateMetricTwoJet4) : ℝ :=
  Real.sqrt J.qSq

/-- Pure four-root Lagrange projector, specialized to finite point data. -/
noncomputable def finiteFourRootProjector4
    (R : Matrix4) (a b c d : ℝ) : Matrix4 :=
  (((a - b) * (a - c) * (a - d))⁻¹) •
    (((R - b • (1 : Matrix4)) * (R - c • (1 : Matrix4))) *
      (R - d • (1 : Matrix4)))

noncomputable def FixedCoordinateMetricTwoJet4.projectorA
    (J : FixedCoordinateMetricTwoJet4) : Matrix4 :=
  finiteFourRootProjector4 J.mixedRicci J.rootA (-J.protectedRoot)
    J.rootB J.protectedRoot

noncomputable def FixedCoordinateMetricTwoJet4.projectorB
    (J : FixedCoordinateMetricTwoJet4) : Matrix4 :=
  finiteFourRootProjector4 J.mixedRicci J.rootB J.rootA
    (-J.protectedRoot) J.protectedRoot

/-- Pure algebraic entrance predicate on a finite metric two-jet. -/
def FixedCoordinateMetricTwoJet4.AlgebraicEntrance
    (J : FixedCoordinateMetricTwoJet4) : Prop :=
  J.metric.transpose = J.metric ∧
  Matrix.det J.metric < 0 ∧
  J.metric * J.metric⁻¹ = 1 ∧
  (J.metric * J.mixedRicci).transpose = J.metric * J.mixedRicci ∧
  J.characteristicData.e1 ≠ 0 ∧
  kaluzaObstruction J.characteristicData = 0 ∧
  0 < J.qSq ∧
  0 < J.discriminant ∧
  J.rootA ≠ -J.protectedRoot ∧
  J.rootA ≠ J.rootB ∧
  J.rootA ≠ J.protectedRoot ∧
  -J.protectedRoot ≠ J.rootB ∧
  -J.protectedRoot ≠ J.protectedRoot ∧
  J.rootB ≠ J.protectedRoot ∧
  J.projectorA * J.projectorA = J.projectorA ∧
  J.projectorB * J.projectorB = J.projectorB ∧
  J.projectorA * J.projectorB = 0 ∧
  Matrix.trace J.projectorA = 1 ∧
  Matrix.trace J.projectorB = 1 ∧
  J.mixedRicci * J.projectorA = J.rootA • J.projectorA ∧
  J.mixedRicci * J.projectorB = J.rootB • J.projectorB

/-- The actual pointwise algebraic entrance is literally a predicate on the
finite coordinate metric two-jet. -/
theorem isActualMetricAlgebraicEntranceAt4_iff_twoJet
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) :
    IsActualMetricAlgebraicEntranceAt4 g z ↔
      (FixedCoordinateMetricTwoJet4.ofField g z).AlgebraicEntrance := by
  rfl

/-- Equality of finite metric two-jets is sufficient for equality of the
complete algebraic entrance predicate; no germ hypothesis is present. -/
theorem isActualMetricAlgebraicEntranceAt4_iff_of_twoJet_eq
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : FixedCoordinateMetricTwoJet4.ofField g z =
      FixedCoordinateMetricTwoJet4.ofField g' z) :
    IsActualMetricAlgebraicEntranceAt4 g z ↔
      IsActualMetricAlgebraicEntranceAt4 g' z := by
  rw [isActualMetricAlgebraicEntranceAt4_iff_twoJet,
    isActualMetricAlgebraicEntranceAt4_iff_twoJet, h]

/-- Equality of literal fixed-coordinate metric four-jets at a point. -/
def SameFixedCoordinateMetricFourJetAt4
    (g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4) : Prop :=
  FixedCoordinateMetricFourJet4.ofField g z =
    FixedCoordinateMetricFourJet4.ofField g' z

/-- Four-jet equality implies equality of its two-jet truncation. -/
theorem sameFixedCoordinateMetricTwoJetAt4_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    SameFixedCoordinateMetricTwoJetAt4 g g' z := by
  exact congrArg FixedCoordinateMetricFourJet4.truncateTwo h

theorem coordinateMetricMatrixField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    coordinateMetricMatrixField4 g z = coordinateMetricMatrixField4 g' z := by
  exact congrArg FixedCoordinateMetricFourJet4.metric h

theorem actualCoordinateMetricJet1Field4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualCoordinateMetricJet1Field4 g z =
      actualCoordinateMetricJet1Field4 g' z := by
  exact congrArg FixedCoordinateMetricFourJet4.first h

theorem actualCoordinateMetricJet2Field4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualCoordinateMetricJet2Field4 g z =
      actualCoordinateMetricJet2Field4 g' z := by
  exact congrArg FixedCoordinateMetricFourJet4.second h

theorem actualCoordinateMetricJet3Field4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualCoordinateMetricJet3Field4 g z =
      actualCoordinateMetricJet3Field4 g' z := by
  exact congrArg FixedCoordinateMetricFourJet4.third h

theorem actualCoordinateMetricJet4Field4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualCoordinateMetricJet4Field4 g z =
      actualCoordinateMetricJet4Field4 g' z := by
  exact congrArg FixedCoordinateMetricFourJet4.fourth h

/-- Ricci itself consumes only the order-two truncation of the packaged
metric four-jet. -/
theorem actualCoordinateRicciCovariantField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualCoordinateRicciCovariantField4 g z =
      actualCoordinateRicciCovariantField4 g' z := by
  unfold actualCoordinateRicciCovariantField4
  rw [coordinateMetricMatrixField4_eq_of_sameFourJet h,
    actualCoordinateMetricJet1Field4_eq_of_sameFourJet h,
    actualCoordinateMetricJet2Field4_eq_of_sameFourJet h]

theorem actualMixedRicciField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualMixedRicciField4 g z = actualMixedRicciField4 g' z := by
  unfold actualMixedRicciField4
  rw [coordinateMetricMatrixField4_eq_of_sameFourJet h,
    actualCoordinateRicciCovariantField4_eq_of_sameFourJet h]

theorem actualRicciCharacteristicDataField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciCharacteristicDataField4 g z =
      actualRicciCharacteristicDataField4 g' z := by
  unfold actualRicciCharacteristicDataField4
  rw [actualMixedRicciField4_eq_of_sameFourJet h]

theorem actualRicciReconstructedQSqField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciReconstructedQSqField4 g z =
      actualRicciReconstructedQSqField4 g' z := by
  unfold actualRicciReconstructedQSqField4
  rw [actualMixedRicciField4_eq_of_sameFourJet h]

theorem actualRicciComplementaryDiscriminantField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciComplementaryDiscriminantField4 g z =
      actualRicciComplementaryDiscriminantField4 g' z := by
  unfold actualRicciComplementaryDiscriminantField4
  rw [actualRicciCharacteristicDataField4_eq_of_sameFourJet h]

theorem actualRicciComplementaryRootAField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciComplementaryRootAField4 g z =
      actualRicciComplementaryRootAField4 g' z := by
  unfold actualRicciComplementaryRootAField4
  rw [actualRicciCharacteristicDataField4_eq_of_sameFourJet h,
    actualRicciComplementaryDiscriminantField4_eq_of_sameFourJet h]

theorem actualRicciComplementaryRootBField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciComplementaryRootBField4 g z =
      actualRicciComplementaryRootBField4 g' z := by
  unfold actualRicciComplementaryRootBField4
  rw [actualRicciCharacteristicDataField4_eq_of_sameFourJet h,
    actualRicciComplementaryDiscriminantField4_eq_of_sameFourJet h]

theorem actualRicciProtectedRootField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciProtectedRootField4 g z =
      actualRicciProtectedRootField4 g' z := by
  unfold actualRicciProtectedRootField4
  rw [actualRicciReconstructedQSqField4_eq_of_sameFourJet h]

theorem actualRicciComplementaryProjectorAField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciComplementaryProjectorAField4 g z =
      actualRicciComplementaryProjectorAField4 g' z := by
  unfold actualRicciComplementaryProjectorAField4
    matrixFourRootProjectorField matrixEigenFactorField
  simp only
  rw [actualMixedRicciField4_eq_of_sameFourJet h,
    actualRicciComplementaryRootAField4_eq_of_sameFourJet h,
    actualRicciComplementaryRootBField4_eq_of_sameFourJet h,
    actualRicciProtectedRootField4_eq_of_sameFourJet h]

theorem actualRicciComplementaryProjectorBField4_eq_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    actualRicciComplementaryProjectorBField4 g z =
      actualRicciComplementaryProjectorBField4 g' z := by
  unfold actualRicciComplementaryProjectorBField4
    matrixFourRootProjectorField matrixEigenFactorField
  simp only
  rw [actualMixedRicciField4_eq_of_sameFourJet h,
    actualRicciComplementaryRootAField4_eq_of_sameFourJet h,
    actualRicciComplementaryRootBField4_eq_of_sameFourJet h,
    actualRicciProtectedRootField4_eq_of_sameFourJet h]

/-- The entire pointwise algebraic Ricci entrance factors through the
order-two truncation of the literal metric four-jet. -/
theorem isActualMetricAlgebraicEntranceAt4_iff_of_sameFourJet
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (h : SameFixedCoordinateMetricFourJetAt4 g g' z) :
    IsActualMetricAlgebraicEntranceAt4 g z ↔
      IsActualMetricAlgebraicEntranceAt4 g' z := by
  unfold IsActualMetricAlgebraicEntranceAt4
  rw [coordinateMetricMatrixField4_eq_of_sameFourJet h,
    actualMixedRicciField4_eq_of_sameFourJet h,
    actualRicciCharacteristicDataField4_eq_of_sameFourJet h,
    actualRicciReconstructedQSqField4_eq_of_sameFourJet h,
    actualRicciProtectedRootField4_eq_of_sameFourJet h,
    actualRicciComplementaryRootAField4_eq_of_sameFourJet h,
    actualRicciComplementaryRootBField4_eq_of_sameFourJet h,
    actualRicciComplementaryProjectorAField4_eq_of_sameFourJet h,
    actualRicciComplementaryProjectorBField4_eq_of_sameFourJet h,
    actualRicciComplementaryDiscriminantField4_eq_of_sameFourJet h]

/-- The exact finite first-jet payload consumed by a curvature-seed
fourth-order channel.  The `cosineDerivative` slot is indexed by the four
possible quotient source components. -/
structure CurvatureSeedOperationalFirstJet4 where
  coframe : Matrix4
  coframeDerivative : Fin 4 → Matrix4
  magnitude : ℝ
  magnitudeDerivative : OneForm4
  scalarCovector : OneForm4
  cosineDerivative : Fin 4 → OneForm4

/-- Extract the operational first jet from the three derived fields used by
the curvature-seed detector. -/
noncomputable def CurvatureSeedOperationalFirstJet4.ofFields
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) : CurvatureSeedOperationalFirstJet4 where
  coframe := L z
  coframeDerivative := matrixFieldCoordinateFDeriv4 L z
  magnitude := q z
  magnitudeDerivative := scalarFieldCoordinateFDeriv q z
  scalarCovector := v z
  cosineDerivative := fun source =>
    curvatureSeedCosineCoordinateDerivative L q v source z

/-- Pure finite-data channel acceptance. -/
def CurvatureSeedOperationalFirstJet4.Accepts
    (J : CurvatureSeedOperationalFirstJet4)
    (choice : FourthOrderComponentChoice) : Prop :=
  IsTransportedSeedFourthOrderCandidate
    J.coframe J.coframe⁻¹ J.coframeDerivative J.magnitude
    J.magnitudeDerivative J.scalarCovector
    (J.cosineDerivative choice.1) choice

/-- Finite accepted channel set evaluated solely from one operational jet. -/
noncomputable def CurvatureSeedOperationalFirstJet4.acceptedChoices
    (J : CurvatureSeedOperationalFirstJet4) :
    Finset FourthOrderComponentChoice := by
  classical
  exact Finset.univ.filter J.Accepts

/-- Pure finite-data numerical output. -/
noncomputable def CurvatureSeedOperationalFirstJet4.couplingSq
    (J : CurvatureSeedOperationalFirstJet4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  transportedSeedFourthOrderCouplingSqCandidate
    J.coframe J.coframe⁻¹ J.coframeDerivative J.magnitude
    J.magnitudeDerivative J.scalarCovector
    (J.cosineDerivative choice.1) choice

/-- The field-based fourth-order channel predicate factors definitionally
through its finite operational first jet. -/
theorem isCurvatureSeedFourthOrderCandidateAt_iff_operationalFirstJet
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) :
    IsCurvatureSeedFourthOrderCandidateAt L q v z choice ↔
      (CurvatureSeedOperationalFirstJet4.ofFields L q v z).Accepts choice := by
  rfl

/-- The field-based channel output factors definitionally through the same
finite operational first jet. -/
theorem curvatureSeedFourthOrderCouplingSqCandidateAt_eq_operationalFirstJet
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4)
    (choice : FourthOrderComponentChoice) :
    curvatureSeedFourthOrderCouplingSqCandidateAt L q v z choice =
      (CurvatureSeedOperationalFirstJet4.ofFields L q v z).couplingSq choice := by
  rfl

/-- The complete finite field-based accepted channel set factors through the
same operational first jet. -/
theorem acceptedCurvatureSeedFourthOrderChoicesAt_eq_operationalFirstJet
    (L : CurvatureCoordinateSpace4 → Matrix4)
    (q : CurvatureCoordinateSpace4 → ℝ)
    (v : CurvatureCoordinateSpace4 → OneForm4)
    (z : CurvatureCoordinateSpace4) :
    acceptedCurvatureSeedFourthOrderChoicesAt L q v z =
      (CurvatureSeedOperationalFirstJet4.ofFields L q v z).acceptedChoices := by
  classical
  rfl

theorem CurvatureSeedOperationalFirstJet4.accepts_iff_of_eq
    {J J' : CurvatureSeedOperationalFirstJet4} (h : J = J')
    (choice : FourthOrderComponentChoice) :
    J.Accepts choice ↔ J'.Accepts choice := by
  rw [h]

theorem CurvatureSeedOperationalFirstJet4.couplingSq_eq_of_eq
    {J J' : CurvatureSeedOperationalFirstJet4} (h : J = J')
    (choice : FourthOrderComponentChoice) :
    J.couplingSq choice = J'.couplingSq choice := by
  rw [h]

theorem CurvatureSeedOperationalFirstJet4.acceptedChoices_eq_of_eq
    {J J' : CurvatureSeedOperationalFirstJet4} (h : J = J') :
    J.acceptedChoices = J'.acceptedChoices := by
  rw [h]

/-- Operational channel jet extracted from the actual metric for one raw
finite detector choice. -/
noncomputable def actualMetricFourthOrderOperationalJetAt4
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    CurvatureSeedOperationalFirstJet4 :=
  CurvatureSeedOperationalFirstJet4.ofFields
    (actualMetricPrincipalCoframeCandidateField4 g choice)
    (positiveMaxwellMagnitudeFromSquare
      (actualRicciReconstructedQSqField4 g))
    (actualMetricScalarOneFormCandidateField4 g
      choice.scalarTimelikeProbe choice.scalarSpacelikeProbe
      choice.relativeMinus) z

/-- Exact separation of the complete actual-metric acceptance predicate into
its upstream point test and its finite fourth-order operational jet. -/
theorem isActualMetricFourthOrderDetectorCandidateAt_iff_operationalJet
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    IsActualMetricFourthOrderDetectorCandidateAt g z choice ↔
      IsActualMetricUpstreamEntranceAt4 g z choice ∧
        (actualMetricFourthOrderOperationalJetAt4 g z choice).Accepts
          choice.channel := by
  rfl

/-- Every numerical output of the actual-metric detector factors through
the finite operational channel jet. -/
theorem actualMetricFourthOrderCouplingSqCandidateAt_eq_operationalJet
    (g : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4)
    (z : CurvatureCoordinateSpace4)
    (choice : ActualMetricDetectorChoice4) :
    actualMetricFourthOrderCouplingSqCandidateAt g z choice =
      (actualMetricFourthOrderOperationalJetAt4 g z choice).couplingSq
        choice.channel := by
  rfl

/-- Complete detector extensionality once the two explicitly separated
finite dependency obligations are supplied.  This theorem identifies the
precise seam left for the primitive metric-four-jet prolongation proof. -/
theorem actualMetricFourthOrderDetector_extensionality_of_operationalJets
    {g g' : CurvatureCoordinateSpace4 →
      ContinuousBilinForm CurvatureCoordinateSpace4}
    {z : CurvatureCoordinateSpace4}
    (hupstream : ∀ choice : ActualMetricDetectorChoice4,
      IsActualMetricUpstreamEntranceAt4 g z choice ↔
        IsActualMetricUpstreamEntranceAt4 g' z choice)
    (hjet : ∀ choice : ActualMetricDetectorChoice4,
      actualMetricFourthOrderOperationalJetAt4 g z choice =
        actualMetricFourthOrderOperationalJetAt4 g' z choice) :
    acceptedActualMetricFourthOrderDetectorChoicesAt g z =
        acceptedActualMetricFourthOrderDetectorChoicesAt g' z ∧
      ∀ choice : ActualMetricDetectorChoice4,
        actualMetricFourthOrderCouplingSqCandidateAt g z choice =
          actualMetricFourthOrderCouplingSqCandidateAt g' z choice := by
  constructor
  · classical
    ext choice
    rw [mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff,
      mem_acceptedActualMetricFourthOrderDetectorChoicesAt_iff,
      isActualMetricFourthOrderDetectorCandidateAt_iff_operationalJet,
      isActualMetricFourthOrderDetectorCandidateAt_iff_operationalJet,
      hupstream choice]
    exact and_congr_right (fun _ =>
      CurvatureSeedOperationalFirstJet4.accepts_iff_of_eq
        (hjet choice) choice.channel)
  · intro choice
    rw [actualMetricFourthOrderCouplingSqCandidateAt_eq_operationalJet,
      actualMetricFourthOrderCouplingSqCandidateAt_eq_operationalJet]
    exact CurvatureSeedOperationalFirstJet4.couplingSq_eq_of_eq
      (hjet choice) choice.channel

set_option linter.constructorNameAsVariable true

end RainichKaluza
