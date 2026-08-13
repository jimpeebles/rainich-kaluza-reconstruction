import RainichKaluza.LocalExteriorSeed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Probe-free geometric coupling detector

The two exterior EMD equations contain a four-component effective connection
and one effective scalar channel.  Earlier evaluated-channel formulas treated
these as the physical complexion one-form `omega` and coupling `a`, recovering
both after choosing scalar probes and assuming a nonzero `2 x 2` determinant.

This file proves the stronger finite-dimensional fact behind a metric-only
detector.  In a principal orthonormal frame the connection response and one
scalar response occupy complementary components of the pair of three-form
channels.  Therefore the complete channel map is injective as soon as the
non-null Maxwell seed amplitude and reconstructed scalar covector are nonzero.
No evaluation probes and no probe determinant occur.

For an arbitrary curvature-normalized Maxwell seed, however, these recovered
variables are `eta = omega + (B/2) Jv` and `A`, where
`A = a cos(2 theta)` and `B = a sin(2 theta)`.  The first-order channels have
an exact shear symmetry and cannot determine `B`.  The next-order constancy
equation generically removes that ambiguity and reconstructs `B`, hence
`a^2 = A^2 + B^2`.
-/

namespace RainichKaluza

/-- Complete pair of seed-channel right-hand sides in the canonical principal
frame.  It is the algebraic content of
`emdExteriorClosure_iff_seedChannels`, with the seed derivatives placed on the
left and the effective pair `(eta,A)` treated as the unknown pair.  Only in an
aligned complexion gauge may these be read directly as `(omega,a)`. -/
noncomputable def canonicalComplexionCouplingChannels
    (E : ℝ) (v eta : OneForm4) (A : ℝ) :
    ThreeTensor4 × ThreeTensor4 :=
  let F := canonicalMaxwellTwoForm E 0
  let G := canonicalHodgeStar E 0
  ((A / 2) • matrixOneWedgeTwoTensor v F -
      matrixOneWedgeTwoTensor eta G,
    matrixOneWedgeTwoTensor eta F -
      (A / 2) • matrixOneWedgeTwoTensor v G)

/-- A nonzero coordinate one-form has a nonzero component. -/
theorem exists_oneForm4_component_ne_zero
    (v : OneForm4) (hv : v ≠ 0) :
    ∃ i, v i ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  funext i
  exact h i

/-- **Probe-free canonical channel theorem.** For a non-null Maxwell seed and
a nonzero scalar covector, the full pair of exterior channels determines its
effective one-form `eta` and cosine-coupling component `A` uniquely.  The
former scalar probe determinant is replaced by the intrinsic branch
conditions `E != 0` and `v != 0`.  This theorem alone does *not* identify
`eta` with the physical complexion derivative or `A` with the full coupling. -/
theorem canonicalComplexionCouplingChannels_injective
    (E : ℝ) (hE : E ≠ 0) (v : OneForm4) (hv : v ≠ 0)
    (eta eta' : OneForm4) (A A' : ℝ)
    (hchannels : canonicalComplexionCouplingChannels E v eta A =
      canonicalComplexionCouplingChannels E v eta' A') :
    eta = eta' ∧ A = A' := by
  have homega0 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.1 0 2 3) hchannels
  have homega1 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.1 1 2 3) hchannels
  have homega2 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.2 0 1 2) hchannels
  have homega3 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.2 0 1 3) hchannels
  have ha0 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.2 0 2 3) hchannels
  have ha1 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.2 1 2 3) hchannels
  have ha2 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.1 0 1 2) hchannels
  have ha3 := congrArg
    (fun P : ThreeTensor4 × ThreeTensor4 => P.1 0 1 3) hchannels
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at homega0
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at homega1
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at homega2
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at homega3
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at ha0
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at ha1
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at ha2
  simp [canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
    canonicalMaxwellTwoForm, canonicalHodgeStar, hE] at ha3
  constructor
  · funext i
    fin_cases i
    · exact homega0
    · exact homega1
    · exact homega2
    · exact homega3
  · obtain ⟨i, hi⟩ := exists_oneForm4_component_ne_zero v hv
    fin_cases i
    · exact ha0.resolve_right hi
    · exact ha1.resolve_right hi
    · exact ha2.resolve_right hi
    · exact ha3.resolve_right hi

/-- Existence of a compatible canonical channel pair together with the
intrinsic non-null/nonzero branch hypotheses gives an actual unique effective
`(eta,A)` output. -/
theorem existsUnique_canonicalComplexionCoupling
    (E : ℝ) (hE : E ≠ 0) (v : OneForm4) (hv : v ≠ 0)
    (X : ThreeTensor4 × ThreeTensor4)
    (hexists : ∃ eta A,
      X = canonicalComplexionCouplingChannels E v eta A) :
    ∃! p : OneForm4 × ℝ,
      X = canonicalComplexionCouplingChannels E v p.1 p.2 := by
  obtain ⟨eta, A, hX⟩ := hexists
  refine ⟨(eta, A), hX, ?_⟩
  intro p hp
  have hinjective := canonicalComplexionCouplingChannels_injective
    E hE v hv p.1 eta p.2 A (hp.symm.trans hX)
  exact Prod.ext hinjective.1 hinjective.2

/-- The effective one-form is read directly from four complementary
components of the complete canonical channel pair. -/
noncomputable def canonicalEffectiveOneFormFromChannels
    (E : ℝ) (X : ThreeTensor4 × ThreeTensor4) : OneForm4 :=
  ![-X.1 0 2 3 / E,
    -X.1 1 2 3 / E,
      X.2 0 1 2 / E,
      X.2 0 1 3 / E]

/-- Four numerators for the cosine-coupling component.  Dividing component
`i` by `E * v_i` returns `A` whenever that scalar-covector component is
nonzero and the raw channels are compatible. -/
noncomputable def canonicalCosineNumeratorFromChannels
    (X : ThreeTensor4 × ThreeTensor4) : OneForm4 :=
  ![-2 * X.2 0 2 3,
    -2 * X.2 1 2 3,
      2 * X.1 0 1 2,
      2 * X.1 0 1 3]

/-- Explicit cosine-coupling candidate from one nonzero component of `v`. -/
noncomputable def canonicalCosineCandidateFromChannels
    (E : ℝ) (v : OneForm4) (X : ThreeTensor4 × ThreeTensor4)
    (i : Fin 4) : ℝ :=
  canonicalCosineNumeratorFromChannels X i / (E * v i)

/-- The explicit four-component formula recovers the effective one-form from
every compatible complete channel pair. -/
theorem canonicalEffectiveOneFormFromChannels_eq
    (E : ℝ) (hE : E ≠ 0) (v eta : OneForm4) (A : ℝ)
    (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalComplexionCouplingChannels E v eta A) :
    canonicalEffectiveOneFormFromChannels E X = eta := by
  rw [hX]
  funext i
  fin_cases i <;>
    simp [canonicalEffectiveOneFormFromChannels,
      canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
      canonicalMaxwellTwoForm, canonicalHodgeStar, hE]

/-- Every nonzero scalar-covector component gives the same explicit `A` on
compatible raw channels. -/
theorem canonicalCosineCandidateFromChannels_eq
    (E : ℝ) (hE : E ≠ 0) (v eta : OneForm4) (A : ℝ)
    (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalComplexionCouplingChannels E v eta A)
    (i : Fin 4) (hvi : v i ≠ 0) :
    canonicalCosineCandidateFromChannels E v X i = A := by
  rw [hX]
  fin_cases i <;>
    simp [canonicalCosineCandidateFromChannels,
      canonicalCosineNumeratorFromChannels,
      canonicalComplexionCouplingChannels, matrixOneWedgeTwoTensor,
      canonicalMaxwellTwoForm, canonicalHodgeStar] at hvi ⊢ <;>
    field_simp [hE, hvi]

/-- A raw channel/component pair is accepted only when the chosen component
is nonzero and the complete channel pair—not merely the extraction
components—is reproduced by the explicit `(eta,A)` constructor. -/
def IsCanonicalEffectiveChannelCandidate
    (E : ℝ) (v : OneForm4) (X : ThreeTensor4 × ThreeTensor4)
    (i : Fin 4) : Prop :=
  v i ≠ 0 ∧
    X = canonicalComplexionCouplingChannels E v
      (canonicalEffectiveOneFormFromChannels E X)
      (canonicalCosineCandidateFromChannels E v X i)

/-- Compatible raw channels produce an accepted witness-free candidate from
every nonzero component of the scalar covector. -/
theorem isCanonicalEffectiveChannelCandidate_of_compatible
    (E : ℝ) (hE : E ≠ 0) (v eta : OneForm4) (A : ℝ)
    (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalComplexionCouplingChannels E v eta A)
    (i : Fin 4) (hvi : v i ≠ 0) :
    IsCanonicalEffectiveChannelCandidate E v X i := by
  constructor
  · exact hvi
  · rw [canonicalEffectiveOneFormFromChannels_eq E hE v eta A X hX,
      canonicalCosineCandidateFromChannels_eq E hE v eta A X hX i hvi]
    exact hX

/-- One nonzero component proves that the whole coordinate one-form is
nonzero. -/
theorem oneForm4_ne_zero_of_component_ne
    (v : OneForm4) (i : Fin 4) (hvi : v i ≠ 0) : v ≠ 0 := by
  intro hv
  exact hvi (congrFun hv i)

/-- Any two accepted raw-channel components reconstruct the same cosine
component.  This is the component-choice independence required by the finite
detector. -/
theorem canonicalEffectiveChannelCandidates_cosine_eq
    (E : ℝ) (hE : E ≠ 0) (v : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4) (i j : Fin 4)
    (hi : IsCanonicalEffectiveChannelCandidate E v X i)
    (hj : IsCanonicalEffectiveChannelCandidate E v X j) :
    canonicalCosineCandidateFromChannels E v X i =
      canonicalCosineCandidateFromChannels E v X j := by
  have hchannels :
      canonicalComplexionCouplingChannels E v
          (canonicalEffectiveOneFormFromChannels E X)
          (canonicalCosineCandidateFromChannels E v X i) =
        canonicalComplexionCouplingChannels E v
          (canonicalEffectiveOneFormFromChannels E X)
          (canonicalCosineCandidateFromChannels E v X j) :=
    hi.2.symm.trans hj.2
  exact (canonicalComplexionCouplingChannels_injective E hE v
    (oneForm4_ne_zero_of_component_ne v i hi.1) _ _ _ _ hchannels).2

/-- Principal reflection on covectors: negative on the Lorentzian Maxwell
plane and positive on its spacelike complement.  In a curvature
trivialization this is the normalized Maxwell residual endomorphism acting on
the cotangent representation. -/
def canonicalPrincipalReflectionCovector (v : OneForm4) : OneForm4 :=
  ![-v 0, -v 1, v 2, v 3]

/-- On the canonical electric seed, wedging with the principal-reflected
covector is the same as wedging with the original covector. -/
theorem canonicalPrincipalReflectionCovector_wedge_electric
    (E : ℝ) (v : OneForm4) :
    matrixOneWedgeTwoTensor (canonicalPrincipalReflectionCovector v)
        (canonicalMaxwellTwoForm E 0) =
      matrixOneWedgeTwoTensor v (canonicalMaxwellTwoForm E 0) := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixOneWedgeTwoTensor, canonicalPrincipalReflectionCovector,
      canonicalMaxwellTwoForm]

/-- On its canonical Hodge partner, principal reflection reverses the wedge
response. -/
theorem canonicalPrincipalReflectionCovector_wedge_hodge
    (E : ℝ) (v : OneForm4) :
    matrixOneWedgeTwoTensor (canonicalPrincipalReflectionCovector v)
        (canonicalHodgeStar E 0) =
      -matrixOneWedgeTwoTensor v (canonicalHodgeStar E 0) := by
  ext k i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixOneWedgeTwoTensor, canonicalPrincipalReflectionCovector,
      canonicalHodgeStar, canonicalMaxwellTwoForm]

/-- Linearity of the coordinate wedge channel in its one-form slot. -/
theorem matrixOneWedgeTwoTensor_add_oneForm
    (v w : OneForm4) (F : Matrix4) :
    matrixOneWedgeTwoTensor (v + w) F =
      matrixOneWedgeTwoTensor v F + matrixOneWedgeTwoTensor w F := by
  ext k i j
  simp [matrixOneWedgeTwoTensor]
  ring

/-- Scalar linearity of the coordinate wedge channel in its one-form slot. -/
theorem matrixOneWedgeTwoTensor_smul_oneForm
    (r : ℝ) (v : OneForm4) (F : Matrix4) :
    matrixOneWedgeTwoTensor (r • v) F =
      r • matrixOneWedgeTwoTensor v F := by
  ext k i j
  simp [matrixOneWedgeTwoTensor]
  ring

/-- The first-order exterior equations see this effective connection rather
than the physical complexion derivative and sine-coupling component
separately. -/
noncomputable def effectiveComplexionOneForm
    (omega Jv : OneForm4) (B : ℝ) : OneForm4 :=
  omega + (B / 2) • Jv

/-- First-order canonical channels with
`A=a cos(2 theta)` and `B=a sin(2 theta)`.  The `B` response lies in the same
four-dimensional subspace as the complexion response. -/
noncomputable def canonicalFullComplexionCouplingChannels
    (E : ℝ) (v omega : OneForm4) (A B : ℝ) :
    ThreeTensor4 × ThreeTensor4 :=
  canonicalComplexionCouplingChannels E v
    (effectiveComplexionOneForm omega
      (canonicalPrincipalReflectionCovector v) B) A

/-- The physical seed equations after rotating the EMD exterior pair back to
the canonical principal seed.  Here `A=a cos(2 theta)` and
`B=a sin(2 theta)`. -/
noncomputable def canonicalPhysicalSeedChannels
    (E : ℝ) (v omega : OneForm4) (A B : ℝ) :
    ThreeTensor4 × ThreeTensor4 :=
  let F := canonicalMaxwellTwoForm E 0
  let G := canonicalHodgeStar E 0
  ((A / 2) • matrixOneWedgeTwoTensor v F -
        matrixOneWedgeTwoTensor omega G +
      (B / 2) • matrixOneWedgeTwoTensor v G,
    matrixOneWedgeTwoTensor omega F +
        (B / 2) • matrixOneWedgeTwoTensor v F -
      (A / 2) • matrixOneWedgeTwoTensor v G)

/-- **Rotation-inversion bridge from EMD closure to detector channels.**
If the two seed equations hold after a unit duality rotation `(c,s)`, then
the unrotated derivative pair is exactly the detector's physical canonical
channel with `A=a(c²-s²)` and `B=2acs`.  This is the algebraic implication
needed to turn genuine exterior EMD closure into the packaged detector
correctness predicate. -/
theorem canonicalSeedChannels_eq_physical_of_rotatedSeedEquations
    (E : ℝ) (v omega : OneForm4) (a c s : ℝ)
    (dF0 dG0 : ThreeTensor4)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hF :
      c • dF0 + s • dG0 =
        (a / 2) • matrixOneWedgeTwoTensor v
            (c • canonicalMaxwellTwoForm E 0 +
              s • canonicalHodgeStar E 0) -
          matrixOneWedgeTwoTensor omega
            ((-s) • canonicalMaxwellTwoForm E 0 +
              c • canonicalHodgeStar E 0))
    (hG :
      (-s) • dF0 + c • dG0 =
        matrixOneWedgeTwoTensor omega
            (c • canonicalMaxwellTwoForm E 0 +
              s • canonicalHodgeStar E 0) -
          (a / 2) • matrixOneWedgeTwoTensor v
            ((-s) • canonicalMaxwellTwoForm E 0 +
              c • canonicalHodgeStar E 0)) :
    (dF0, dG0) = canonicalPhysicalSeedChannels E v omega
      (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s)) := by
  have hinvertF :
      dF0 = c • (c • dF0 + s • dG0) -
        s • ((-s) • dF0 + c • dG0) := by
    calc
      dF0 = (c ^ 2 + s ^ 2) • dF0 := by rw [hunit, one_smul]
      _ = c • (c • dF0 + s • dG0) -
          s • ((-s) • dF0 + c • dG0) := by module
  have hinvertG :
      dG0 = s • (c • dF0 + s • dG0) +
        c • ((-s) • dF0 + c • dG0) := by
    calc
      dG0 = (c ^ 2 + s ^ 2) • dG0 := by rw [hunit, one_smul]
      _ = s • (c • dF0 + s • dG0) +
          c • ((-s) • dF0 + c • dG0) := by module
  have hsquare : s ^ 2 = 1 - c ^ 2 := by
    linarith [hunit]
  apply Prod.ext
  · rw [hinvertF, hF, hG]
    ext k i j
    simp [canonicalPhysicalSeedChannels, matrixOneWedgeTwoTensor]
    ring_nf
    rw [hsquare]
    ring
  · rw [hinvertG, hF, hG]
    ext k i j
    simp [canonicalPhysicalSeedChannels, matrixOneWedgeTwoTensor]
    ring_nf
    rw [hsquare]
    ring

/-- **Effective-channel normal form.** The expanded physical seed equations
depend on `(omega,B)` only through `eta=omega+(B/2)Jv`. -/
theorem canonicalPhysicalSeedChannels_eq_full
    (E : ℝ) (v omega : OneForm4) (A B : ℝ) :
    canonicalPhysicalSeedChannels E v omega A B =
      canonicalFullComplexionCouplingChannels E v omega A B := by
  unfold canonicalPhysicalSeedChannels
    canonicalFullComplexionCouplingChannels
    canonicalComplexionCouplingChannels effectiveComplexionOneForm
  dsimp only
  simp_rw [matrixOneWedgeTwoTensor_add_oneForm,
    matrixOneWedgeTwoTensor_smul_oneForm]
  rw [canonicalPrincipalReflectionCovector_wedge_electric,
    canonicalPrincipalReflectionCovector_wedge_hodge]
  apply Prod.ext
  · ext k i j
    simp
    ring
  · ext k i j
    simp

/-- The effective connection is unchanged when `B` is shifted and `omega` is
compensated along the principal reflection of the scalar covector. -/
theorem effectiveComplexionOneForm_shear
    (omega Jv : OneForm4) (B tau : ℝ) :
    effectiveComplexionOneForm
        (omega - (tau / 2) • Jv) Jv (B + tau) =
      effectiveComplexionOneForm omega Jv B := by
  funext i
  simp [effectiveComplexionOneForm]
  ring

/-- **First-order non-identifiability theorem.** Every real shift of the
sine-coupling component can be absorbed by a corresponding shift of the
complexion one-form.  Thus no first-order channel probe can recover `B`, and
therefore no first-order channel construction can recover `a^2=A^2+B^2`,
without an additional differential condition. -/
theorem canonicalFullComplexionCouplingChannels_shear_invariant
    (E : ℝ) (v omega : OneForm4) (A B tau : ℝ) :
    canonicalFullComplexionCouplingChannels E v
        (omega - (tau / 2) • canonicalPrincipalReflectionCovector v)
        A (B + tau) =
      canonicalFullComplexionCouplingChannels E v omega A B := by
  unfold canonicalFullComplexionCouplingChannels
  rw [effectiveComplexionOneForm_shear]

/-- The physical first-order channel map is never injective in `(omega,B)`:
the shear symmetry gives two distinct inputs with exactly the same output,
independently of `E`, `v`, and `A`. -/
theorem canonicalFullComplexionCouplingChannels_not_injective
    (E : ℝ) (v : OneForm4) (A : ℝ) :
    ¬ Function.Injective
      (fun p : OneForm4 × ℝ =>
        canonicalFullComplexionCouplingChannels E v p.1 A p.2) := by
  intro hinjective
  have hchannels := canonicalFullComplexionCouplingChannels_shear_invariant
    E v 0 A 0 1
  have hpairs :
      ((0 - (1 / 2 : ℝ) • canonicalPrincipalReflectionCovector v, 0 + 1) :
          OneForm4 × ℝ) = (0, 0) :=
    hinjective hchannels
  have hscalar := congrArg Prod.snd hpairs
  norm_num at hscalar

/-- The same shear invariance stated for the expanded physical seed equations,
without the effective-channel abbreviation. -/
theorem canonicalPhysicalSeedChannels_shear_invariant
    (E : ℝ) (v omega : OneForm4) (A B tau : ℝ) :
    canonicalPhysicalSeedChannels E v
        (omega - (tau / 2) • canonicalPrincipalReflectionCovector v)
        A (B + tau) =
      canonicalPhysicalSeedChannels E v omega A B := by
  rw [canonicalPhysicalSeedChannels_eq_full,
    canonicalPhysicalSeedChannels_eq_full]
  exact canonicalFullComplexionCouplingChannels_shear_invariant
    E v omega A B tau

/-- Consequently the expanded physical first-order seed equations are never
injective in `(omega,B)`. -/
theorem canonicalPhysicalSeedChannels_not_injective
    (E : ℝ) (v : OneForm4) (A : ℝ) :
    ¬ Function.Injective
      (fun p : OneForm4 × ℝ =>
        canonicalPhysicalSeedChannels E v p.1 A p.2) := by
  intro hinjective
  apply canonicalFullComplexionCouplingChannels_not_injective E v A
  intro p p' hchannels
  apply hinjective
  simpa only [canonicalPhysicalSeedChannels_eq_full] using hchannels

/-- The next-order relation forced by constancy of the physical coupling,
written solely in terms of the effective first-order connection `eta`, the
principal-reflected scalar covector `Jv`, and `B=a sin(2 theta)`. -/
def nextOrderSineCouplingEquation
    (dA eta Jv : OneForm4) (B : ℝ) : OneForm4 :=
  dA + (2 * B) • eta - (B ^ 2) • Jv

/-- The next-order constancy equation is covariant under simultaneous
reversal of the scalar orientation and both signed coupling components. -/
theorem nextOrderSineCouplingEquation_neg_scalar
    (dA eta Jv : OneForm4) (B : ℝ) :
    nextOrderSineCouplingEquation (-dA) eta (-Jv) (-B) =
      -nextOrderSineCouplingEquation dA eta Jv B := by
  funext i
  simp [nextOrderSineCouplingEquation]
  ring

/-- If `dA=-2B omega` and `eta=omega+(B/2)Jv`, then the next-order equation
vanishes identically.  The first identity is the derivative of
`A=a cos(2 theta)` for constant `a` and `omega=dtheta`. -/
theorem nextOrderSineCouplingEquation_eq_zero
    (dA eta Jv omega : OneForm4) (B : ℝ)
    (hdA : dA = (-2 * B) • omega)
    (heta : eta = effectiveComplexionOneForm omega Jv B) :
    nextOrderSineCouplingEquation dA eta Jv B = 0 := by
  rw [hdA, heta]
  funext i
  simp [nextOrderSineCouplingEquation, effectiveComplexionOneForm]
  ring

/-- Product-rule derivative of the double-angle cosine
`A=a(c²-s²)` when the physical coupling `a` is constant. -/
def doubleAngleCosineFirstDerivative
    (a c s : ℝ) (dc ds : OneForm4) : OneForm4 :=
  (2 * a * c) • dc - (2 * a * s) • ds

/-- The unit-circle complexion equations turn the product-rule derivative of
`A=a(c²-s²)` into `dA=-2B omega`, with `B=2acs`. -/
theorem doubleAngleCosineFirstDerivative_eq
    (a c s : ℝ) (dc ds omega : OneForm4)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega) :
    doubleAngleCosineFirstDerivative a c s dc ds =
      (-2 * (a * (2 * c * s))) • omega := by
  rw [hdc, hds]
  funext i
  simp [doubleAngleCosineFirstDerivative]
  ring

/-- Coordinate component of `eta wedge Jv`. -/
def oneFormWedgeOneComponent
    (eta Jv : OneForm4) (i j : Fin 4) : ℝ :=
  eta i * Jv j - eta j * Jv i

/-- The generic fourth-order wedge is unaffected by the first-order shear
term parallel to the principal-reflected scalar covector.  Thus, on a
physical channel, the nondegenerate locus is intrinsically
`omega ∧ Jv ≠ 0`; it does not depend on the hidden sine component `B`. -/
theorem oneFormWedgeOneComponent_effectiveComplexionOneForm
    (omega Jv : OneForm4) (B : ℝ) (i j : Fin 4) :
    oneFormWedgeOneComponent
        (effectiveComplexionOneForm omega Jv B) Jv i j =
      oneFormWedgeOneComponent omega Jv i j := by
  simp [oneFormWedgeOneComponent, effectiveComplexionOneForm]
  ring

/-- Explicit recovery of `B=a sin(2 theta)` from any nondegenerate component
of the next-order equation wedged with `Jv`. -/
noncomputable def sineCouplingFromNextOrderComponent
    (dA eta Jv : OneForm4) (i j : Fin 4) : ℝ :=
  -(dA i * Jv j - dA j * Jv i) /
    (2 * oneFormWedgeOneComponent eta Jv i j)

/-- The explicit next-order quotient returns the hidden sine-coupling
component whenever the constancy equation holds and the chosen component of
`eta wedge Jv` is nonzero. -/
theorem sineCouplingFromNextOrderComponent_eq
    (dA eta Jv : OneForm4) (B : ℝ)
    (hB : nextOrderSineCouplingEquation dA eta Jv B = 0)
    (i j : Fin 4)
    (hnondegenerate : oneFormWedgeOneComponent eta Jv i j ≠ 0) :
    sineCouplingFromNextOrderComponent dA eta Jv i j = B := by
  have hBi := congrFun hB i
  have hBj := congrFun hB j
  simp [nextOrderSineCouplingEquation] at hBi hBj
  have hwB :
      dA i * Jv j - dA j * Jv i +
          2 * B * oneFormWedgeOneComponent eta Jv i j = 0 := by
    unfold oneFormWedgeOneComponent
    calc
      dA i * Jv j - dA j * Jv i +
          2 * B * (eta i * Jv j - eta j * Jv i) =
        (dA i + 2 * B * eta i - B ^ 2 * Jv i) * Jv j -
          (dA j + 2 * B * eta j - B ^ 2 * Jv j) * Jv i := by ring
      _ = 0 := by rw [hBi, hBj]; ring
  unfold sineCouplingFromNextOrderComponent
  apply (div_eq_iff (mul_ne_zero (by norm_num) hnondegenerate)).2
  nlinarith [hwB]

/-- **Generic next-order uniqueness theorem.** If `eta wedge Jv` has a
nonzero component, the fourth-order relation determines the formerly hidden
sine-coupling component `B` uniquely. -/
theorem nextOrderSineCoupling_unique
    (dA eta Jv : OneForm4) (B B' : ℝ)
    (hB : nextOrderSineCouplingEquation dA eta Jv B = 0)
    (hB' : nextOrderSineCouplingEquation dA eta Jv B' = 0)
    (i j : Fin 4)
    (hnondegenerate : oneFormWedgeOneComponent eta Jv i j ≠ 0) :
    B = B' := by
  have hBi := congrFun hB i
  have hBj := congrFun hB j
  have hB'i := congrFun hB' i
  have hB'j := congrFun hB' j
  simp [nextOrderSineCouplingEquation] at hBi hBj hB'i hB'j
  have hwB :
      dA i * Jv j - dA j * Jv i +
          2 * B * oneFormWedgeOneComponent eta Jv i j = 0 := by
    unfold oneFormWedgeOneComponent
    calc
      dA i * Jv j - dA j * Jv i +
          2 * B * (eta i * Jv j - eta j * Jv i) =
        (dA i + 2 * B * eta i - B ^ 2 * Jv i) * Jv j -
          (dA j + 2 * B * eta j - B ^ 2 * Jv j) * Jv i := by ring
      _ = 0 := by rw [hBi, hBj]; ring
  have hwB' :
      dA i * Jv j - dA j * Jv i +
          2 * B' * oneFormWedgeOneComponent eta Jv i j = 0 := by
    unfold oneFormWedgeOneComponent
    calc
      dA i * Jv j - dA j * Jv i +
          2 * B' * (eta i * Jv j - eta j * Jv i) =
        (dA i + 2 * B' * eta i - B' ^ 2 * Jv i) * Jv j -
          (dA j + 2 * B' * eta j - B' ^ 2 * Jv j) * Jv i := by ring
      _ = 0 := by rw [hB'i, hB'j]; ring
  have hzero :
      (B - B') * oneFormWedgeOneComponent eta Jv i j = 0 := by
    nlinarith [hwB, hwB']
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hzero).resolve_right hnondegenerate)

/-- Squared physical coupling reconstructed from its cosine and sine
components, without choosing a sign for the scalar orientation. -/
def couplingSqFromDoubleAngleComponents (A B : ℝ) : ℝ :=
  A ^ 2 + B ^ 2

/-- The double-angle components recover the physical squared coupling. -/
theorem couplingSqFromDoubleAngleComponents_eq
    (a c s : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) :
    couplingSqFromDoubleAngleComponents
        (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s)) = a ^ 2 := by
  unfold couplingSqFromDoubleAngleComponents
  calc
    (a * (c ^ 2 - s ^ 2)) ^ 2 + (a * (2 * c * s)) ^ 2 =
        a ^ 2 * (c ^ 2 + s ^ 2) ^ 2 := by ring
    _ = a ^ 2 := by rw [hunit]; ring

/-- The complete fourth-order squared-coupling constructor, using the
first-order cosine component and one nondegenerate next-order component. -/
noncomputable def couplingSqFromNextOrderComponent
    (A : ℝ) (dA eta Jv : OneForm4) (i j : Fin 4) : ℝ :=
  couplingSqFromDoubleAngleComponents A
    (sineCouplingFromNextOrderComponent dA eta Jv i j)

/-- On a constant-coupling EMD channel, the explicit next-order constructor
returns the physical squared coupling. -/
theorem couplingSqFromNextOrderComponent_eq
    (A B a c s : ℝ) (dA eta Jv : OneForm4) (i j : Fin 4)
    (hA : A = a * (c ^ 2 - s ^ 2))
    (hBvalue : B = a * (2 * c * s))
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hequation : nextOrderSineCouplingEquation dA eta Jv B = 0)
    (hnondegenerate : oneFormWedgeOneComponent eta Jv i j ≠ 0) :
    couplingSqFromNextOrderComponent A dA eta Jv i j = a ^ 2 := by
  rw [couplingSqFromNextOrderComponent,
    sineCouplingFromNextOrderComponent_eq dA eta Jv B hequation i j
      hnondegenerate,
    hA, hBvalue]
  exact couplingSqFromDoubleAngleComponents_eq a c s hunit

/-- A finite detector choice consists of one scalar-covector component for
the first-channel quotient and one ordered two-component choice for the
next-order wedge quotient.  There are only `4^3` such raw choices; invalid
choices are rejected by `IsFourthOrderChannelCandidate`. -/
abbrev FourthOrderComponentChoice := Fin 4 × (Fin 4 × Fin 4)

/-- A nonzero component of the intrinsic fourth-order wedge automatically
supplies every finite quotient index needed by the detector.  In particular,
the active wedge already forces the scalar covector to be nonzero, so no
separate source-component hypothesis is required. -/
theorem exists_fourthOrderComponentChoice_of_activeWedge
    (eta v : OneForm4)
    (hactive : ∃ left right : Fin 4,
      oneFormWedgeOneComponent eta
        (canonicalPrincipalReflectionCovector v) left right ≠ 0) :
    ∃ choice : FourthOrderComponentChoice,
      v choice.1 ≠ 0 ∧
      oneFormWedgeOneComponent eta
        (canonicalPrincipalReflectionCovector v)
        choice.2.1 choice.2.2 ≠ 0 := by
  obtain ⟨left, right, hwedge⟩ := hactive
  have hv : v ≠ 0 := by
    intro hv
    subst v
    have hreflection : canonicalPrincipalReflectionCovector (0 : OneForm4) = 0 := by
      funext i
      fin_cases i <;> simp [canonicalPrincipalReflectionCovector]
    rw [hreflection] at hwedge
    exact hwedge (by simp [oneFormWedgeOneComponent])
  obtain ⟨source, hvsource⟩ := exists_oneForm4_component_ne_zero v hv
  exact ⟨(source, (left, right)), hvsource, hwedge⟩

/-- The finite source/wedge enumeration is nonempty exactly on the intrinsic
active-wedge locus. -/
theorem exists_fourthOrderComponentChoice_iff_activeWedge
    (eta v : OneForm4) :
    (∃ choice : FourthOrderComponentChoice,
      v choice.1 ≠ 0 ∧
      oneFormWedgeOneComponent eta
        (canonicalPrincipalReflectionCovector v)
        choice.2.1 choice.2.2 ≠ 0) ↔
      ∃ left right : Fin 4,
        oneFormWedgeOneComponent eta
          (canonicalPrincipalReflectionCovector v) left right ≠ 0 := by
  constructor
  · rintro ⟨choice, _, hwedge⟩
    exact ⟨choice.2.1, choice.2.2, hwedge⟩
  · exact exists_fourthOrderComponentChoice_of_activeWedge eta v

/-- The principal reflection used by the fourth-order denominator preserves
continuity of a covector field.  Writing this elementary fact explicitly
lets the active-locus theorem below avoid any coordinate-free regularity
assumption hidden inside the finite component search. -/
theorem continuousAt_canonicalPrincipalReflectionCovector
    {X : Type*} [TopologicalSpace X]
    (v : X → OneForm4) (z : X) (hv : ContinuousAt v z) :
    ContinuousAt (fun y ↦ canonicalPrincipalReflectionCovector (v y)) z := by
  apply continuousAt_pi.mpr
  intro i
  have hi := continuousAt_pi.mp hv i
  fin_cases i
  · change ContinuousAt (fun y ↦ -v y 0) z
    exact hi.neg
  · change ContinuousAt (fun y ↦ -v y 1) z
    exact hi.neg
  · change ContinuousAt (fun y ↦ v y 2) z
    exact hi
  · change ContinuousAt (fun y ↦ v y 3) z
    exact hi

/-- **Openness of one active fourth-order chart.**  If one enumerated wedge
component is nonzero at a point, the same fixed component remains nonzero on
a smaller neighborhood whenever the two underlying covector fields are
continuous.  Thus the existential finite-channel condition is a genuine
open regular locus, not a pointwise choice that may jump arbitrarily. -/
theorem eventually_oneFormWedgeOneComponent_ne_zero
    {X : Type*} [TopologicalSpace X]
    (eta v : X → OneForm4) (z : X) (left right : Fin 4)
    (heta : ContinuousAt eta z) (hv : ContinuousAt v z)
    (hactive : oneFormWedgeOneComponent (eta z)
      (canonicalPrincipalReflectionCovector (v z)) left right ≠ 0) :
    ∀ᶠ y in nhds z,
      oneFormWedgeOneComponent (eta y)
        (canonicalPrincipalReflectionCovector (v y)) left right ≠ 0 := by
  have hJ := continuousAt_canonicalPrincipalReflectionCovector v z hv
  have hwedge : ContinuousAt
      (fun y ↦ oneFormWedgeOneComponent (eta y)
        (canonicalPrincipalReflectionCovector (v y)) left right) z := by
    unfold oneFormWedgeOneComponent
    exact ((continuousAt_pi.mp heta left).mul
      (continuousAt_pi.mp hJ right)).sub
        ((continuousAt_pi.mp heta right).mul
          (continuousAt_pi.mp hJ left))
  simpa only [Pi.zero_apply] using
    (hwedge.ne_iff_eventually_ne continuousAt_const).mp hactive

/-- A fixed nonzero component of a continuous covector field remains a valid
quotient source on a smaller neighborhood.  This is the source-component
counterpart of the active-wedge openness theorem above. -/
theorem eventually_oneForm4_component_ne_zero
    {X : Type*} [TopologicalSpace X]
    (v : X → OneForm4) (z : X) (source : Fin 4)
    (hv : ContinuousAt v z) (hsource : v z source ≠ 0) :
    ∀ᶠ y in nhds z, v y source ≠ 0 := by
  have hcomponent := continuousAt_pi.mp hv source
  simpa only [Pi.zero_apply] using
    (hcomponent.ne_iff_eventually_ne continuousAt_const).mp hsource

/-- The hidden sine component obtained from raw first-order channels and the
next derivative of their explicitly reconstructed cosine component.  The
principal-reflected covector is constructed from the supplied scalar
covector, rather than passed in as extra data. -/
noncomputable def fourthOrderSineCandidate
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  sineCouplingFromNextOrderComponent dA
    (canonicalEffectiveOneFormFromChannels E X)
    (canonicalPrincipalReflectionCovector v)
    choice.2.1 choice.2.2

/-- Squared coupling attached to one raw finite component choice. -/
noncomputable def fourthOrderCouplingSqCandidate
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  couplingSqFromDoubleAngleComponents
    (canonicalCosineCandidateFromChannels E v X choice.1)
    (fourthOrderSineCandidate E v dA X choice)

/-- Reversing the reconstructed scalar orientation reverses the explicit
cosine candidate. -/
theorem canonicalCosineCandidateFromChannels_neg_scalar
    (E : ℝ) (v : OneForm4) (X : ThreeTensor4 × ThreeTensor4)
    (i : Fin 4) :
    canonicalCosineCandidateFromChannels E (-v) X i =
      -canonicalCosineCandidateFromChannels E v X i := by
  unfold canonicalCosineCandidateFromChannels
  rw [show E * (-v) i = -(E * v i) by simp, div_neg]

/-- Reversing both the scalar covector and the signed cosine component leaves
the complete raw first-order channel pair unchanged. -/
theorem canonicalComplexionCouplingChannels_neg_scalar_cosine
    (E : ℝ) (v eta : OneForm4) (A : ℝ) :
    canonicalComplexionCouplingChannels E (-v) eta (-A) =
      canonicalComplexionCouplingChannels E v eta A := by
  apply Prod.ext <;> ext i j k <;>
    simp [canonicalComplexionCouplingChannels,
      matrixOneWedgeTwoTensor] <;> ring

/-- Principal reflection commutes with scalar-orientation reversal. -/
theorem canonicalPrincipalReflectionCovector_neg (v : OneForm4) :
    canonicalPrincipalReflectionCovector (-v) =
      -canonicalPrincipalReflectionCovector v := by
  funext i
  fin_cases i <;> simp [canonicalPrincipalReflectionCovector]

/-- Reversing both the scalar covector and the actual derivative of its
cosine channel reverses the recovered sine candidate. -/
theorem fourthOrderSineCandidate_neg_scalar
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice : FourthOrderComponentChoice) :
    fourthOrderSineCandidate E (-v) (-dA) X choice =
      -fourthOrderSineCandidate E v dA X choice := by
  rw [fourthOrderSineCandidate, fourthOrderSineCandidate,
    canonicalPrincipalReflectionCovector_neg]
  simp only [sineCouplingFromNextOrderComponent,
    oneFormWedgeOneComponent, Pi.neg_apply]
  rw [show
    2 *
        (canonicalEffectiveOneFormFromChannels E X choice.2.1 *
            (-canonicalPrincipalReflectionCovector v choice.2.2) -
          canonicalEffectiveOneFormFromChannels E X choice.2.2 *
            (-canonicalPrincipalReflectionCovector v choice.2.1)) =
      -(2 *
        (canonicalEffectiveOneFormFromChannels E X choice.2.1 *
            canonicalPrincipalReflectionCovector v choice.2.2 -
          canonicalEffectiveOneFormFromChannels E X choice.2.2 *
            canonicalPrincipalReflectionCovector v choice.2.1)) by ring,
    div_neg]
  ring

/-- **Scalar-orientation independence.** The complete fourth-order squared
coupling is unchanged when the curvature-reconstructed scalar covector and
its actual cosine-channel derivative are both reversed. -/
theorem fourthOrderCouplingSqCandidate_neg_scalar
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice : FourthOrderComponentChoice) :
    fourthOrderCouplingSqCandidate E (-v) (-dA) X choice =
      fourthOrderCouplingSqCandidate E v dA X choice := by
  unfold fourthOrderCouplingSqCandidate
  rw [canonicalCosineCandidateFromChannels_neg_scalar,
    fourthOrderSineCandidate_neg_scalar]
  simp [couplingSqFromDoubleAngleComponents]

/-- Exact acceptance predicate for a fourth-order detector branch.  It checks
the non-null seed, exact reproduction of *all* first-order channels, a
nonzero next-order wedge denominator, and the complete four-component
constancy equation.  Thus the components not used in the two quotients are
obstruction equations rather than discarded data. -/
def IsFourthOrderChannelCandidate
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice : FourthOrderComponentChoice) : Prop :=
  E ≠ 0 ∧
  IsCanonicalEffectiveChannelCandidate E v X choice.1 ∧
  oneFormWedgeOneComponent
      (canonicalEffectiveOneFormFromChannels E X)
      (canonicalPrincipalReflectionCovector v)
      choice.2.1 choice.2.2 ≠ 0 ∧
  nextOrderSineCouplingEquation dA
      (canonicalEffectiveOneFormFromChannels E X)
      (canonicalPrincipalReflectionCovector v)
      (fourthOrderSineCandidate E v dA X choice) = 0

/-- The actual finite set of accepted detector choices.  It has at most 64
elements before component-choice independence collapses all accepted outputs
to one squared coupling. -/
noncomputable def acceptedFourthOrderChannelChoices
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4) :
    Finset FourthOrderComponentChoice := by
  classical
  exact Finset.univ.filter
    (IsFourthOrderChannelCandidate E v dA X)

/-- Compatible first-order channels and the genuine next-order constancy
equation produce an accepted finite detector branch from every pair of
nonzero quotient denominators. -/
theorem isFourthOrderChannelCandidate_of_compatible
    (E : ℝ) (hE : E ≠ 0) (v eta dA : OneForm4) (A B : ℝ)
    (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalComplexionCouplingChannels E v eta A)
    (source left right : Fin 4) (hvsource : v source ≠ 0)
    (hequation : nextOrderSineCouplingEquation dA eta
      (canonicalPrincipalReflectionCovector v) B = 0)
    (hnondegenerate : oneFormWedgeOneComponent eta
      (canonicalPrincipalReflectionCovector v) left right ≠ 0) :
    IsFourthOrderChannelCandidate E v dA X
      (source, (left, right)) := by
  have heta := canonicalEffectiveOneFormFromChannels_eq
    E hE v eta A X hX
  have hfirst := isCanonicalEffectiveChannelCandidate_of_compatible
    E hE v eta A X hX source hvsource
  have hB := sineCouplingFromNextOrderComponent_eq dA eta
    (canonicalPrincipalReflectionCovector v) B hequation left right
    hnondegenerate
  refine ⟨hE, hfirst, ?_, ?_⟩
  · simpa only [heta] using hnondegenerate
  · unfold fourthOrderSineCandidate
    simpa only [heta, hB] using hequation

/-- Every accepted finite branch belongs to the explicitly filtered detector
output. -/
theorem mem_acceptedFourthOrderChannelChoices_iff
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice : FourthOrderComponentChoice) :
    choice ∈ acceptedFourthOrderChannelChoices E v dA X ↔
      IsFourthOrderChannelCandidate E v dA X choice := by
  classical
  simp [acceptedFourthOrderChannelChoices]

/-- Any two accepted component choices reconstruct the same hidden sine
component. -/
theorem fourthOrderSineCandidates_eq
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice choice' : FourthOrderComponentChoice)
    (hchoice : IsFourthOrderChannelCandidate E v dA X choice)
    (hchoice' : IsFourthOrderChannelCandidate E v dA X choice') :
    fourthOrderSineCandidate E v dA X choice =
      fourthOrderSineCandidate E v dA X choice' := by
  exact nextOrderSineCoupling_unique dA
    (canonicalEffectiveOneFormFromChannels E X)
    (canonicalPrincipalReflectionCovector v)
    (fourthOrderSineCandidate E v dA X choice)
    (fourthOrderSineCandidate E v dA X choice')
    hchoice.2.2.2 hchoice'.2.2.2 choice.2.1 choice.2.2
    hchoice.2.2.1

/-- **Finite-branch confluence theorem.** All accepted raw component choices
return exactly the same squared coupling.  Hence the generic detector has a
single geometric output even though it is implemented as a finite family of
quotients and obstruction checks. -/
theorem fourthOrderCouplingSqCandidates_eq
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4)
    (choice choice' : FourthOrderComponentChoice)
    (hchoice : IsFourthOrderChannelCandidate E v dA X choice)
    (hchoice' : IsFourthOrderChannelCandidate E v dA X choice') :
    fourthOrderCouplingSqCandidate E v dA X choice =
      fourthOrderCouplingSqCandidate E v dA X choice' := by
  unfold fourthOrderCouplingSqCandidate
  rw [canonicalEffectiveChannelCandidates_cosine_eq E hchoice.1 v X
      choice.1 choice'.1 hchoice.2.1 hchoice'.2.1,
    fourthOrderSineCandidates_eq E v dA X choice choice' hchoice hchoice']

/-- On genuine constant-coupling data every accepted explicit branch returns
the physical invariant `a^2`. -/
theorem fourthOrderCouplingSqCandidate_eq_physical
    (E : ℝ) (hE : E ≠ 0) (v eta dA : OneForm4)
    (A B a c s : ℝ) (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalComplexionCouplingChannels E v eta A)
    (hA : A = a * (c ^ 2 - s ^ 2))
    (hBvalue : B = a * (2 * c * s))
    (hunit : c ^ 2 + s ^ 2 = 1)
    (source left right : Fin 4) (hvsource : v source ≠ 0)
    (hequation : nextOrderSineCouplingEquation dA eta
      (canonicalPrincipalReflectionCovector v) B = 0)
    (hnondegenerate : oneFormWedgeOneComponent eta
      (canonicalPrincipalReflectionCovector v) left right ≠ 0) :
    fourthOrderCouplingSqCandidate E v dA X
        (source, (left, right)) = a ^ 2 := by
  unfold fourthOrderCouplingSqCandidate fourthOrderSineCandidate
  rw [canonicalCosineCandidateFromChannels_eq E hE v eta A X hX
      source hvsource,
    canonicalEffectiveOneFormFromChannels_eq E hE v eta A X hX]
  exact couplingSqFromNextOrderComponent_eq A B a c s dA eta
    (canonicalPrincipalReflectionCovector v) left right hA hBvalue hunit
    hequation hnondegenerate

/-- A raw channel pair is a genuine constant-coupling physical channel with
coupling `a` when it admits double-angle data whose first-order channel and
next-order constancy equation are exact.  This predicate is used only in the
correctness theorem; it is not an input to the detector. -/
def IsPhysicalConstantCouplingChannel
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4) (a : ℝ) : Prop :=
  ∃ eta A B c s,
    X = canonicalComplexionCouplingChannels E v eta A ∧
    A = a * (c ^ 2 - s ^ 2) ∧
    B = a * (2 * c * s) ∧
    c ^ 2 + s ^ 2 = 1 ∧
    nextOrderSineCouplingEquation dA eta
      (canonicalPrincipalReflectionCovector v) B = 0

/-- **Physical-channel scalar-orientation covariance.** Reversing the
reconstructed scalar covector and its cosine-channel derivative reverses the
signed EMD coupling, while leaving the raw curvature channels and the
orientation-free squared coupling unchanged. -/
theorem isPhysicalConstantCouplingChannel_neg_scalar
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4) (a : ℝ) :
    IsPhysicalConstantCouplingChannel E (-v) (-dA) X (-a) ↔
      IsPhysicalConstantCouplingChannel E v dA X a := by
  constructor
  · rintro ⟨eta, A, B, c, s, hX, hA, hB, hunit, hequation⟩
    refine ⟨eta, -A, -B, c, s, ?_, ?_, ?_, hunit, ?_⟩
    · calc
        X = canonicalComplexionCouplingChannels E (-v) eta A := hX
        _ = canonicalComplexionCouplingChannels E v eta (-A) := by
          simpa using
            canonicalComplexionCouplingChannels_neg_scalar_cosine
              E v eta (-A)
    · nlinarith
    · nlinarith
    · have hneg := congrArg Neg.neg hequation
      rw [← nextOrderSineCouplingEquation_neg_scalar,
        canonicalPrincipalReflectionCovector_neg] at hneg
      simpa using hneg
  · rintro ⟨eta, A, B, c, s, hX, hA, hB, hunit, hequation⟩
    refine ⟨eta, -A, -B, c, s, ?_, ?_, ?_, hunit, ?_⟩
    · calc
        X = canonicalComplexionCouplingChannels E v eta A := hX
        _ = canonicalComplexionCouplingChannels E (-v) eta (-A) :=
          (canonicalComplexionCouplingChannels_neg_scalar_cosine
            E v eta A).symm
    · nlinarith
    · nlinarith
    · rw [canonicalPrincipalReflectionCovector_neg,
        nextOrderSineCouplingEquation_neg_scalar, hequation, neg_zero]

/-- **Exterior-to-correctness packaging.**  Once a raw pair has the physical
seed-channel normal form and the differentiated double-angle cosine obeys
`dA=-2B omega`, it supplies exactly the physical witness required by the
accepted-branch correctness theorem.  In particular, neither `eta` nor the
hidden sine component is an independent detector input. -/
theorem isPhysicalConstantCouplingChannel_of_physicalSeedChannels
    (E : ℝ) (v omega dA : OneForm4)
    (A B a c s : ℝ) (X : ThreeTensor4 × ThreeTensor4)
    (hX : X = canonicalPhysicalSeedChannels E v omega A B)
    (hA : A = a * (c ^ 2 - s ^ 2))
    (hB : B = a * (2 * c * s))
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdA : dA = (-2 * B) • omega) :
    IsPhysicalConstantCouplingChannel E v dA X a := by
  refine ⟨effectiveComplexionOneForm omega
      (canonicalPrincipalReflectionCovector v) B,
    A, B, c, s, ?_, hA, hB, hunit, ?_⟩
  · calc
      X = canonicalPhysicalSeedChannels E v omega A B := hX
      _ = canonicalFullComplexionCouplingChannels E v omega A B :=
        canonicalPhysicalSeedChannels_eq_full E v omega A B
      _ = canonicalComplexionCouplingChannels E v
          (effectiveComplexionOneForm omega
            (canonicalPrincipalReflectionCovector v) B) A := rfl
  · exact nextOrderSineCouplingEquation_eq_zero dA
      (effectiveComplexionOneForm omega
        (canonicalPrincipalReflectionCovector v) B)
      (canonicalPrincipalReflectionCovector v) omega B hdA rfl

/-- A physical-channel witness plus the two explicit generic component
conditions constructs an accepted member of the finite detector. -/
theorem isFourthOrderChannelCandidate_of_physical
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4) (a : ℝ)
    (source left right : Fin 4)
    (hE : E ≠ 0) (hvsource : v source ≠ 0)
    (hphysical : IsPhysicalConstantCouplingChannel E v dA X a)
    (hnondegenerate : oneFormWedgeOneComponent
      (canonicalEffectiveOneFormFromChannels E X)
      (canonicalPrincipalReflectionCovector v) left right ≠ 0) :
    IsFourthOrderChannelCandidate E v dA X
      (source, (left, right)) := by
  rcases hphysical with
    ⟨eta, A, B, c, s, hX, hA, hB, hunit, hequation⟩
  have heta := canonicalEffectiveOneFormFromChannels_eq
    E hE v eta A X hX
  apply isFourthOrderChannelCandidate_of_compatible
    E hE v eta dA A B X hX source left right hvsource hequation
  simpa only [heta] using hnondegenerate

/-- **Accepted-channel physical correctness.** Once the finite detector
accepts a raw branch, genuine constant-coupling channel compatibility alone
forces its output to be the physical invariant `a²`; no quotient component
or scalar orientation is supplied separately. -/
theorem fourthOrderCouplingSqCandidate_eq_physical_of_acceptance
    (E : ℝ) (v dA : OneForm4)
    (X : ThreeTensor4 × ThreeTensor4) (a : ℝ)
    (choice : FourthOrderComponentChoice)
    (hchoice : IsFourthOrderChannelCandidate E v dA X choice)
    (hphysical : IsPhysicalConstantCouplingChannel E v dA X a) :
    fourthOrderCouplingSqCandidate E v dA X choice = a ^ 2 := by
  rcases hphysical with
    ⟨eta, A, B, c, s, hX, hA, hB, hunit, hequation⟩
  have heta := canonicalEffectiveOneFormFromChannels_eq
    E hchoice.1 v eta A X hX
  have hnondegenerate :
      oneFormWedgeOneComponent eta
        (canonicalPrincipalReflectionCovector v)
        choice.2.1 choice.2.2 ≠ 0 := by
    simpa only [heta] using hchoice.2.2.1
  exact fourthOrderCouplingSqCandidate_eq_physical
    E hchoice.1 v eta dA A B a c s X hX hA hB hunit
    choice.1 choice.2.1 choice.2.2 hchoice.2.1.1
    hequation hnondegenerate

/-- Pull a coordinate covector back to the supplied principal coframe.  When
`K` is the inverse of the coframe matrix `L`, this is the ordinary `K^T`
covector transformation. -/
noncomputable def pullCovectorToPrincipalFrame
    (K : Matrix4) (v : OneForm4) : OneForm4 :=
  fun a => ∑ i, K i a * v i

/-- Principal-frame covector pullback commutes with scalar multiplication. -/
theorem pullCovectorToPrincipalFrame_smul
    (K : Matrix4) (r : ℝ) (v : OneForm4) :
    pullCovectorToPrincipalFrame K (r • v) =
      r • pullCovectorToPrincipalFrame K v := by
  funext a
  simp only [pullCovectorToPrincipalFrame, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, K i a * (r * v i)) =
        ∑ i, r * (K i a * v i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = r * ∑ i, K i a * v i := by
      simp only [Finset.mul_sum]

/-- Pull all three covariant slots of a coordinate three-form back to the
supplied principal coframe. -/
noncomputable def pullThreeTensorToPrincipalFrame
    (K : Matrix4) (H : ThreeTensor4) : ThreeTensor4 :=
  fun a b c => ∑ i, ∑ j, ∑ k,
    K i a * K j b * K k c * H i j k

/-- Pullback is additive on coordinate three-tensors. -/
theorem pullThreeTensorToPrincipalFrame_add
    (K : Matrix4) (H J : ThreeTensor4) :
    pullThreeTensorToPrincipalFrame K (H + J) =
      pullThreeTensorToPrincipalFrame K H +
        pullThreeTensorToPrincipalFrame K J := by
  ext a b c
  simp only [pullThreeTensorToPrincipalFrame, Pi.add_apply]
  calc
    (∑ i, ∑ j, ∑ k,
        K i a * K j b * K k c * (H i j k + J i j k)) =
        ∑ i, ∑ j, ∑ k,
          (K i a * K j b * K k c * H i j k +
            K i a * K j b * K k c * J i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (∑ i, ∑ j, ∑ k, K i a * K j b * K k c * H i j k) +
        ∑ i, ∑ j, ∑ k, K i a * K j b * K k c * J i j k := by
      simp only [Finset.sum_add_distrib]

/-- Pullback commutes with scalar multiplication. -/
theorem pullThreeTensorToPrincipalFrame_smul
    (K : Matrix4) (r : ℝ) (H : ThreeTensor4) :
    pullThreeTensorToPrincipalFrame K (r • H) =
      r • pullThreeTensorToPrincipalFrame K H := by
  ext a b c
  simp only [pullThreeTensorToPrincipalFrame, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, ∑ j, ∑ k,
        K i a * K j b * K k c * (r * H i j k)) =
        ∑ i, ∑ j, ∑ k,
          r * (K i a * K j b * K k c * H i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = r * ∑ i, ∑ j, ∑ k,
        K i a * K j b * K k c * H i j k := by
      simp only [Finset.mul_sum]

/-- Pullback is compatible with subtraction. -/
theorem pullThreeTensorToPrincipalFrame_sub
    (K : Matrix4) (H J : ThreeTensor4) :
    pullThreeTensorToPrincipalFrame K (H - J) =
      pullThreeTensorToPrincipalFrame K H -
        pullThreeTensorToPrincipalFrame K J := by
  rw [sub_eq_add_neg, pullThreeTensorToPrincipalFrame_add,
    ← neg_one_smul ℝ J, pullThreeTensorToPrincipalFrame_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

/-- Covariant two-form transport is additive. -/
theorem transportTwoForm_add_detector
    (L F G : Matrix4) :
    transportTwoForm L (F + G) =
      transportTwoForm L F + transportTwoForm L G := by
  simp [transportTwoForm, Matrix.mul_add, Matrix.add_mul]

/-- Pullback commutes with the coordinate wedge of a covector and a
two-form.  This is the component-level naturality identity needed to move
the EMD seed equations from the chart frame into the detector's principal
frame. -/
theorem pullThreeTensor_matrixOneWedgeTwoTensor
    (K : Matrix4) (v : OneForm4) (F : Matrix4) :
    pullThreeTensorToPrincipalFrame K
        (matrixOneWedgeTwoTensor v F) =
      matrixOneWedgeTwoTensor (pullCovectorToPrincipalFrame K v)
        (transportTwoForm K F) := by
  ext a b c
  simp [pullThreeTensorToPrincipalFrame, matrixOneWedgeTwoTensor,
    pullCovectorToPrincipalFrame, transportTwoForm, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- If `K` is a supplied right inverse of the coframe `L`, pulling a wedge
whose two-form was transported by `L` returns the canonical two-form while
pulling its covector coefficient. -/
theorem pullThreeTensor_matrixOneWedgeTwoTensor_transport
    (L K : Matrix4) (v : OneForm4) (F : Matrix4)
    (hLK : L * K = 1) :
    pullThreeTensorToPrincipalFrame K
        (matrixOneWedgeTwoTensor v (transportTwoForm L F)) =
      matrixOneWedgeTwoTensor (pullCovectorToPrincipalFrame K v) F := by
  rw [pullThreeTensor_matrixOneWedgeTwoTensor]
  have htransport :
      transportTwoForm K (transportTwoForm L F) = F := by
    rw [← transportTwoForm_mul K L F, hLK]
    simp [transportTwoForm]
  rw [htransport]

/-- The complete raw seed-derivative pair, computed from the transported
positive-`q` Ricci seed and then expressed in its canonical principal frame.
This is the geometric splice between `LocalExteriorSeed` and the finite
channel detector; no complexion, coupling, or matter two-form is an input. -/
noncomputable def transportedPositiveQCanonicalSeedChannels
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq : OneForm4) : ThreeTensor4 × ThreeTensor4 :=
  (pullThreeTensorToPrincipalFrame K
      (localPositiveQSeedExteriorDerivative L dL q dq),
    pullThreeTensorToPrincipalFrame K
      (localPositiveQHodgeSeedExteriorDerivative L dL q dq))

/-- **Transported rotation-inversion bridge.**  Rotated EMD seed equations
in the coordinate frame force the actual transported curvature-seed jets,
after pullback by the inverse coframe, into the detector's physical canonical
channel.  This is the frame-covariant version of
`canonicalSeedChannels_eq_physical_of_rotatedSeedEquations`. -/
theorem transportedPositiveQCanonicalSeedChannels_eq_physical_of_rotatedSeedEquations
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega : OneForm4) (a c s : ℝ)
    (hLK : L * K = 1)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hF :
      c • localPositiveQSeedExteriorDerivative L dL q dq +
          s • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
        (a / 2) • matrixOneWedgeTwoTensor v
            (c • transportTwoForm L
                (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
              s • transportTwoForm L
                (canonicalHodgeStar (Real.sqrt (2 * q)) 0)) -
          matrixOneWedgeTwoTensor omega
            ((-s) • transportTwoForm L
                (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
              c • transportTwoForm L
                (canonicalHodgeStar (Real.sqrt (2 * q)) 0)))
    (hG :
      (-s) • localPositiveQSeedExteriorDerivative L dL q dq +
          c • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
        matrixOneWedgeTwoTensor omega
            (c • transportTwoForm L
                (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
              s • transportTwoForm L
                (canonicalHodgeStar (Real.sqrt (2 * q)) 0)) -
          (a / 2) • matrixOneWedgeTwoTensor v
            ((-s) • transportTwoForm L
                (canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0) +
              c • transportTwoForm L
                (canonicalHodgeStar (Real.sqrt (2 * q)) 0))) :
    transportedPositiveQCanonicalSeedChannels L K dL q dq =
      canonicalPhysicalSeedChannels (Real.sqrt (2 * q))
        (pullCovectorToPrincipalFrame K v)
        (pullCovectorToPrincipalFrame K omega)
        (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s)) := by
  let F := canonicalMaxwellTwoForm (Real.sqrt (2 * q)) 0
  let G := canonicalHodgeStar (Real.sqrt (2 * q)) 0
  have hrotF :
      c • transportTwoForm L F + s • transportTwoForm L G =
        transportTwoForm L (c • F + s • G) := by
    rw [transportTwoForm_add_detector, transportTwoForm_smul,
      transportTwoForm_smul]
  have hrotG :
      (-s) • transportTwoForm L F + c • transportTwoForm L G =
        transportTwoForm L ((-s) • F + c • G) := by
    rw [transportTwoForm_add_detector, transportTwoForm_smul,
      transportTwoForm_smul]
  change c • localPositiveQSeedExteriorDerivative L dL q dq +
      s • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
        (a / 2) • matrixOneWedgeTwoTensor v
            (c • transportTwoForm L F + s • transportTwoForm L G) -
          matrixOneWedgeTwoTensor omega
            ((-s) • transportTwoForm L F + c • transportTwoForm L G) at hF
  change (-s) • localPositiveQSeedExteriorDerivative L dL q dq +
      c • localPositiveQHodgeSeedExteriorDerivative L dL q dq =
        matrixOneWedgeTwoTensor omega
            (c • transportTwoForm L F + s • transportTwoForm L G) -
          (a / 2) • matrixOneWedgeTwoTensor v
            ((-s) • transportTwoForm L F + c • transportTwoForm L G) at hG
  rw [hrotF, hrotG] at hF hG
  have hpF := congrArg (pullThreeTensorToPrincipalFrame K) hF
  have hpG := congrArg (pullThreeTensorToPrincipalFrame K) hG
  have hpF' :
      c • pullThreeTensorToPrincipalFrame K
            (localPositiveQSeedExteriorDerivative L dL q dq) +
          s • pullThreeTensorToPrincipalFrame K
            (localPositiveQHodgeSeedExteriorDerivative L dL q dq) =
        (a / 2) • matrixOneWedgeTwoTensor
            (pullCovectorToPrincipalFrame K v) (c • F + s • G) -
          matrixOneWedgeTwoTensor
            (pullCovectorToPrincipalFrame K omega) ((-s) • F + c • G) := by
    simpa only [pullThreeTensorToPrincipalFrame_add,
      pullThreeTensorToPrincipalFrame_smul,
      pullThreeTensorToPrincipalFrame_sub,
      pullThreeTensor_matrixOneWedgeTwoTensor_transport L K _ _ hLK]
      using hpF
  have hpG' :
      (-s) • pullThreeTensorToPrincipalFrame K
            (localPositiveQSeedExteriorDerivative L dL q dq) +
          c • pullThreeTensorToPrincipalFrame K
            (localPositiveQHodgeSeedExteriorDerivative L dL q dq) =
        matrixOneWedgeTwoTensor
            (pullCovectorToPrincipalFrame K omega) (c • F + s • G) -
          (a / 2) • matrixOneWedgeTwoTensor
            (pullCovectorToPrincipalFrame K v) ((-s) • F + c • G) := by
    simpa only [pullThreeTensorToPrincipalFrame_add,
      pullThreeTensorToPrincipalFrame_smul,
      pullThreeTensorToPrincipalFrame_sub,
      pullThreeTensor_matrixOneWedgeTwoTensor_transport L K _ _ hLK]
      using hpG
  unfold transportedPositiveQCanonicalSeedChannels
  change (_, _) = canonicalPhysicalSeedChannels (Real.sqrt (2 * q))
    (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K omega)
    (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s))
  exact canonicalSeedChannels_eq_physical_of_rotatedSeedEquations
    (Real.sqrt (2 * q)) (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K omega) a c s _ _ hunit hpF' hpG'

/-- **Genuine EMD closure enters the finite detector.**  The local EMD
Bianchi/Maxwell closure of the transported curvature seed implies the exact
physical canonical-channel normal form used by the fourth-order detector.
The conclusion contains only the actual curvature-seed jets and pulled-back
scalar covectors; the matter forms and coupling occur only in this converse
correctness hypothesis. -/
theorem transportedPositiveQCanonicalSeedChannels_eq_physical_of_emdClosure
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega : OneForm4) (a c s : ℝ)
    (dc ds : OneForm4)
    (hLK : L * K = 1)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hclosure :
      let J := localPositiveQExteriorDualityJet
        L dL q dq c s dc ds
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo)) :
    transportedPositiveQCanonicalSeedChannels L K dL q dq =
      canonicalPhysicalSeedChannels (Real.sqrt (2 * q))
        (pullCovectorToPrincipalFrame K v)
        (pullCovectorToPrincipalFrame K omega)
        (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s)) := by
  have hseed :=
    (localPositiveQ_emdClosure_iff_seedChannels
      L dL q dq omega v c s a dc ds hdc hds).mp hclosure
  dsimp only [localPositiveQExteriorDualityJet,
    ExteriorDualityJet.rotatedSeedDF,
    ExteriorDualityJet.rotatedSeedDG,
    ExteriorDualityJet.rotatedF,
    ExteriorDualityJet.rotatedG,
    transportedPositiveQHodgeSeed] at hseed
  exact
    transportedPositiveQCanonicalSeedChannels_eq_physical_of_rotatedSeedEquations
      L K dL q dq v omega a c s hLK hunit hseed.1 hseed.2

/-- **Genuine constant-coupling EMD data supplies detector correctness.**
Local EMD closure and the actual product-rule derivative of
`A=a(c²-s²)` imply the packaged physical-channel predicate for the
transported curvature-seed detector. -/
theorem isPhysicalConstantCouplingChannel_transported_of_emdClosure
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega dA : OneForm4) (a c s : ℝ)
    (dc ds : OneForm4)
    (hLK : L * K = 1)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hdA : dA = doubleAngleCosineFirstDerivative a c s dc ds)
    (hclosure :
      let J := localPositiveQExteriorDualityJet
        L dL q dq c s dc ds
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo)) :
    IsPhysicalConstantCouplingChannel (Real.sqrt (2 * q))
      (pullCovectorToPrincipalFrame K v)
      (pullCovectorToPrincipalFrame K dA)
      (transportedPositiveQCanonicalSeedChannels L K dL q dq) a := by
  have hchannels :=
    transportedPositiveQCanonicalSeedChannels_eq_physical_of_emdClosure
      L K dL q dq v omega a c s dc ds hLK hunit hdc hds hclosure
  have hdAcoordinate :
      dA = (-2 * (a * (2 * c * s))) • omega := by
    rw [hdA]
    exact doubleAngleCosineFirstDerivative_eq a c s dc ds omega hdc hds
  have hdAprincipal :
      pullCovectorToPrincipalFrame K dA =
        (-2 * (a * (2 * c * s))) •
          pullCovectorToPrincipalFrame K omega := by
    rw [hdAcoordinate, pullCovectorToPrincipalFrame_smul]
  exact isPhysicalConstantCouplingChannel_of_physicalSeedChannels
    (Real.sqrt (2 * q)) (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K omega)
    (pullCovectorToPrincipalFrame K dA)
    (a * (c ^ 2 - s ^ 2)) (a * (2 * c * s)) a c s
    (transportedPositiveQCanonicalSeedChannels L K dL q dq)
    hchannels rfl rfl hunit hdAprincipal

/-- Fourth-order acceptance predicate evaluated directly on a transported
curvature seed.  The remaining scalar inputs are the reconstructed scalar
covector `v` and the derivative `dA` of the curvature scalar channel, both in
the original coordinate frame; they are pulled back internally. -/
def IsTransportedSeedFourthOrderCandidate
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v dA : OneForm4)
    (choice : FourthOrderComponentChoice) : Prop :=
  IsFourthOrderChannelCandidate (Real.sqrt (2 * q))
    (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq)
    choice

/-- Finite accepted-branch output of the transported curvature-seed
detector. -/
noncomputable def acceptedTransportedSeedFourthOrderChoices
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v dA : OneForm4) :
    Finset FourthOrderComponentChoice :=
  acceptedFourthOrderChannelChoices (Real.sqrt (2 * q))
    (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq)

/-- Squared-coupling value produced by one transported-seed branch. -/
noncomputable def transportedSeedFourthOrderCouplingSqCandidate
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v dA : OneForm4)
    (choice : FourthOrderComponentChoice) : ℝ :=
  fourthOrderCouplingSqCandidate (Real.sqrt (2 * q))
    (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq)
    choice

/-- Membership in the transported detector output is exactly its explicit
fourth-order acceptance predicate. -/
theorem mem_acceptedTransportedSeedFourthOrderChoices_iff
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v dA : OneForm4)
    (choice : FourthOrderComponentChoice) :
    choice ∈ acceptedTransportedSeedFourthOrderChoices
        L K dL q dq v dA ↔
      IsTransportedSeedFourthOrderCandidate L K dL q dq v dA choice := by
  exact mem_acceptedFourthOrderChannelChoices_iff
    (Real.sqrt (2 * q))
    (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq)
    choice

/-- **Generic transported-seed necessity.**  On the positive-`q` locus,
genuine constant-coupling EMD closure produces an accepted member of the
finite fourth-order detector for every explicit source and wedge component
whose denominators are nonzero. -/
theorem isTransportedSeedFourthOrderCandidate_of_emdClosure
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega dA : OneForm4) (a c s : ℝ)
    (dc ds : OneForm4) (source left right : Fin 4)
    (hLK : L * K = 1) (hq : 0 < q)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hdA : dA = doubleAngleCosineFirstDerivative a c s dc ds)
    (hclosure :
      let J := localPositiveQExteriorDualityJet
        L dL q dq c s dc ds
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo))
    (hvsource : pullCovectorToPrincipalFrame K v source ≠ 0)
    (hnondegenerate : oneFormWedgeOneComponent
      (canonicalEffectiveOneFormFromChannels (Real.sqrt (2 * q))
        (transportedPositiveQCanonicalSeedChannels L K dL q dq))
      (canonicalPrincipalReflectionCovector
        (pullCovectorToPrincipalFrame K v)) left right ≠ 0) :
    IsTransportedSeedFourthOrderCandidate L K dL q dq v dA
      (source, (left, right)) := by
  have hphysical :=
    isPhysicalConstantCouplingChannel_transported_of_emdClosure
      L K dL q dq v omega dA a c s dc ds hLK hunit hdc hds hdA hclosure
  unfold IsTransportedSeedFourthOrderCandidate
  exact isFourthOrderChannelCandidate_of_physical
    (Real.sqrt (2 * q)) (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq) a
    source left right
    (Real.sqrt_ne_zero'.mpr (mul_pos (by norm_num) hq))
    hvsource hphysical hnondegenerate

/-- On the same generic EMD locus, the finite transported-seed detector is
actually nonempty.  This is the existence half missing from mere
accepted-branch correctness. -/
theorem acceptedTransportedSeedFourthOrderChoices_nonempty_of_emdClosure
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega dA : OneForm4) (a c s : ℝ)
    (dc ds : OneForm4)
    (hLK : L * K = 1) (hq : 0 < q)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hdA : dA = doubleAngleCosineFirstDerivative a c s dc ds)
    (hclosure :
      let J := localPositiveQExteriorDualityJet
        L dL q dq c s dc ds
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo))
    (hv : pullCovectorToPrincipalFrame K v ≠ 0)
    (hnondegenerate : ∃ left right,
      oneFormWedgeOneComponent
        (canonicalEffectiveOneFormFromChannels (Real.sqrt (2 * q))
          (transportedPositiveQCanonicalSeedChannels L K dL q dq))
        (canonicalPrincipalReflectionCovector
          (pullCovectorToPrincipalFrame K v)) left right ≠ 0) :
    (acceptedTransportedSeedFourthOrderChoices
      L K dL q dq v dA).Nonempty := by
  obtain ⟨source, hvsource⟩ :=
    exists_oneForm4_component_ne_zero
      (pullCovectorToPrincipalFrame K v) hv
  obtain ⟨left, right, hwedge⟩ := hnondegenerate
  refine ⟨(source, (left, right)), ?_⟩
  rw [mem_acceptedTransportedSeedFourthOrderChoices_iff]
  exact isTransportedSeedFourthOrderCandidate_of_emdClosure
    L K dL q dq v omega dA a c s dc ds source left right
    hLK hq hunit hdc hds hdA hclosure hvsource hwedge

/-- **Transported-seed physical result.** Every accepted finite branch on
genuine constant-coupling EMD data returns the physical invariant `a²`. -/
theorem transportedSeedFourthOrderCouplingSqCandidate_eq_physical_of_emdClosure
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v omega dA : OneForm4) (a c s : ℝ)
    (dc ds : OneForm4) (choice : FourthOrderComponentChoice)
    (hLK : L * K = 1)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hdc : dc = (-s) • omega) (hds : ds = c • omega)
    (hdA : dA = doubleAngleCosineFirstDerivative a c s dc ds)
    (hclosure :
      let J := localPositiveQExteriorDualityJet
        L dL q dq c s dc ds
      EMDExteriorClosure matrixOneWedgeTwo v a J.rotatedF J.rotatedG
        (J.rotatedDF matrixOneWedgeTwo)
        (J.rotatedDG matrixOneWedgeTwo))
    (hchoice : IsTransportedSeedFourthOrderCandidate
      L K dL q dq v dA choice) :
    transportedSeedFourthOrderCouplingSqCandidate
      L K dL q dq v dA choice = a ^ 2 := by
  have hphysical :=
    isPhysicalConstantCouplingChannel_transported_of_emdClosure
      L K dL q dq v omega dA a c s dc ds hLK hunit hdc hds hdA hclosure
  unfold transportedSeedFourthOrderCouplingSqCandidate
  exact fourthOrderCouplingSqCandidate_eq_physical_of_acceptance
    (Real.sqrt (2 * q)) (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq) a choice
    hchoice hphysical

/-- Accepted transported-seed branches are confluent: every branch gives
the same squared-coupling invariant. -/
theorem transportedSeedFourthOrderCouplingSqCandidates_eq
    (L K : Matrix4) (dL : Fin 4 → Matrix4)
    (q : ℝ) (dq v dA : OneForm4)
    (choice choice' : FourthOrderComponentChoice)
    (hchoice : IsTransportedSeedFourthOrderCandidate
      L K dL q dq v dA choice)
    (hchoice' : IsTransportedSeedFourthOrderCandidate
      L K dL q dq v dA choice') :
    transportedSeedFourthOrderCouplingSqCandidate
        L K dL q dq v dA choice =
      transportedSeedFourthOrderCouplingSqCandidate
        L K dL q dq v dA choice' := by
  exact fourthOrderCouplingSqCandidates_eq
    (Real.sqrt (2 * q))
    (pullCovectorToPrincipalFrame K v)
    (pullCovectorToPrincipalFrame K dA)
    (transportedPositiveQCanonicalSeedChannels L K dL q dq)
    choice choice' hchoice hchoice'

/-- Cosine component extracted from the scalar equation
`box(phi)=-2 a q cos(2 theta)` on the positive-`q` canonical seed.  The seed
is the Ricci-residual-normalized form `H=exp(a phi/2)F/sqrt(2)`, whose Maxwell
stress (without an extra `1/2`) equals the Ricci residual. -/
noncomputable def cosineCouplingFromScalarEquation
    (q boxPhi : ℝ) : ℝ :=
  -boxPhi / (2 * q)

/-- The scalar equation reconstructs `A=a cos(2 theta)` whenever `q` is
nonzero. -/
theorem cosineCouplingFromScalarEquation_eq
    (q boxPhi a c s : ℝ) (hq : q ≠ 0)
    (hscalar : boxPhi = -2 * a * q * (c ^ 2 - s ^ 2)) :
    cosineCouplingFromScalarEquation q boxPhi =
      a * (c ^ 2 - s ^ 2) := by
  unfold cosineCouplingFromScalarEquation
  rw [hscalar]
  field_simp [hq]

end RainichKaluza
