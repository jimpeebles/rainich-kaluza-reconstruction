import RainichKaluza.KaluzaUpliftOrbit
import RainichKaluza.RadialPotentialSplice

/-!
# Conditional local Kaluza uplift assembly

This file is the explicit composition interface between the accepted-data
output of Phase III and the completed local uplift module.

The earlier layers deliberately use three different abstractions:

* exterior jets for Maxwell unweighting and obstruction tests;
* `C¹` fields on a star-shaped coordinate patch for radial potential recovery;
* actual componentwise `C²` normal-gauge fields for the Ricci calculation.

`AcceptedKaluzaBranchAt` states the precise bridge between those layers.  It
does not claim that curvature automatically supplies the bridge: the physical
Maxwell field must already carry the post-unweighting `C¹` closed package, a
scalar normalization must be fixed at the base point, and a normal-gauge
realizer must certify that the normalized scalar and gauge representatives
produce the accepted EMD data.  Those are exactly the
conditional inputs that the upstream Phase-II/III program must eventually
construct.

Given that certificate, `exists_completeConditionalKaluzaUplift` performs all
remaining choices constructively at theorem level: it integrates the scalar
one-form, chooses the radial Maxwell potential, constructs the Lorentzian
Kaluza product germ, proves intrinsic Ricci-flatness in every nonlinear chart,
retains the converse Ricci-flatness/EMD equivalence, and records the complete
scalar, gauge, coupling-orientation, and product-presentation orbits.
-/

namespace RainichKaluza

open Set

/-- Accepted local data at the Phase-III/IV boundary.

The `realize` operation is the explicit compatibility bridge from integrated
representatives to the actual normal/radial-gauge coordinate fields.  Its last
three laws prevent it from being a merely nominal wrapper: the realized scalar
and potential are the normalized chosen fields, and their coordinate jets
satisfy the full EMD system used by the converse Kaluza reduction. -/
structure AcceptedKaluzaBranchAt (x : BaseCoordinateSpace) where
  patch : Set BaseCoordinateSpace
  point_mem : x ∈ patch
  patch_convex : Convex ℝ patch
  scalarOneForm : BaseCoordinateSpace → BaseCoordinateSpace →L[ℝ] ℝ
  scalar_closed : IsClosedScalarOneFormOn scalarOneForm patch
  scalarValueAtPoint : ℝ
  physicalMaxwell : BaseCoordinateSpace → ContinuousBilinForm BaseCoordinateSpace
  physicalMaxwellDerivative :
    BaseCoordinateSpace →
      BaseCoordinateSpace →L[ℝ] ContinuousBilinForm BaseCoordinateSpace
  physicalMaxwell_closed :
    IsC1ClosedTwoFormOn physicalMaxwell physicalMaxwellDerivative patch
  coupling : ℝ
  coupling_is_kaluza : IsKaluzaCoupling coupling
  realize :
    (phi : BaseCoordinateSpace → ℝ) →
      IsScalarPotentialOn phi scalarOneForm patch →
      phi x = scalarValueAtPoint →
      (A : BaseCoordinateSpace → BaseCoordinateSpace →L[ℝ] ℝ) →
      IsGaugePotentialOn A physicalMaxwell patch →
      LorentzianKaluzaLocalProductGermAt x
  realize_scalar :
    ∀ phi hphi hvalue A hA,
      (realize phi hphi hvalue A hA).fields.phi = phi
  realize_potential :
    ∀ phi hphi hvalue A hA y i,
      (realize phi hphi hvalue A hA).fields.potential y i =
        A y (coordinateDirection i)
  realize_emd :
    ∀ phi hphi hvalue A hA,
      (realize phi hphi hvalue A hA).fields.EMDEquations

/-- Complete output of the conditional local uplift assembly. -/
structure CompleteConditionalKaluzaUplift
    {x : BaseCoordinateSpace} (B : AcceptedKaluzaBranchAt x) where
  scalarPotential : BaseCoordinateSpace → ℝ
  scalarPotential_is :
    IsScalarPotentialOn scalarPotential B.scalarOneForm B.patch
  scalarPotential_value : scalarPotential x = B.scalarValueAtPoint
  gaugePotential : BaseCoordinateSpace → BaseCoordinateSpace →L[ℝ] ℝ
  gaugePotential_is :
    IsGaugePotentialOn gaugePotential B.physicalMaxwell B.patch
  product : LorentzianKaluzaLocalProductGermAt x
  product_scalar : product.fields.phi = scalarPotential
  product_potential :
    ∀ y i, product.fields.potential y i =
      gaugePotential y (coordinateDirection i)
  emd_equations : product.fields.EMDEquations
  intrinsic_ricciFlat : ∀ z : ℝ, product.IntrinsicRicciFlatAt z
  converse_reduction :
    ∀ z : ℝ,
      product.IntrinsicRicciFlatAt z ↔ product.fields.EMDEquations
  scalar_orbit :
    ∀ psi : BaseCoordinateSpace → ℝ,
      IsScalarPotentialOn psi B.scalarOneForm B.patch →
      ∃ c : ℝ, B.patch.EqOn scalarPotential (fun y => psi y + c)
  gauge_orbit :
    ∀ A' : BaseCoordinateSpace → BaseCoordinateSpace →L[ℝ] ℝ,
      IsGaugePotentialOn A' B.physicalMaxwell B.patch →
      ∃ chi : BaseCoordinateSpace → ℝ,
        IsScalarPotentialOn chi (A' - gaugePotential) B.patch
  positive_coupling_orientation :
    B.coupling = Real.sqrt 3 ∨ -B.coupling = Real.sqrt 3
  presentation_orbit_complete :
    ∀ (P Q : KaluzaUpliftPresentation BaseCoordinateSpace)
      (T : ProductFiberCoordinateJet BaseCoordinateSpace),
      P.EquivalentUnder Q T ↔
        P.WarpedBaseCompatible Q ∧
        P.FiberRadiusCompatible Q T ∧
        P.ConnectionCompatible Q T

/-- **Conditional forward-and-converse local uplift theorem.** Every accepted
branch certificate produces a complete local Lorentzian Kaluza uplift with no
unlisted scalar-potential, Maxwell-potential, chart, or product-presentation
choice. -/
theorem exists_completeConditionalKaluzaUplift
    {x : BaseCoordinateSpace} (B : AcceptedKaluzaBranchAt x) :
    Nonempty (CompleteConditionalKaluzaUplift B) := by
  obtain ⟨phiRaw, hphiRaw⟩ := exists_scalarPotential_of_closed
    B.patch_convex B.physicalMaxwell_closed.isOpen B.scalar_closed
  let phi : BaseCoordinateSpace → ℝ := fun y =>
    phiRaw y - phiRaw x + B.scalarValueAtPoint
  have hphi : IsScalarPotentialOn phi B.scalarOneForm B.patch := by
    intro y hy
    exact ((hphiRaw y hy).sub_const (phiRaw x)).add_const
      B.scalarValueAtPoint
  have hphiValue : phi x = B.scalarValueAtPoint := by
    simp [phi]
  obtain ⟨A, hA, hAorbit⟩ :=
    exists_gaugePotentialOn_orbit_of_closed B.physicalMaxwell_closed
      B.patch_convex
  let K := B.realize phi hphi hphiValue A hA
  have hemd : K.fields.EMDEquations :=
    B.realize_emd phi hphi hphiValue A hA
  refine ⟨{
    scalarPotential := phi
    scalarPotential_is := hphi
    scalarPotential_value := hphiValue
    gaugePotential := A
    gaugePotential_is := hA
    product := K
    product_scalar := B.realize_scalar phi hphi hphiValue A hA
    product_potential := B.realize_potential phi hphi hphiValue A hA
    emd_equations := hemd
    intrinsic_ricciFlat := fun z =>
      (K.intrinsicRicciFlatAt_iff_emd z).mpr hemd
    converse_reduction := K.intrinsicRicciFlatAt_iff_emd
    scalar_orbit := fun psi hpsi =>
      scalarPotential_unique_up_to_constant B.patch_convex
        B.physicalMaxwell_closed.isOpen hphi hpsi
    gauge_orbit := hAorbit
    positive_coupling_orientation :=
      kaluzaCoupling_has_positive_orientation B.coupling B.coupling_is_kaluza
    presentation_orbit_complete := fun P Q T =>
      P.equivalentUnder_iff_compatible Q T }⟩

end RainichKaluza
