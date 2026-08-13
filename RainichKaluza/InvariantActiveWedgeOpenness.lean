import RainichKaluza.InvariantActiveWedge

/-!
# Openness of the choice-free active-wedge locus

The fourth-order recovery formula divides by a component of
`omega wedge (S^T v)`.  The preceding invariant formulation removes all
principal-frame and scalar-orientation choices from that condition.  This
file records its basic stability property: for continuous physical data, the
active locus is open.  Equivalently, activity at one point persists on a
neighborhood.

This is an openness statement only.  It makes no density claim and therefore
does not identify the active locus with a generic set in the open-dense or
measure-theoretic senses.
-/

namespace RainichKaluza

open scoped Topology
open Filter

/-- The stress action on a covector varies continuously when both inputs do.
This is the finite-dimensional polynomial regularity behind stability of the
active gate. -/
theorem continuous_mixedEndomorphismCovectorAction
    {X : Type*} [TopologicalSpace X]
    {S : X → Matrix4} {v : X → OneForm4}
    (hS : Continuous S) (hv : Continuous v) :
    Continuous (fun z ↦ mixedEndomorphismCovectorAction (S z) (v z)) := by
  apply continuous_pi
  intro a
  unfold mixedEndomorphismCovectorAction pullCovectorToPrincipalFrame
  apply continuous_finsetSum
  intro i _
  exact (hS.matrix_elem i a).mul ((continuous_apply i).comp hv)

/-- Every component of the invariant wedge is a continuous scalar function
of continuous stress, complexion, and scalar covector fields. -/
theorem continuous_coordinateMaxwellStressWedgeComponent
    {X : Type*} [TopologicalSpace X]
    {S : X → Matrix4} {omega v : X → OneForm4}
    (hS : Continuous S) (homega : Continuous omega) (hv : Continuous v)
    (i j : Fin 4) :
    Continuous (fun z ↦ oneFormWedgeOneComponent (omega z)
      (mixedEndomorphismCovectorAction (S z) (v z)) i j) := by
  have hSv := continuous_mixedEndomorphismCovectorAction hS hv
  unfold oneFormWedgeOneComponent
  exact (((continuous_apply i).comp homega).mul
      ((continuous_apply j).comp hSv)).sub
    (((continuous_apply j).comp homega).mul
      ((continuous_apply i).comp hSv))

/-- **Open active-locus theorem.**  For continuous coordinate stress,
complexion, and scalar-covector fields, the choice-free physical active set
`omega wedge (S^T v) != 0` is open. -/
theorem isOpen_coordinateMaxwellStressActiveWedge
    {X : Type*} [TopologicalSpace X]
    (S : X → Matrix4) (omega v : X → OneForm4)
    (hS : Continuous S) (homega : Continuous omega) (hv : Continuous v) :
    IsOpen {z | IsCoordinateMaxwellStressActiveWedge
      (S z) (omega z) (v z)} := by
  have hopenComponent : ∀ i j : Fin 4,
      IsOpen {z | oneFormWedgeOneComponent (omega z)
        (mixedEndomorphismCovectorAction (S z) (v z)) i j ≠ 0} := by
    intro i j
    exact isOpen_ne.preimage
      (continuous_coordinateMaxwellStressWedgeComponent
        hS homega hv i j)
  rw [show {z | IsCoordinateMaxwellStressActiveWedge
      (S z) (omega z) (v z)} =
      ⋃ i : Fin 4, ⋃ j : Fin 4,
        {z | oneFormWedgeOneComponent (omega z)
          (mixedEndomorphismCovectorAction (S z) (v z)) i j ≠ 0} by
    ext z
    simp only [IsCoordinateMaxwellStressActiveWedge,
      CovectorWedgeActive, Set.mem_setOf_eq, Set.mem_iUnion]]
  exact isOpen_iUnion fun i ↦ isOpen_iUnion fun j ↦
    hopenComponent i j

/-- Local form of the openness result: activity at `z` persists throughout
some open neighborhood of `z`. -/
theorem exists_open_nhds_coordinateMaxwellStressActiveWedge
    {X : Type*} [TopologicalSpace X]
    (S : X → Matrix4) (omega v : X → OneForm4)
    (hS : Continuous S) (homega : Continuous omega) (hv : Continuous v)
    {z : X}
    (hz : IsCoordinateMaxwellStressActiveWedge (S z) (omega z) (v z)) :
    ∃ V : Set X, IsOpen V ∧ z ∈ V ∧
      ∀ y ∈ V, IsCoordinateMaxwellStressActiveWedge
        (S y) (omega y) (v y) := by
  let V : Set X := {y | IsCoordinateMaxwellStressActiveWedge
    (S y) (omega y) (v y)}
  refine ⟨V, isOpen_coordinateMaxwellStressActiveWedge
    S omega v hS homega hv, hz, ?_⟩
  intro y hy
  exact hy

/-- Pointwise regularity is enough for neighborhood persistence.  This
version avoids assuming continuity away from the active base point. -/
theorem eventually_coordinateMaxwellStressActiveWedge_of_continuousAt
    {X : Type*} [TopologicalSpace X]
    (S : X → Matrix4) (omega v : X → OneForm4)
    {z : X}
    (hS : ContinuousAt S z) (homega : ContinuousAt omega z)
    (hv : ContinuousAt v z)
    (hz : IsCoordinateMaxwellStressActiveWedge (S z) (omega z) (v z)) :
    ∀ᶠ y in nhds z,
      IsCoordinateMaxwellStressActiveWedge (S y) (omega y) (v y) := by
  obtain ⟨i, j, hij⟩ := hz
  have hSv : ContinuousAt
      (fun y ↦ mixedEndomorphismCovectorAction (S y) (v y)) z := by
    apply continuousAt_pi.mpr
    intro a
    unfold mixedEndomorphismCovectorAction pullCovectorToPrincipalFrame
    apply tendsto_finsetSum Finset.univ
    intro k _
    exact ((continuous_apply_apply k a).continuousAt.comp hS).mul
      ((continuous_apply k).continuousAt.comp hv)
  have hcomponent : ContinuousAt
      (fun y ↦ oneFormWedgeOneComponent (omega y)
        (mixedEndomorphismCovectorAction (S y) (v y)) i j) z := by
    unfold oneFormWedgeOneComponent
    exact (((continuous_apply i).continuousAt.comp homega).mul
        ((continuous_apply j).continuousAt.comp hSv)).sub
      (((continuous_apply j).continuousAt.comp homega).mul
        ((continuous_apply i).continuousAt.comp hSv))
  filter_upwards [hcomponent.eventually_ne hij] with y hy
  exact ⟨i, j, hy⟩

/-- Patchwise form used in geometric applications.  If the three fields are
continuous only on an open regular patch `U`, then the active part of that
patch is still open in the ambient coordinate space. -/
theorem isOpen_coordinateMaxwellStressActiveWedgeOn
    {X : Type*} [TopologicalSpace X]
    (U : Set X) (S : X → Matrix4) (omega v : X → OneForm4)
    (hU : IsOpen U) (hS : ContinuousOn S U)
    (homega : ContinuousOn omega U) (hv : ContinuousOn v U) :
    IsOpen {z | z ∈ U ∧ IsCoordinateMaxwellStressActiveWedge
      (S z) (omega z) (v z)} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hUnhds : U ∈ nhds z := hU.mem_nhds hz.1
  have hactive :=
    eventually_coordinateMaxwellStressActiveWedge_of_continuousAt
      S omega v (hS.continuousAt hUnhds)
        (homega.continuousAt hUnhds) (hv.continuousAt hUnhds) hz.2
  filter_upwards [hUnhds, hactive] with y hyU hyActive
  exact ⟨hyU, hyActive⟩

/-!
The audit anchors for this module are:

* `isOpen_coordinateMaxwellStressActiveWedge`;
* `exists_open_nhds_coordinateMaxwellStressActiveWedge`;
* `eventually_coordinateMaxwellStressActiveWedge_of_continuousAt`.
* `isOpen_coordinateMaxwellStressActiveWedgeOn`.
-/

end RainichKaluza
