import Aoki.Sheaf.FreeOpen
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # Zero and monomorphisms for free open sheaves -/

noncomputable section

namespace Aoki

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}

/-- Inclusion of opens induces a monomorphism of free sheaves. -/
instance freeOpenMap_mono {V W : Opens X} (i : V ⟶ W) : Mono (freeOpenMap i) := by
  haveI : Mono (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) :=
    NatTrans.mono_of_mono_app _
  exact (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_mono _

/-- The empty open represents the zero sheaf. -/
theorem freeOpen_bot_isZero : IsZero (freeOpen (⊥ : Opens X)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (freeOpenHomAddEquiv ⊥ (freeOpen (⊥ : Opens X))).injective
  rw [map_zero]
  apply TopCat.Presheaf.IsSheaf.section_ext (freeOpen (⊥ : Opens X)).property
  intro x hx
  exact False.elim hx

end Aoki
