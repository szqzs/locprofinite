import Aoki.Sheaf.FreeOpen
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Order.Directed

/-!
# Directed unions of free open sheaves

The free sheaf on a directed union is the colimit of the free sheaves on its
members. The proof is the unique gluing property of sections, transported
through their representing equivalence.
-/

noncomputable section

namespace Aoki

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

variable {X : TopCat.{u}} {ι : Type v} [Preorder ι]
    (U : ι →o Opens X)

/-- The canonical cocone with vertex the free sheaf on the union. -/
def freeOpenUnionCocone : Cocone (U.toFunctor ⋙ freeOpenFunctor X) where
  pt := freeOpen (⨆ i, U i)
  ι :=
    { app := fun i => freeOpenMap (homOfLE (le_iSup (fun i => U i) i))
      naturality := fun i j f => by
        change (freeOpenFunctor X).map _ ≫ (freeOpenFunctor X).map _ = _
        rw [← Functor.map_comp]
        rfl }

variable [IsDirectedOrder ι]

/-- Cocone sections are compatible on pairwise intersections because both
are restrictions of a section at a common upper index. -/
theorem freeOpenUnion_compatible
    (s : Cocone (U.toFunctor ⋙ freeOpenFunctor X)) :
    TopCat.Presheaf.IsCompatible s.pt.obj (fun i => U i)
      (fun i => freeOpenHomEquiv (U i) s.pt (s.ι.app i)) := by
  intro i j
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hi := congrArg (freeOpenHomEquiv (U i) s.pt) (s.w (homOfLE hik))
  have hj := congrArg (freeOpenHomEquiv (U j) s.pt) (s.w (homOfLE hjk))
  change freeOpenHomEquiv (U i) s.pt
    (freeOpenMap (homOfLE (U.monotone hik)) ≫ s.ι.app k) = _ at hi
  change freeOpenHomEquiv (U j) s.pt
    (freeOpenMap (homOfLE (U.monotone hjk)) ≫ s.ι.app k) = _ at hj
  rw [freeOpenHomEquiv_restrict] at hi hj
  dsimp only [TopCat.Presheaf.IsCompatible]
  rw [← hi, ← hj, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The free sheaf construction carries a directed union to a colimit. -/
def freeOpenUnionCoconeIsColimit : IsColimit (freeOpenUnionCocone U) := by
  classical
  let sf (s : Cocone (U.toFunctor ⋙ freeOpenFunctor X)) (i : ι) :=
    freeOpenHomEquiv (U i) s.pt (s.ι.app i)
  have hgl (s : Cocone (U.toFunctor ⋙ freeOpenFunctor X)) :=
    s.pt.existsUnique_gluing (fun i => U i) (sf s) (freeOpenUnion_compatible U s)
  let gl (s : Cocone (U.toFunctor ⋙ freeOpenFunctor X)) := (hgl s).choose
  have hres (s : Cocone (U.toFunctor ⋙ freeOpenFunctor X)) (i : ι) :
      s.pt.obj.map (homOfLE (le_iSup (fun i => U i) i)).op (gl s) = sf s i :=
    (hgl s).choose_spec.1 i
  refine
    { desc := fun s => (freeOpenHomEquiv (iSup fun i => U i) s.pt).symm (gl s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply (freeOpenHomEquiv (U i) s.pt).injective
    change freeOpenHomEquiv (U i) s.pt (freeOpenMap _ ≫ _) = _
    rw [freeOpenHomEquiv_restrict, Equiv.apply_symm_apply]
    exact hres s i
  · intro s m hm
    apply (freeOpenHomEquiv (iSup fun i => U i) s.pt).injective
    rw [Equiv.apply_symm_apply]
    apply (hgl s).choose_spec.2
    intro i
    have h := congrArg (freeOpenHomEquiv (U i) s.pt) (hm i)
    change freeOpenHomEquiv (U i) s.pt (freeOpenMap _ ≫ m) = _ at h
    rw [freeOpenHomEquiv_restrict] at h
    exact h

end Aoki
