import Aoki.Sheaf.FreeOpen
import Aoki.Sheaf.EpiSections
import Aoki.Topology.CompactOpenCovers

/-!
# Projective sheaves from compact open subsets

This is the sheaf-theoretic projectivity input for the finite cover of the
Aoki space. The results concern actual abelian sheaves, not a proxy category.
-/

noncomputable section

namespace Aoki

open CategoryTheory TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} [T2Space X] [TotallyDisconnectedSpace X]

theorem hasDisjointOpenRefinements_of_isCompact
    (W : Opens X) (hW : IsCompact (W : Set X)) : HasDisjointOpenRefinements W := by
  intro ι U _ hcover
  exact Aoki.Topology.exists_disjoint_open_refinement W hW U hcover

/-- Epimorphisms of abelian sheaves are surjective on compact-open sections. -/
theorem surjective_sections_of_isCompact
    (W : Opens X) (hW : IsCompact (W : Set X))
    (M N : TopCat.Sheaf AddCommGrpCat.{u} X) (p : M ⟶ N) [Epi p] :
    Function.Surjective (p.hom.app (op W)) :=
  surjective_sections_of_disjoint_refinements W
    (hasDisjointOpenRefinements_of_isCompact W hW) M N p

/-- The free abelian sheaf represented by a compact open is projective. -/
theorem projective_freeOpen_of_isCompact
    (W : Opens X) (hW : IsCompact (W : Set X)) : Projective (freeOpen W) :=
  projective_freeOpen_of_surjective W (surjective_sections_of_isCompact W hW)

/-- The same holds for a disjoint union of compact opens, with any small index set. -/
theorem projective_freeOpen_disjoint_iSup {ι : Type u} (W : ι → Opens X)
    (hcompact : ∀ i, IsCompact (W i : Set X))
    (hdisj : Pairwise (fun i j => Disjoint (W i) (W j))) :
    Projective (freeOpen (iSup W)) := by
  apply projective_freeOpen_of_surjective
  exact surjective_sections_of_disjoint_refinements _
    (HasDisjointOpenRefinements.disjoint_iSup W hdisj
      (fun i => hasDisjointOpenRefinements_of_isCompact (W i) (hcompact i)))

/-- Countable unions of compact opens already give projective free sheaves:
disjointifying the countable cover reduces to the preceding theorem. -/
theorem projective_freeOpen_countable_iSup (K : ℕ → Opens X)
    (hcompact : ∀ n, IsCompact (K n : Set X)) :
    Projective (freeOpen (iSup K)) := by
  let L : ℕ → Opens X := fun n =>
    ⟨Aoki.Topology.compactOpenPiece (fun n => (K n : Set X)) n,
      Aoki.Topology.compactOpenPiece_isOpen _ hcompact (fun n => (K n).isOpen) n⟩
  have hLcompact : ∀ n, IsCompact (L n : Set X) := fun n =>
    Aoki.Topology.compactOpenPiece_isCompact _ hcompact (fun n => (K n).isOpen) n
  have hLdisj : Pairwise (fun n m => Disjoint (L n) (L m)) := by
    intro n m hnm
    exact Opens.coe_disjoint.mp
      (Aoki.Topology.compactOpenPiece_pairwiseDisjoint (fun n => (K n : Set X)) hnm)
  have hEq : iSup L = iSup K := by
    apply SetLike.coe_injective
    simp only [Opens.coe_iSup]
    exact Aoki.Topology.iUnion_compactOpenPiece _
  have hproj := projective_freeOpen_disjoint_iSup
    (fun n : ULift.{u} ℕ => L n.down) (fun n => hLcompact n.down)
    (hLdisj.comp_of_injective ULift.down_injective)
  simpa only [iSup_ulift, hEq] using hproj

end Aoki
