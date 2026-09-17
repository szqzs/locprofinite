import Mathlib.Topology.Sheaves.Flasque

/-!
# Surjectivity of sections from disjoint refinements

A sheaf epimorphism is surjective on sections over an open set whose open
covers admit disjoint open refinements. This is the projectivity input for
compact opens and disjoint unions of profinite spaces.
-/

noncomputable section

open CategoryTheory TopCat TopologicalSpace Opposite
open TopCat.Presheaf

namespace Aoki

universe u

variable {X : TopCat.{u}}

/-- Every open cover of `W` has a pairwise disjoint open refinement. -/
def HasDisjointOpenRefinements (W : Opens X) : Prop :=
  ∀ (ι : Type u) (U : ι → Opens X), (∀ i, U i ≤ W) → W ≤ iSup U →
    ∃ (κ : Type u) (V : κ → Opens X) (j : κ → ι),
      Pairwise (fun a b => Disjoint (V a) (V b)) ∧
      (∀ a, V a ≤ U (j a)) ∧ W ≤ iSup V

/-- The refinement property is preserved by disjoint unions of open sets. -/
theorem HasDisjointOpenRefinements.disjoint_iSup {ι : Type u}
    (U : ι → Opens X) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hlocal : ∀ i, HasDisjointOpenRefinements (U i)) :
    HasDisjointOpenRefinements (iSup U) := by
  classical
  intro κ V hV hcover
  have hpiece (i : ι) : U i ≤ ⨆ a, U i ⊓ V a := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl ((le_iSup U i).trans hcover)
  choose κ' W j hdisj hsub hcov using
    fun i => hlocal i κ (fun a => U i ⊓ V a) (fun _ => inf_le_left) (hpiece i)
  refine ⟨Σ i, κ' i, (fun a => W a.1 a.2), (fun a => j a.1 a.2), ?_, ?_, ?_⟩
  · rintro ⟨i, a⟩ ⟨k, b⟩ hab
    by_cases hik : i = k
    · subst k
      exact hdisj i (by intro h; exact hab (congrArg (fun b : κ' i => Sigma.mk i b) h))
    · exact (hU hik).mono ((hsub i a).trans inf_le_left)
        ((hsub k b).trans inf_le_left)
  · intro a
    exact (hsub a.1 a.2).trans inf_le_right
  · apply iSup_le
    intro i
    exact (hcov i).trans (iSup_le fun a => le_iSup (fun b : Σ i, κ' i => W b.1 b.2) ⟨i, a⟩)

/-- Sections on disjoint opens are automatically compatible. -/
theorem compatible_of_pairwise_disjoint
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) {ι : Type u} (U : ι → Opens X)
    (hU : Pairwise (fun a b => Disjoint (U a) (U b)))
    (s : ∀ i, M.obj.obj (op (U i))) : IsCompatible M.obj U s := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · apply TopCat.Presheaf.IsSheaf.section_ext M.property
    intro x hx
    have hempty : U i ⊓ U j = ⊥ := disjoint_iff.mp (hU hij)
    simp only [hempty, Opens.mem_bot] at hx

/-- The local lifting property of an epimorphism becomes a global lifting
property after refining its lifting neighborhoods to disjoint opens. -/
theorem surjective_sections_of_disjoint_refinements
    (W : Opens X) (hW : HasDisjointOpenRefinements W)
    (M N : TopCat.Sheaf AddCommGrpCat.{u} X) (p : M ⟶ N) [Epi p] :
    Function.Surjective (p.hom.app (op W)) := by
  classical
  intro s
  have hlocal := (TopCat.Presheaf.isLocallySurjective_iff p.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi p).mpr inferInstance)
  have hl : ∀ x : W, ∃ U : Opens X, ∃ hUW : U ≤ W,
      ∃ t : M.obj.obj (op U), p.hom.app (op U) t = N.obj.map (homOfLE hUW).op s ∧
        (x : X) ∈ U := by
    intro x
    obtain ⟨U, hUW, ⟨t, ht⟩, hx⟩ := hlocal W s x x.property
    exact ⟨U, hUW, t, ht, hx⟩
  choose U hUW t ht hx using hl
  have hcover : W ≤ iSup U := by
    intro x hxW
    exact (le_iSup U ⟨x, hxW⟩) (hx ⟨x, hxW⟩)
  obtain ⟨κ, V, j, hdisj, hVU, hcoverV⟩ := hW W U hUW hcover
  have hVW : ∀ a, V a ≤ W := fun a => (hVU a).trans (hUW (j a))
  let sf : ∀ a, M.obj.obj (op (V a)) :=
    fun a => M.obj.map (homOfLE (hVU a)).op (t (j a))
  obtain ⟨t', ht', _⟩ := M.existsUnique_gluing' V W
    (fun a => homOfLE (hVW a)) hcoverV sf
    (compatible_of_pairwise_disjoint M V hdisj sf)
  refine ⟨t', ?_⟩
  apply N.eq_of_locally_eq' V W (fun a => homOfLE (hVW a)) hcoverV
  intro a
  erw [← NatTrans.naturality_apply, ht']
  dsimp only [sf]
  erw [NatTrans.naturality_apply, ht]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end Aoki
