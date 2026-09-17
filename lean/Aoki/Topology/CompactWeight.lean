import Aoki.Topology.Weight

/-!
# The weight of a compact Hausdorff space

Finite intersections of a chosen family of separating neighborhoods give a
basis with at most the infinite cardinal envelope of the underlying set.
-/

noncomputable section

namespace Aoki.Topology

open Set TopologicalSpace Cardinal

universe u

theorem weight_le_max_mk (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : weight X ≤ max ℵ₀ #X := by
  classical
  have hsep : ∀ x y : X, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ (x ≠ y → y ∈ V) ∧ Disjoint U V := by
    intro x y
    by_cases h : x = y
    · exact ⟨univ, ∅, isOpen_univ, isOpen_empty, mem_univ x,
        fun hxy => False.elim (hxy h), disjoint_empty _⟩
    · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation h
      exact ⟨U, V, hU, hV, hxU, fun _ => hyV, hUV⟩
  choose U V hU hV hxU hyV hUV using hsep
  let b : X × Finset X → Set X := fun p => ⋂ y ∈ p.2, U p.1 y
  have hb : IsTopologicalBasis (range b) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨⟨x, s⟩, rfl⟩
      exact isOpen_biInter_finset (fun y _ => hU x y)
    · intro x O hxO hO
      have hcover : Oᶜ ⊆ ⋃ y : X, V x y := by
        intro y hy
        exact mem_iUnion.mpr ⟨y, hyV x y (fun h => hy (h ▸ hxO))⟩
      obtain ⟨s, hs⟩ := hO.isClosed_compl.isCompact.elim_finite_subcover
        (V x) (hV x) hcover
      refine ⟨b (x, s), mem_range_self _, ?_, ?_⟩
      · exact mem_iInter₂.mpr (fun y _ => hxU x y)
      · intro z hz
        by_contra hzO
        obtain ⟨y, hy, hzV⟩ := mem_iUnion₂.mp (hs hzO)
        exact Set.disjoint_left.mp (hUV x y) (mem_iInter₂.mp hz y hy) hzV
  refine (weight_le_card_basis X hb).trans (Cardinal.mk_range_le.trans ?_)
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc
    #X * #(Finset X) ≤ max ℵ₀ #X * max ℵ₀ #X :=
      mul_le_mul' (le_max_right _ _) (mk_finset_le_max X)
    _ = max ℵ₀ #X := Cardinal.mul_eq_self (le_max_left _ _)

end Aoki.Topology
