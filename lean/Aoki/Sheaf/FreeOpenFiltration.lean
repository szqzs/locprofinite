import Aoki.Sheaf.FreeOpenColimit
import Aoki.Sheaf.FreeOpenBasic
import Aoki.Homological.TransfiniteDimension

/-! # Continuous filtrations obtained from successively adjoining opens -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Aoki

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

variable {X : TopCat.{u}} {J : Type v} [LinearOrder J]

/-- The union of all opens with index strictly before the current index. -/
def initialOpenUnion (K : J → Opens X) : J →o Opens X where
  toFun j := ⨆ i : Set.Iio j, K i
  monotone' i j hij := by
    apply iSup_le
    intro k
    exact le_iSup_of_le ⟨k.val, k.property.trans_le hij⟩ le_rfl

@[simp] theorem initialOpenUnion_bot [OrderBot J] (K : J → Opens X) :
    initialOpenUnion K ⊥ = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro i
  exact (not_lt_bot i.property).elim

theorem initialOpenUnion_succ [SuccOrder J] (K : J → Opens X) (j : J)
    (hj : ¬IsMax j) : initialOpenUnion K (Order.succ j) = initialOpenUnion K j ⊔ K j := by
  apply le_antisymm
  · apply iSup_le
    intro i
    have hij : i.val ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp i.property
    rcases lt_or_eq_of_le hij with h | he
    · exact (le_iSup (fun i : Set.Iio j => K i) ⟨i.val, h⟩).trans le_sup_left
    · simpa only [he] using (le_sup_right : K j ≤ initialOpenUnion K j ⊔ K j)
  · apply sup_le
    · exact (initialOpenUnion K).monotone (Order.le_succ j)
    · exact le_iSup (fun i : Set.Iio (Order.succ j) => K i)
        ⟨j, Order.lt_succ_of_not_isMax hj⟩

theorem iSup_initialOpenUnion [NoMaxOrder J] (K : J → Opens X) :
    (⨆ j, initialOpenUnion K j) = iSup K := by
  apply le_antisymm
  · apply iSup_le
    intro j
    exact iSup_le (fun i => le_iSup K i.val)
  · apply iSup_le
    intro i
    obtain ⟨j, hij⟩ := exists_gt i
    exact (le_iSup (fun k : Set.Iio j => K k) ⟨i, hij⟩).trans
      (le_iSup (fun j => initialOpenUnion K j) j)

theorem initialOpenUnion_limit [SuccOrder J] (K : J → Opens X) (j : J)
    (hj : Order.IsSuccLimit j) :
    (⨆ i : Set.Iio j, initialOpenUnion K i.val) = initialOpenUnion K j := by
  apply le_antisymm
  · exact iSup_le (fun i => (initialOpenUnion K).monotone i.property.le)
  · apply iSup_le
    intro i
    have hi : ¬IsMax i.val := not_isMax_of_lt i.property
    exact (le_iSup (fun k : Set.Iio (Order.succ i.val) => K k)
      ⟨i.val, Order.lt_succ_of_not_isMax hi⟩).trans
      (le_iSup (fun k : Set.Iio j => initialOpenUnion K k.val)
        ⟨Order.succ i.val, hj.succ_lt i.property⟩)

/-- The filtration of free sheaves is continuous at every limit index. -/
instance initialFreeOpenFiltration_continuous [SuccOrder J] (K : J → Opens X) :
    ((initialOpenUnion K).toFunctor ⋙ freeOpenFunctor X).IsWellOrderContinuous where
  nonempty_isColimit j hj := by
    let V : Set.Iio j →o Opens X :=
      (initialOpenUnion K).comp ⟨Subtype.val, fun _ _ h => h⟩
    have hV : (⨆ i, V i) = initialOpenUnion K j := initialOpenUnion_limit K j hj
    refine ⟨IsColimit.ofIsoColimit (freeOpenUnionCoconeIsColimit V) ?_⟩
    refine Cocone.ext ((freeOpenFunctor X).mapIso (eqToIso hV)) ?_
    intro i
    change (freeOpenFunctor X).map _ ≫ (freeOpenFunctor X).map _ =
      (freeOpenFunctor X).map _
    rw [← Functor.map_comp]
    congr 1

end Aoki
