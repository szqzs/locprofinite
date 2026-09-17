import Aoki.Sheaf.CohomologyVanishing
import Aoki.Topology.Weight

/-!
# Vanishing for countable cardinality or countable weight

These are the degree-one cases of the sharp size lower bound. In fact every
positive-degree cohomology group vanishes under either hypothesis, with any
abelian coefficient sheaf.
-/

noncomputable section

namespace Aoki

open CategoryTheory TopologicalSpace Cardinal

universe u

variable {X : TopCat.{u}} [T2Space X] [TotallyDisconnectedSpace X]

/-- Countably indexed compact opens give a projective represented union;
the index type is allowed to be empty. -/
theorem projective_freeOpen_iSup_of_countable {ι : Type u} [Countable ι]
    (K : ι → Opens X) (hK : ∀ i, IsCompact (K i : Set X)) :
    Projective (freeOpen (iSup K)) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (Option ι)
  let L : Option ι → Opens X := Option.elim' ⊥ K
  have hL : ∀ i, IsCompact (L i : Set X) := by
    intro i
    cases i with
    | none => exact isCompact_empty
    | some i => exact hK i
  have hsup : (⨆ n : ℕ, L (e n)) = iSup K := by
    apply le_antisymm
    · apply iSup_le
      intro n
      cases h : e n with
      | none => simp [L]
      | some i => simpa [h, L] using le_iSup K i
    · apply iSup_le
      intro i
      obtain ⟨n, hn⟩ := he (some i)
      simpa [hn, L] using le_iSup (fun n => L (e n)) n
  rw [← hsup]
  exact projective_freeOpen_countable_iSup (fun n => L (e n)) (fun n => hL (e n))

theorem sheaf_cohomology_eq_zero_of_countable_index_compactOpen_cover
    {ι : Type u} [Countable ι] (K : ι → Opens X)
    (hK : ∀ i, IsCompact (K i : Set X)) (hcover : iSup K = ⊤)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 := by
  apply sheaf_cohomology_eq_zero_of_projective_top _ M n a
  rw [← hcover]
  exact projective_freeOpen_iSup_of_countable K hK

variable [LocallyCompactSpace X]

/-- Countable locally profinite Hausdorff spaces have no positive-degree
ordinary sheaf cohomology, for any abelian sheaf. -/
theorem sheaf_cohomology_eq_zero_of_countable [Countable X]
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 := by
  obtain ⟨K, hK, hcover⟩ := Topology.exists_point_indexed_compactOpen_cover (X := X)
  exact sheaf_cohomology_eq_zero_of_countable_index_compactOpen_cover K hK hcover M n a

/-- Countable weight also forces all positive-degree cohomology to vanish. -/
theorem sheaf_cohomology_eq_zero_of_weight_le_aleph0
    (hweight : Topology.weight X ≤ ℵ₀)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 := by
  haveI : Countable (CompactOpens X) := Cardinal.mk_le_aleph0_iff.mp
    (Topology.mk_compactOpens_le_weight.trans (max_le le_rfl hweight))
  exact sheaf_cohomology_eq_zero_of_countable_index_compactOpen_cover
    CompactOpens.toOpens (fun K => K.isCompact) Topology.iSup_compactOpens_eq_top M n a

end Aoki
