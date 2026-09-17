import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal thinning for the Aoki quotient construction

A family of finite exceptional sets indexed by a strictly smaller infinite
cardinal cannot meet every two-point fibre of a larger set.
-/

namespace Aoki

open Cardinal

universe u

/-- The first coordinates appearing in a family of finite exceptional sets have
cardinality at most the maximum of the index cardinality and `aleph0`. -/
theorem mk_exceptional_first_coordinates_le {P A : Type u}
    (N : P → Set (A × Bool)) (hN : ∀ p, (N p).Finite) :
    Cardinal.mk (⋃ p, Prod.fst '' N p) ≤ max ℵ₀ (Cardinal.mk P) := by
  cases isEmpty_or_nonempty P
  · simp
  calc
    Cardinal.mk (⋃ p, Prod.fst '' N p)
        ≤ Cardinal.mk P * ⨆ p, Cardinal.mk (Prod.fst '' N p) :=
      Cardinal.mk_iUnion_le _
    _ ≤ max ℵ₀ (Cardinal.mk P) * ℵ₀ := by
      apply mul_le_mul'
      · exact le_max_right _ _
      · exact ciSup_le fun p => (hN p |>.image Prod.fst).lt_aleph0.le
    _ = max ℵ₀ (Cardinal.mk P) :=
      Cardinal.mul_aleph0_eq (le_max_left _ _)

/-- A larger cardinal contains a two-point fibre avoiding every exceptional set. -/
theorem exists_fresh_pair_of_max_lt {P A : Type u}
    (h : max ℵ₀ (Cardinal.mk P) < Cardinal.mk A)
    (N : P → Set (A × Bool)) (hN : ∀ p, (N p).Finite) :
    ∃ a : A, ∀ p : P, (a, false) ∉ N p ∧ (a, true) ∉ N p := by
  classical
  have hsmall : Cardinal.mk (⋃ p, Prod.fst '' N p) < Cardinal.mk A :=
    (mk_exceptional_first_coordinates_le N hN).trans_lt h
  have hproper : (⋃ p, Prod.fst '' N p) ≠ Set.univ := by
    intro heq
    rw [heq, Cardinal.mk_univ] at hsmall
    exact (lt_irrefl _ hsmall)
  have hex : ∃ a : A, a ∉ ⋃ p, Prod.fst '' N p := by
    by_contra! hcontra
    exact hproper (Set.eq_univ_of_forall hcontra)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, fun p => ⟨?_, ?_⟩⟩
  · intro hp
    exact ha (Set.mem_iUnion.mpr ⟨p, Set.mem_image_of_mem Prod.fst hp⟩)
  · intro hp
    exact ha (Set.mem_iUnion.mpr ⟨p, Set.mem_image_of_mem Prod.fst hp⟩)

/-- Finset form used for thinning one coordinate of a top Čech coboundary. -/
theorem exists_fresh_pair {P A : Type u} [Infinite P]
    (h : Cardinal.mk P < Cardinal.mk A) (N : P → Finset (A × Bool)) :
    ∃ a : A, ∀ p : P, (a, false) ∉ N p ∧ (a, true) ∉ N p := by
  apply exists_fresh_pair_of_max_lt (N := fun p => (N p : Set (A × Bool)))
  · simpa [max_eq_right (Cardinal.aleph0_le_mk P)] using h
  · exact fun p => (N p).finite_toSet

/-- Set-valued version for a strictly smaller infinite index type. -/
theorem exists_fresh_pair_of_finite {P A : Type u} [Infinite P]
    (h : Cardinal.mk P < Cardinal.mk A)
    (N : P → Set (A × Bool)) (hN : ∀ p, (N p).Finite) :
    ∃ a : A, ∀ p : P, (a, false) ∉ N p ∧ (a, true) ∉ N p := by
  apply exists_fresh_pair_of_max_lt (N := N)
  · simpa [max_eq_right (Cardinal.aleph0_le_mk P)] using h
  · exact hN

end Aoki
