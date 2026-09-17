import Aoki.Functions

/-!
# Almost-constant sections and their coordinate differences

The predicates here encode precisely the finite exceptional sets that occur
when a function extends over a discrete set's one-point compactification.
-/

namespace Aoki

universe u

/-- A function is constant outside a finite exceptional set. -/
def AlmostConstant {X : Type u} (f : X → F) : Prop :=
  ∃ c : F, ∃ N : Finset X, ∀ x, x ∉ N → f x = c

theorem AlmostConstant.add {X : Type u} {f g : X → F}
    (hf : AlmostConstant f) (hg : AlmostConstant g) :
    AlmostConstant (fun x => f x + g x) := by
  classical
  obtain ⟨c, N, hN⟩ := hf
  obtain ⟨d, M, hM⟩ := hg
  refine ⟨c + d, N ∪ M, ?_⟩
  intro x hx
  have hN' : x ∉ N := fun h => hx (Finset.mem_union_left M h)
  have hM' : x ∉ M := fun h => hx (Finset.mem_union_right N h)
  dsimp only
  rw [hN x hN', hM x hM']

/-- Every section in coordinate `i` is almost constant. -/
def Along {A : ℕ → Type u} :
    (n : ℕ) → ℕ → (Config A n → F) → Prop
  | 0, i, f => i = 0 ∧ AlmostConstant f
  | n + 1, i, f =>
      if i = n + 1 then
        ∀ x, AlmostConstant (fun z => f (x, z))
      else
        ∀ z, Along n i (fun x => f (x, z))

theorem Along.add {A : ℕ → Type u} {n i : ℕ}
    {f g : Config A n → F} (hf : Along n i f) (hg : Along n i g) :
    Along n i (fun x => f x + g x) := by
  induction n with
  | zero =>
      exact ⟨hf.1, hf.2.add hg.2⟩
  | succ n ih =>
      by_cases hi : i = n + 1
      · simp only [Along, if_pos hi] at hf hg ⊢
        intro x
        exact (hf x).add (hg x)
      · simp only [Along, if_neg hi] at hf hg ⊢
        intro z
        exact ih (hf z) (hg z)

/-- Slicing a later coordinate preserves almost constancy in an earlier one. -/
theorem along_slice {A : ℕ → Type u} {n i : ℕ}
    {f : Config A (n + 1) → F} (hi : i ≤ n) (hf : Along (n + 1) i f)
    (z : A (n + 1) × Bool) : Along n i (fun x => f (x, z)) := by
  have hne : i ≠ n + 1 := Nat.ne_of_lt (Nat.lt_succ_of_le hi)
  simp only [Along, if_neg hne] at hf
  exact hf z

/-- The last-coordinate predicate is the ordinary section-wise condition. -/
theorem along_last {A : ℕ → Type u} {n : ℕ}
    {f : Config A (n + 1) → F} :
    Along (n + 1) (n + 1) f ↔
      ∀ x, AlmostConstant (fun z => f (x, z)) := by
  simp [Along]

/-- Taking the two-bit difference preserves earlier-coordinate conditions. -/
theorem along_delta {A : ℕ → Type u} {n i : ℕ}
    {f : Config A (n + 1) → F} {a : A (n + 1)}
    (hi : i ≤ n) (hf : Along (n + 1) i f) : Along n i (delta a f) := by
  exact (along_slice hi hf (a, false)).add (along_slice hi hf (a, true))

/-- An almost-constant function cannot have constant nonzero flip difference. -/
theorem not_flip_sum_one {A : ℕ → Type u} [Infinite (A 0)]
    {g : Config A 0 → F} (hg : AlmostConstant g) :
    ¬ (∀ x : Config A 0, g x + g (flip 0 x) = 1) := by
  classical
  obtain ⟨c, N, hN⟩ := hg
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset (N.image Prod.fst)
  have hfalse : (a, false) ∉ N := by
    intro hm
    exact ha (Finset.mem_image_of_mem Prod.fst hm)
  have htrue : (a, true) ∉ N := by
    intro hm
    exact ha (Finset.mem_image_of_mem Prod.fst hm)
  intro h
  have hc := h (a, false)
  change g (a, false) + g (a, true) = 1 at hc
  rw [hN (a, false) hfalse, hN (a, true) htrue, self_add] at hc
  exact zero_ne_one hc

end Aoki
