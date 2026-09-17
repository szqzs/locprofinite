import Aoki.Nonvanishing
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The algebraic obstruction quotient

**This is an algebraic quotient of a vector space of functions. This file does
not identify it with sheaf cohomology, or with a Čech cohomology group.**

The permitted sums `IsBoundary n` form a vector subspace. The alternating
function determines a nonzero element of its quotient in every positive degree
for the increasing aleph-sized coordinate sets.
-/

namespace Aoki

universe u

variable {A : ℕ → Type u}

theorem almostConstant_zero {X : Type u} : AlmostConstant (0 : X → F) := by
  exact ⟨0, ∅, fun _ _ => rfl⟩

theorem AlmostConstant.smul {X : Type u} {f : X → F}
    (hf : AlmostConstant f) (c : F) : AlmostConstant (c • f) := by
  obtain ⟨d, N, hN⟩ := hf
  refine ⟨c * d, N, ?_⟩
  intro x hx
  change c * f x = c * d
  rw [hN x hx]

theorem along_zero {n i : ℕ} (hi : i ≤ n) :
    Along (A := A) n i (0 : Config A n → F) := by
  induction n with
  | zero =>
      exact ⟨Nat.eq_zero_of_le_zero hi, almostConstant_zero⟩
  | succ n ih =>
      by_cases hlast : i = n + 1
      · simp only [Along, if_pos hlast]
        exact fun _ => almostConstant_zero
      · simp only [Along, if_neg hlast]
        intro _
        exact ih (by omega)

theorem Along.smul {n i : ℕ} {f : Config A n → F}
    (hf : Along n i f) (c : F) : Along n i (c • f) := by
  induction n with
  | zero => exact ⟨hf.1, hf.2.smul c⟩
  | succ n ih =>
      by_cases hlast : i = n + 1
      · simp only [Along, if_pos hlast] at hf ⊢
        exact fun x => (hf x).smul c
      · simp only [Along, if_neg hlast] at hf ⊢
        exact fun z => ih (hf z)

theorem IsBoundary.zero (n : ℕ) : IsBoundary (A := A) n 0 := by
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · intro _ _
    rfl
  · intro i
    exact along_zero (Nat.le_of_lt_succ i.isLt)
  · intro x
    simp

theorem IsBoundary.add {n : ℕ} {g h : Config A n → F}
    (hg : IsBoundary n g) (hh : IsBoundary n h) : IsBoundary n (g + h) := by
  obtain ⟨f, hfi, hfa, hfg⟩ := hg
  obtain ⟨k, hki, hka, hkh⟩ := hh
  refine ⟨fun i => f i + k i, ?_, ?_, ?_⟩
  · intro i x
    change f i (flip n x) + k i (flip n x) = f i x + k i x
    rw [hfi i x, hki i x]
  · intro i
    exact (hfa i).add (hka i)
  · intro x
    change g x + h x = ∑ i, (f i x + k i x)
    rw [hfg x, hkh x, Finset.sum_add_distrib]

theorem IsBoundary.smul {n : ℕ} {g : Config A n → F}
    (hg : IsBoundary n g) (c : F) : IsBoundary n (c • g) := by
  obtain ⟨f, hfi, hfa, hfg⟩ := hg
  refine ⟨fun i => c • f i, ?_, ?_, ?_⟩
  · intro i x
    change c * f i (flip n x) = c * f i x
    rw [hfi i x]
  · intro i
    exact (hfa i).smul c
  · intro x
    change c * g x = ∑ i, c * f i x
    rw [hfg x, Finset.mul_sum]

/-- The algebraic subspace of sums permitted by the coordinate conditions. -/
def boundarySubmodule (n : ℕ) : Submodule F (Config A n → F) where
  carrier := {g | IsBoundary n g}
  zero_mem' := IsBoundary.zero n
  add_mem' := fun hg hh => hg.add hh
  smul_mem' := fun c _ hg => hg.smul c

@[simp] theorem mem_boundarySubmodule {n : ℕ} {g : Config A n → F} :
    g ∈ boundarySubmodule n ↔ IsBoundary n g := Iff.rfl

/-- An algebraic obstruction space; no cohomological identification is asserted. -/
def ObstructionSpace (A : ℕ → Type u) (n : ℕ) :=
  (Config A n → F) ⧸ boundarySubmodule (A := A) n

instance (n : ℕ) : AddCommGroup (ObstructionSpace A n) :=
  inferInstanceAs (AddCommGroup ((Config A n → F) ⧸ boundarySubmodule n))

instance (n : ℕ) : Module F (ObstructionSpace A n) :=
  inferInstanceAs (Module F ((Config A n → F) ⧸ boundarySubmodule n))

/-- The class of the alternating function in the algebraic obstruction quotient. -/
def alternatingClass (n : ℕ) : ObstructionSpace A n :=
  Submodule.Quotient.mk (alternating n)

/-- The closed, all-positive-degrees nonvanishing theorem for this quotient. -/
theorem aleph_alternatingClass_ne_zero (r : ℕ) :
    alternatingClass (A := AlephBase) (r + 1) ≠ 0 := by
  intro hzero
  apply aleph_alternating_not_boundary r
  exact (Submodule.Quotient.mk_eq_zero
    (boundarySubmodule (A := AlephBase) (r + 1))).mp hzero

end Aoki
