import Aoki.Cardinals
import Mathlib.Data.ZMod.Basic

/-!
# Functions and bit differences in the Aoki construction

This file defines simultaneous bit flips, the alternating-bit cocycle, and the
operation of summing over the last Boolean bit. No topology is used here.
-/

namespace Aoki

universe u

abbrev F := ZMod 2

/-- Regard a Boolean bit as an element of the field with two elements. -/
def bit (b : Bool) : F := if b then 1 else 0

@[simp] theorem self_add (x : F) : x + x = 0 := by
  calc
    x + x = -x + x := by rw [ZMod.neg_eq_self_mod_two]
    _ = 0 := neg_add_cancel x

@[simp] theorem bit_false : bit false = 0 := rfl

@[simp] theorem bit_true : bit true = 1 := rfl

theorem bit_not (b : Bool) : bit (!b) = bit b + 1 := by
  cases b <;> simp [bit, self_add]

variable {A : ℕ → Type u}

/-- Simultaneously flip every Boolean bit, leaving every base coordinate unchanged. -/
def flip : (n : ℕ) → Config A n → Config A n
  | 0, x => (x.1, !x.2)
  | n + 1, x => (flip n x.1, (x.2.1, !x.2.2))

/-- The final bit of a configuration, as a field element. -/
def lastBit : (n : ℕ) → Config A n → F
  | 0, x => bit x.2
  | _ + 1, x => bit x.2.2

/-- The product of the differences between consecutive bits. -/
def alternating : (n : ℕ) → Config A n → F
  | 0, _ => 1
  | n + 1, x => alternating n x.1 * (lastBit n x.1 + bit x.2.2)

/-- Sum over the two points in the final Boolean orbit above a fixed base point. -/
def delta {n : ℕ} (a : A (n + 1)) (f : Config A (n + 1) → F)
    (x : Config A n) : F :=
  f (x, (a, false)) + f (x, (a, true))

/-- Invariance under simultaneous bit flip. -/
def Invariant {n : ℕ} (f : Config A n → F) : Prop :=
  ∀ x, f (flip n x) = f x

@[simp] theorem flip_flip (n : ℕ) (x : Config A n) : flip n (flip n x) = x := by
  induction n with
  | zero => simp [flip]
  | succ n ih => simp [flip, ih]

theorem lastBit_flip (n : ℕ) (x : Config A n) :
    lastBit n (flip n x) = lastBit n x + 1 := by
  cases n <;> simp only [lastBit, flip, bit_not]

@[simp] theorem delta_alternating {n : ℕ} (a : A (n + 1)) (x : Config A n) :
    delta a (alternating (n + 1)) x = alternating n x := by
  change alternating n x * (lastBit n x + 0) +
    alternating n x * (lastBit n x + 1) = alternating n x
  rw [add_zero, ← mul_add, ← add_assoc, self_add, zero_add, mul_one]

theorem invariant_delta {n : ℕ} {f : Config A (n + 1) → F}
    (hf : Invariant f) (a : A (n + 1)) : Invariant (delta a f) := by
  intro x
  have hfalse := hf (x, (a, true))
  have htrue := hf (x, (a, false))
  simp only [flip, Bool.not_true, Bool.not_false] at hfalse htrue
  dsimp only [delta]
  rw [hfalse, htrue, add_comm]

theorem alternating_invariant (n : ℕ) : Invariant (alternating (A := A) n) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      change alternating n (flip n x.1) *
          (lastBit n (flip n x.1) + bit (!x.2.2)) =
        alternating n x.1 * (lastBit n x.1 + bit x.2.2)
      rw [ih, lastBit_flip, bit_not, add_add_add_comm, self_add, add_zero]

end Aoki
