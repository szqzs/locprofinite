import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# The cardinal sizes in the Aoki construction

`AlephBase n` is a chosen type of cardinality `aleph n`. `Config A n` is the
left-associated product of the first `n + 1` doubled coordinate sets in `A`.
-/

namespace Aoki

open Cardinal

universe u

/-- A chosen set of cardinality `aleph n`, in universe zero. -/
noncomputable def AlephBase (n : ℕ) : Type :=
  (Cardinal.aleph (n : Ordinal)).out

/-- The first `n + 1` coordinate sets, each doubled by a Boolean bit. -/
def Config (A : ℕ → Type u) : ℕ → Type u
  | 0 => A 0 × Bool
  | n + 1 => Config A n × (A (n + 1) × Bool)

@[simp] theorem mk_alephBase (n : ℕ) :
    #(AlephBase n) = Cardinal.aleph (n : Ordinal) := by
  exact Cardinal.mk_out _

instance (n : ℕ) : Infinite (AlephBase n) := by
  apply Cardinal.infinite_iff.mpr
  rw [mk_alephBase]
  exact Cardinal.aleph0_le_aleph _

@[simp] theorem mk_alephBase_bool (n : ℕ) :
    #(AlephBase n × Bool) = Cardinal.aleph (n : Ordinal) := by
  simp only [Cardinal.mk_prod, Cardinal.lift_id, mk_alephBase, Cardinal.mk_bool]
  exact Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph _)
    (Cardinal.ofNat_le_aleph0.trans (Cardinal.aleph0_le_aleph _)) (by simp)

theorem aleph_nat_lt_succ (n : ℕ) :
    Cardinal.aleph (n : Ordinal) < Cardinal.aleph ((n + 1 : ℕ) : Ordinal) := by
  rw [Cardinal.aleph_lt_aleph]
  exact_mod_cast Nat.lt_succ_self n

@[simp] theorem mk_config (n : ℕ) :
    #(Config AlephBase n) = Cardinal.aleph (n : Ordinal) := by
  induction n with
  | zero => exact mk_alephBase_bool 0
  | succ n ih =>
      change #(Config AlephBase n × (AlephBase (n + 1) × Bool)) = _
      rw [Cardinal.mk_prod, ih, mk_alephBase_bool]
      simpa only [Cardinal.lift_id] using
        Cardinal.mul_eq_right (Cardinal.aleph0_le_aleph ((n + 1 : ℕ) : Ordinal))
          (aleph_nat_lt_succ n).le (Cardinal.aleph_pos (n : Ordinal)).ne'

instance (n : ℕ) : Infinite (Config AlephBase n) := by
  apply Cardinal.infinite_iff.mpr
  rw [mk_config]
  exact Cardinal.aleph0_le_aleph _

/-- The previous coordinate tuples form a strictly smaller set than the next base. -/
theorem config_lt_next (n : ℕ) : #(Config AlephBase n) < #(AlephBase (n + 1)) := by
  rw [mk_config, mk_alephBase]
  exact aleph_nat_lt_succ n

end Aoki
