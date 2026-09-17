import Aoki.AlmostConstant
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Relating recursive configurations to coordinate tuples -/

namespace Aoki

set_option backward.isDefEq.respectTransparency false

universe u

variable {A : ℕ → Type u}

abbrev Tuple (A : ℕ → Type u) (n : ℕ) := (i : Fin (n + 1)) → A i × Bool

/-- The recursive configuration and the usual finite dependent product agree. -/
def configEquivTuple : (n : ℕ) → Config A n ≃ Tuple A n
  | 0 => (Equiv.piUnique (fun i : Fin 1 => A i × Bool)).symm
  | n + 1 =>
      (Equiv.prodCongr (configEquivTuple n) (Equiv.refl _)).trans
        ((Equiv.prodComm _ _).trans (Fin.snocEquiv (fun i => A i × Bool)))

@[simp] theorem configEquivTuple_zero (x : Config A 0) :
    configEquivTuple 0 x 0 = x := rfl

@[simp] theorem configEquivTuple_succ_castSucc (n : ℕ) (x : Config A (n + 1))
    (i : Fin (n + 1)) :
    configEquivTuple (n + 1) x i.castSucc = configEquivTuple n x.1 i := by
  change Fin.snoc (α := fun j : Fin (n + 2) => A j × Bool)
    (configEquivTuple n x.1) x.2 i.castSucc = _
  simp

@[simp] theorem configEquivTuple_succ_last (n : ℕ) (x : Config A (n + 1)) :
    configEquivTuple (n + 1) x (Fin.last (n + 1)) = x.2 := by
  change Fin.snoc (α := fun j : Fin (n + 2) => A j × Bool)
    (configEquivTuple n x.1) x.2 (Fin.last (n + 1)) = _
  simp

@[simp] theorem configEquivTuple_flip (n : ℕ) (x : Config A n) (i : Fin (n + 1)) :
    configEquivTuple n (flip n x) i =
      ((configEquivTuple n x i).1, !(configEquivTuple n x i).2) := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      rfl
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [flip]
      · simpa [flip] using ih x.1 j

@[simp] theorem lastBit_eq_tuple_last (n : ℕ) (x : Config A n) :
    lastBit n x = bit (configEquivTuple n x (Fin.last n)).2 := by
  cases n with
  | zero => rfl
  | succ n => simp [lastBit]

/-- The inductive obstruction function is the usual product of adjacent bit differences. -/
theorem alternating_eq_tuple_product (n : ℕ) (x : Config A n) :
    alternating n x = ∏ j : Fin n,
      (bit (configEquivTuple n x j.castSucc).2 + bit (configEquivTuple n x j.succ).2) := by
  induction n with
  | zero => simp [alternating]
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      change alternating n x.1 * (lastBit n x.1 + bit x.2.2) = _
      rw [ih, lastBit_eq_tuple_last]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        rw [configEquivTuple_succ_castSucc]
        have h : j.castSucc.succ = j.succ.castSucc := rfl
        rw [h, configEquivTuple_succ_castSucc]
      · simp

/-- Replace one coordinate, expressed through the finite product equivalence. -/
def replaceConfig (n : ℕ) (i : Fin (n + 1)) (x : Config A n) (z : A i × Bool) :
    Config A n :=
  (configEquivTuple n).symm (Function.update (configEquivTuple n x) i z)

@[simp] theorem configEquivTuple_replace (n : ℕ) (i : Fin (n + 1))
    (x : Config A n) (z : A i × Bool) :
    configEquivTuple n (replaceConfig n i x z) =
      Function.update (configEquivTuple n x) i z :=
  (configEquivTuple n).apply_symm_apply _

@[simp] theorem replaceConfig_zero (x : Config A 0) (z : A 0 × Bool) :
    replaceConfig 0 0 x z = z := by
  apply (configEquivTuple 0).injective
  funext i
  have hi : i = 0 := Fin.ext (by omega)
  subst i
  rw [configEquivTuple_replace]
  simp

@[simp] theorem replaceConfig_last (n : ℕ) (x : Config A (n + 1))
    (z : A (n + 1) × Bool) :
    replaceConfig (n + 1) (Fin.last (n + 1)) x z = (x.1, z) := by
  apply (configEquivTuple (n + 1)).injective
  funext i
  rw [configEquivTuple_replace]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

@[simp] theorem replaceConfig_castSucc (n : ℕ) (i : Fin (n + 1))
    (x : Config A (n + 1)) (z : A i × Bool) :
    replaceConfig (n + 1) i.castSucc x z = (replaceConfig n i x.1 z, x.2) := by
  apply (configEquivTuple (n + 1)).injective
  funext j
  rw [configEquivTuple_replace]
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [Function.update_of_ne (show Fin.last (n + 1) ≠ i.castSucc by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_last, Fin.val_castSucc] at this; omega)]
    simp
  · rw [configEquivTuple_succ_castSucc, configEquivTuple_replace]
    by_cases h : k = i
    · subst k
      simp
    · rw [Function.update_of_ne (show k.castSucc ≠ i.castSucc from
        fun he => h (Fin.ext (congrArg (fun j : Fin (n + 2) => j.val) he))),
        Function.update_of_ne h]
      simp

/-- The recursive coordinate condition follows from almost constancy along
every one-coordinate variation of an ordinary tuple. -/
theorem along_of_coordinate_sections [∀ i, Nonempty (A i)]
    (n : ℕ) (i : Fin (n + 1)) (f : Config A n → F)
    (h : ∀ x : Config A n, AlmostConstant (fun z => f (replaceConfig n i x z))) :
    Along n i.val f := by
  classical
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      refine ⟨rfl, ?_⟩
      simpa using h (Classical.choice inferInstance, false)
  | succ n ih =>
      revert h
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro h
        change Along (n + 1) (n + 1) f
        rw [along_last]
        intro x
        simpa using h (x, (Classical.choice inferInstance, false))
      · intro h
        have hne : (j.castSucc : Fin (n + 2)).val ≠ n + 1 := Nat.ne_of_lt j.isLt
        simp only [Along, if_neg hne]
        intro z
        apply ih j (fun x => f (x, z))
        intro x
        simpa using h (x, z)

end Aoki
