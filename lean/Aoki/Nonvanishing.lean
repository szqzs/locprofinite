import Aoki.AlmostConstant
import Aoki.Thinning
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-!
# The nondecomposition theorem

This is the algebraic nonvanishing argument for the proposed answer to Aoki's
Question 2.14. It does not identify the quotient below with sheaf cohomology.
-/

namespace Aoki

universe u

variable {A : ℕ → Type u}

instance infiniteConfig [∀ i, Infinite (A i)] (n : ℕ) : Infinite (Config A n) := by
  induction n with
  | zero => change Infinite (A 0 × Bool); infer_instance
  | succ n ih =>
    letI := ih
    change Infinite (Config A n × (A (n + 1) × Bool))
    infer_instance

/-- A sum of invariant functions, one almost constant in each coordinate. -/
def IsBoundary (n : ℕ) (g : Config A n → F) : Prop :=
  ∃ f : Fin (n + 1) → Config A n → F,
    (∀ i, Invariant (f i)) ∧
    (∀ i, Along n i.val (f i)) ∧
    (∀ x, g x = ∑ i, f i x)

/-- Uniform thinning kills the difference of the last summand. -/
theorem exists_delta_last_zero {n : ℕ} [Infinite (Config A n)]
    (growth : Cardinal.mk (Config A n) < Cardinal.mk (A (n + 1)))
    {f : Config A (n + 1) → F} (hf : Along (n + 1) (n + 1) f) :
    ∃ a : A (n + 1), ∀ x, delta a f x = 0 := by
  classical
  have h : ∀ x, AlmostConstant (fun z => f (x, z)) := along_last.mp hf
  choose c N hN using h
  obtain ⟨a, ha⟩ := exists_fresh_pair growth N
  refine ⟨a, fun x => ?_⟩
  calc
    delta a f x = c x + c x :=
      congrArg₂ (· + ·) (hN x _ (ha x).1) (hN x _ (ha x).2)
    _ = 0 := self_add _

/-- Taking a difference removes the last summand of a boundary expression. -/
theorem boundary_delta {n : ℕ} [Infinite (Config A n)]
    (growth : Cardinal.mk (Config A n) < Cardinal.mk (A (n + 1)))
    {g : Config A (n + 1) → F} (hg : IsBoundary (n + 1) g) :
    ∃ a : A (n + 1), IsBoundary n (delta a g) := by
  classical
  obtain ⟨f, hinv, halong, heq⟩ := hg
  obtain ⟨a, ha⟩ := exists_delta_last_zero growth (halong (Fin.last (n + 1)))
  refine ⟨a, (fun i => delta a (f i.castSucc)), ?_, ?_, ?_⟩
  · exact fun i => invariant_delta (hinv i.castSucc) a
  · intro i
    exact along_delta (Nat.le_of_lt_succ i.isLt) (halong i.castSucc)
  · intro x
    calc
      delta a g x = (∑ i, f i (x, (a, false))) +
          (∑ i, f i (x, (a, true))) := by simp only [delta, heq]
      _ = ∑ i, delta a (f i) x := by rw [← Finset.sum_add_distrib]; rfl
      _ = (∑ i : Fin (n + 1), delta a (f i.castSucc) x) +
          delta a (f (Fin.last (n + 1))) x := Fin.sum_univ_castSucc _
      _ = ∑ i : Fin (n + 1), delta a (f i.castSucc) x := by rw [ha, add_zero]

/-- The two-coordinate case is impossible: the remaining flip difference
would be both constantly one and zero off finitely many base coordinates. -/
theorem alternating_one_not_boundary [Infinite (A 0)]
    (growth : Cardinal.mk (Config A 0) < Cardinal.mk (A 1)) :
    ¬ IsBoundary 1 (alternating (A := A) 1) := by
  classical
  letI : Infinite (Config A 0) := by change Infinite (A 0 × Bool); infer_instance
  intro h
  obtain ⟨f, hinv, halong, heq⟩ := h
  have hlast : Along 1 1 (f 1) := halong 1
  obtain ⟨a, ha⟩ := exists_delta_last_zero growth hlast
  have hslice : AlmostConstant (fun x : Config A 0 => f 0 (x, (a, false))) := by
    exact (along_slice (n := 0) (Nat.le_refl 0) (halong 0) (a, false)).2
  apply not_flip_sum_one hslice
  intro x
  have hflip : f 0 (flip 0 x, (a, false)) = f 0 (x, (a, true)) := by
    simpa only [flip, Bool.not_true] using hinv 0 (x, (a, true))
  calc
    f 0 (x, (a, false)) + f 0 (flip 0 x, (a, false)) = delta a (f 0) x := by
      rw [hflip]; rfl
    _ = delta a (f 0) x + delta a (f 1) x := by rw [ha, add_zero]
    _ = delta a (alternating 1) x := by
      simp only [delta, heq]
      erw [Fin.sum_univ_two, Fin.sum_univ_two]
      ring
    _ = 1 := by rw [delta_alternating]; rfl

/-- For strictly growing coordinate cardinalities, no positive-degree
alternating product is a sum of the permitted coordinate boundaries. -/
theorem alternating_not_boundary [∀ i, Infinite (A i)]
    (growth : ∀ n, Cardinal.mk (Config A n) < Cardinal.mk (A (n + 1)))
    (r : ℕ) : ¬ IsBoundary (r + 1) (alternating (A := A) (r + 1)) := by
  induction r with
  | zero => exact alternating_one_not_boundary (growth 0)
  | succ r ih =>
    intro h
    obtain ⟨a, ha⟩ := boundary_delta (growth (r + 1)) h
    apply ih
    have heq : delta a (alternating (A := A) (r + 1 + 1)) =
        alternating (r + 1) := funext (delta_alternating a)
    rwa [heq] at ha

/-- Closed specialization to coordinate sizes `aleph 0, …, aleph (r + 1)`.
The argument is valid in every positive degree, not merely for tested examples. -/
theorem aleph_alternating_not_boundary (r : ℕ) :
    ¬ IsBoundary (r + 1) (alternating (A := AlephBase) (r + 1)) :=
  alternating_not_boundary config_lt_next r

/-- Positive-degree form, with the same degree convention as the paper proof. -/
theorem aleph_nondecomposition (d : ℕ) (hd : 0 < d) :
    ¬ ∃ f : Fin (d + 1) → Config AlephBase d → F,
      (∀ i, Invariant (f i)) ∧
      (∀ i, Along d i.val (f i)) ∧
      (∀ x, alternating d x = ∑ i, f i x) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact aleph_alternating_not_boundary r

end Aoki
