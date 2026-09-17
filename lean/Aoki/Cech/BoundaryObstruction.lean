import Aoki.ConfigTuple
import Aoki.OnePoint
import Aoki.Nonvanishing
import Aoki.Sheaf.ChartProjectivity
import Aoki.Topology.GeometrySize
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuous deleted-face sections satisfy the combinatorial obstruction

Pull back a section on the intersection with the ith chart omitted to the
all-finite configurations. It is flip invariant, and continuity across the ith
point at infinity makes it almost constant in that coordinate. Thus the already
checked nondecomposition theorem applies to the actual chart sections.
-/

noncomputable section

namespace Aoki.Geometry

open TopologicalSpace

set_option backward.isDefEq.respectTransparency false

universe u

variable {A : ℕ → Type u} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- Include an all-finite configuration in the compact product. -/
def fullPoint (x : Config A n) : CompactProduct A n :=
  fun i => (configEquivTuple n x i : OnePoint (A i × Bool))

omit [∀ i, DiscreteTopology (A i)] [∀ i, TopologicalSpace (A i)] in
theorem fullPoint_ne_infty (x : Config A n) : fullPoint x ≠ infty := by
  intro h
  exact OnePoint.coe_ne_infty _ (congrFun h 0)

/-- The actual orbit of an all-finite configuration in the punctured quotient. -/
def fullOrbit (x : Config A n) : U A n :=
  ⟨quotientMap (fullPoint x), fun h => fullPoint_ne_infty x
    ((quotientMap_eq_infty_iff _).mp h)⟩

omit [∀ i, DiscreteTopology (A i)] [∀ i, TopologicalSpace (A i)] in
theorem fullOrbit_mem_chart (x : Config A n) (i : Fin (n + 1)) :
    fullOrbit x ∈ chart i :=
  ⟨fullPoint x, OnePoint.coe_ne_infty _, rfl⟩

omit [∀ i, DiscreteTopology (A i)] [∀ i, TopologicalSpace (A i)] in
@[simp] theorem fullPoint_flip (x : Config A n) :
    fullPoint (Aoki.flip n x) = flip (fullPoint x) := by
  funext i
  simp [fullPoint, flip, configEquivTuple_flip, coordinateFlip]

omit [∀ i, DiscreteTopology (A i)] [∀ i, TopologicalSpace (A i)] in
@[simp] theorem fullOrbit_flip (x : Config A n) : fullOrbit (Aoki.flip n x) = fullOrbit x := by
  apply Subtype.ext
  change quotientMap (fullPoint (Aoki.flip n x)) = quotientMap (fullPoint x)
  rw [fullPoint_flip]
  exact (quotientMap_eq_iff _ _).mpr (Or.inr rfl)

/-- The open intersection of every chart except one. -/
def deletedOpen (i : Fin (n + 1)) : Opens (U A n) :=
  ⨅ j : {j : Fin (n + 1) // j ≠ i}, chartOpen j.1

theorem mem_deletedOpen (i : Fin (n + 1)) (q : U A n) :
    q ∈ deletedOpen i ↔ ∀ j, j ≠ i → q ∈ chart j := by
  change q ∈ (⨅ j : {j : Fin (n + 1) // j ≠ i}, chartOpen j.1) ↔ _
  simp [mem_finite_iInf_opens, chartOpen]

def fullLift (i : Fin (n + 1)) (x : Config A n) : deletedOpen (A := A) i :=
  ⟨fullOrbit x, (mem_deletedOpen i _).mpr (fun j _ => fullOrbit_mem_chart x j)⟩

@[simp] theorem fullLift_flip (i : Fin (n + 1)) (x : Config A n) :
    fullLift i (Aoki.flip n x) = fullLift i x := by
  apply Subtype.ext
  exact fullOrbit_flip x

/-- Vary one coordinate through its whole one-point compactification. -/
def partialPoint (i : Fin (n + 1)) (x : Config A n) (z : OnePoint (A i × Bool)) :
    CompactProduct A n := Function.update (fullPoint x) i z

omit [∀ i, DiscreteTopology (A i)] [∀ i, TopologicalSpace (A i)] in
theorem partialPoint_ne_infty (hn : 0 < n) (i : Fin (n + 1))
    (x : Config A n) (z : OnePoint (A i × Bool)) : partialPoint i x z ≠ infty := by
  haveI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hji⟩ := exists_ne i
  intro h
  have hj := congrFun h j
  change Function.update (fullPoint x) i z j = OnePoint.infty at hj
  rw [Function.update_of_ne hji] at hj
  exact OnePoint.coe_ne_infty _ hj

def partialOrbit (hn : 0 < n) (i : Fin (n + 1)) (x : Config A n)
    (z : OnePoint (A i × Bool)) : U A n :=
  ⟨quotientMap (partialPoint i x z), fun h => partialPoint_ne_infty hn i x z
    ((quotientMap_eq_infty_iff _).mp h)⟩

def partialLift (hn : 0 < n) (i : Fin (n + 1)) (x : Config A n)
    (z : OnePoint (A i × Bool)) : deletedOpen (A := A) i :=
  ⟨partialOrbit hn i x z, (mem_deletedOpen i _).mpr (fun j hji =>
    ⟨partialPoint i x z, by
      change Function.update (fullPoint x) i z j ≠ OnePoint.infty
      rw [Function.update_of_ne hji]
      exact OnePoint.coe_ne_infty _, rfl⟩)⟩

omit [∀ i, DiscreteTopology (A i)] in
theorem continuous_partialPoint (i : Fin (n + 1)) (x : Config A n) :
    Continuous (partialPoint i x) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    simp only [partialPoint, Function.update_self]
    exact continuous_id
  · simpa [partialPoint, Function.update_of_ne hji] using
      (continuous_const : Continuous (fun _ : OnePoint (A i × Bool) => fullPoint x j))

theorem continuous_partialLift (hn : 0 < n) (i : Fin (n + 1)) (x : Config A n) :
    Continuous (partialLift hn i x) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_quotientMap.comp (continuous_partialPoint i x)

omit [∀ i, DiscreteTopology (A i)] [∀ i, TopologicalSpace (A i)] in
theorem fullPoint_replace (i : Fin (n + 1)) (x : Config A n) (z : A i × Bool) :
    fullPoint (replaceConfig n i x z) = partialPoint i x (↑z) := by
  funext j
  simp only [fullPoint, configEquivTuple_replace, partialPoint]
  by_cases hji : j = i
  · subst j; simp
  · simp [Function.update_of_ne hji, fullPoint]

@[simp] theorem partialLift_coe (hn : 0 < n) (i : Fin (n + 1))
    (x : Config A n) (z : A i × Bool) :
    partialLift hn i x (↑z) = fullLift i (replaceConfig n i x z) := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg quotientMap (fullPoint_replace i x z).symm

/-- Any function on the deleted-face chart pulls back to an invariant function. -/
theorem invariant_deleted_section (i : Fin (n + 1)) (f : deletedOpen (A := A) i → F) :
    Invariant (fun x => f (fullLift i x)) := by
  intro x
  dsimp only
  rw [fullLift_flip]

variable [TopologicalSpace F] [DiscreteTopology F]

/-- Continuity of an actual deleted-face section gives the exact `Along`
condition of the combinatorial nondecomposition theorem. -/
theorem along_deleted_section [∀ i, Nonempty (A i)] (hn : 0 < n)
    (i : Fin (n + 1)) (f : deletedOpen (A := A) i → F) (hf : Continuous f) :
    Along n i.val (fun x => f (fullLift i x)) := by
  apply along_of_coordinate_sections
  intro x
  have h := almostConstant_of_continuous_onePoint (hf.comp (continuous_partialLift hn i x))
  simpa only [Function.comp_apply, partialLift_coe] using h

/-- The alternating top function cannot be a sum of restrictions of actual
continuous sections from the deleted-face intersections. -/
theorem aleph_no_continuous_deleted_decomposition (n : ℕ) (hn : 0 < n) :
    ¬ ∃ f : (i : Fin (n + 1)) → C(deletedOpen (A := AlephBase) i, F),
      ∀ x : Config AlephBase n, alternating n x = ∑ i, f i (fullLift i x) := by
  rintro ⟨f, hf⟩
  apply aleph_nondecomposition n hn
  exact ⟨fun i x => f i (fullLift i x),
    (fun i => invariant_deleted_section i (f i)),
    (fun i => along_deleted_section hn i (f i) (f i).continuous), hf⟩

end Aoki.Geometry
