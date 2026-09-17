import Mathlib.Topology.Separation.DisjointCover

/-!
# Disjoint refinements of compact-open covers

Countable families of compact open sets can be made pairwise disjoint by
subtracting their predecessors. Compact open subsets of totally disconnected
Hausdorff spaces admit finite disjoint compact-open refinements of open covers.
These are purely topological statements; no sheaf or cohomology assertions are
made in this file.
-/

namespace Aoki.Topology

open Set TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- Remove the earlier members of a countable family. -/
def compactOpenPiece (K : ℕ → Set X) (n : ℕ) : Set X :=
  K n \ ⋃ j < n, K j

omit [TopologicalSpace X] in
theorem compactOpenPiece_subset (K : ℕ → Set X) (n : ℕ) :
    compactOpenPiece K n ⊆ K n := fun _ hx => hx.1

theorem compactOpenPiece_isCompact (K : ℕ → Set X)
    (hKc : ∀ n, IsCompact (K n)) (hKo : ∀ n, IsOpen (K n)) (n : ℕ) :
    IsCompact (compactOpenPiece K n) :=
  (hKc n).diff (isOpen_iUnion fun j => isOpen_iUnion fun _ => hKo j)

theorem compactOpenPiece_isOpen [T2Space X] (K : ℕ → Set X)
    (hKc : ∀ n, IsCompact (K n)) (hKo : ∀ n, IsOpen (K n)) (n : ℕ) :
    IsOpen (compactOpenPiece K n) := by
  have hclosed : IsClosed (⋃ j < n, K j) :=
    (Set.finite_Iio n).isClosed_biUnion fun j _ => (hKc j).isClosed
  exact (hKo n).sdiff hclosed

omit [TopologicalSpace X] in
theorem compactOpenPiece_pairwiseDisjoint (K : ℕ → Set X) :
    Pairwise (fun n m => Disjoint (compactOpenPiece K n) (compactOpenPiece K m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hxn hxm
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact hxm.2 (Set.mem_iUnion₂.mpr ⟨n, hlt, hxn.1⟩)
  · exact hxn.2 (Set.mem_iUnion₂.mpr ⟨m, hlt, hxm.1⟩)

omit [TopologicalSpace X] in
theorem iUnion_compactOpenPiece (K : ℕ → Set X) :
    (⋃ n, compactOpenPiece K n) = ⋃ n, K n := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono fun n => compactOpenPiece_subset K n
  · intro x hx
    have hex : ∃ n, x ∈ K n := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro hearlier
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hearlier
    exact Nat.find_min hex hj hxj

/-- A countable compact-open cover has a subordinate pairwise disjoint
compact-open cover with the same indexing set. -/
theorem countable_compactOpen_disjoint_refinement [T2Space X]
    (K : ℕ → Set X) (hKc : ∀ n, IsCompact (K n)) (hKo : ∀ n, IsOpen (K n)) :
    ∃ L : ℕ → Set X,
      (∀ n, IsCompact (L n) ∧ IsOpen (L n) ∧ L n ⊆ K n) ∧
      Pairwise (fun n m => Disjoint (L n) (L m)) ∧
      (⋃ n, L n) = ⋃ n, K n := by
  exact ⟨compactOpenPiece K,
    fun n => ⟨compactOpenPiece_isCompact K hKc hKo n,
      compactOpenPiece_isOpen K hKc hKo n, compactOpenPiece_subset K n⟩,
    compactOpenPiece_pairwiseDisjoint K, iUnion_compactOpenPiece K⟩

/-- An open cover of a compact open subspace has a finite, pairwise disjoint
compact-open refinement in the ambient space. -/
theorem exists_compactOpen_disjoint_refinement [T2Space X] [TotallyDisconnectedSpace X]
    {ι : Type v} (W : Opens X) (hW : IsCompact (W : Set X))
    (U : ι → Opens X) (hcover : W ≤ iSup U) :
    ∃ (n : ℕ) (V : Fin n → Opens X) (j : Fin n → ι),
      Pairwise (fun a b => Disjoint (V a) (V b)) ∧
      (∀ k, V k ≤ U (j k)) ∧ W ≤ iSup V ∧
      (∀ k, IsCompact (V k : Set X)) := by
  classical
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let U' : ι → Opens W := fun i =>
    ⟨Subtype.val ⁻¹' (U i : Set X), (U i).isOpen.preimage continuous_subtype_val⟩
  have hU' : IsOpenCover U' := by
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover x.property)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨n, C, hCsub, hCcover, hCdisj⟩ :=
    hU'.exists_finite_nonempty_disjoint_clopen_cover
  choose j hj using fun k => (hCsub k).2
  let V : Fin n → Opens X := fun k =>
    ⟨Subtype.val '' (C k : Set W),
      W.isOpen.isOpenMap_subtype_val _ (C k).isOpen⟩
  refine ⟨n, V, j, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply Opens.coe_disjoint.mp
    apply Set.disjoint_left.mpr
    rintro x ⟨xa, hxa, rfl⟩ ⟨xb, hxb, hxb_eq⟩
    have heq : xb = xa := Subtype.ext hxb_eq
    subst xb
    have hdisj : Disjoint (C a : Set W) (C b : Set W) := by
      simpa [disjoint_iff, ← SetLike.coe_set_eq] using hCdisj hab
    exact Set.disjoint_left.mp hdisj hxa hxb
  · intro k x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hj k hy
  · intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hCcover (Set.mem_univ (⟨x, hx⟩ : W)))
    exact Opens.mem_iSup.mpr ⟨k, ⟨⟨x, hx⟩, hk, rfl⟩⟩
  · intro k
    exact (C k).isClosed.isCompact.image continuous_subtype_val

/-- Universe-aligned form convenient for applications with arbitrary cover indices. -/
theorem exists_disjoint_open_refinement [T2Space X] [TotallyDisconnectedSpace X]
    {ι : Type v} (W : Opens X) (hW : IsCompact (W : Set X))
    (U : ι → Opens X) (hcover : W ≤ iSup U) :
    ∃ (κ : Type u) (V : κ → Opens X) (j : κ → ι),
      Pairwise (fun a b => Disjoint (V a) (V b)) ∧
      (∀ k, V k ≤ U (j k)) ∧ W ≤ iSup V := by
  obtain ⟨n, V, j, hdisj, hsub, hcover', _⟩ :=
    exists_compactOpen_disjoint_refinement W hW U hcover
  refine ⟨ULift.{u} (Fin n), fun k => V k.down, fun k => j k.down, ?_, ?_, ?_⟩
  · exact hdisj.comp_of_injective ULift.down_injective
  · exact fun k => hsub k.down
  · intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcover' hx)
    exact Opens.mem_iSup.mpr ⟨ULift.up k, hk⟩

end Aoki.Topology
