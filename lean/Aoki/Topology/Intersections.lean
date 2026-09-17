import Aoki.Topology.Charts

/-!
# Disjoint compact-open cells in finite intersections of quotient charts
-/

namespace Aoki.Geometry

universe u

variable {A : ℕ → Type u} {n : ℕ}

/-- Labels for the finite coordinates, with one chosen bit fixed to false. -/
def GaugeLabel (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I) :=
  {v : (j : I) → A j.1 × Bool // (v ⟨i, hi⟩).2 = false}

/-- A compact-open cylinder before taking the quotient. -/
def cylinder {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} {hi : i ∈ I}
    (v : GaugeLabel (A := A) I i hi) : Set (CompactProduct A n) :=
  {x | ∀ j : I, x j.1 = (↑(v.1 j) : OnePoint (A j.1 × Bool))}

/-- The image of a labeled cylinder in the compact orbit space. -/
def quotientCell {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} {hi : i ∈ I}
    (v : GaugeLabel (A := A) I i hi) : Set (CompactQuotient A n) :=
  quotientMap '' cylinder v

theorem infty_notMem_quotientCell {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    quotientMap infty ∉ quotientCell v := by
  rintro ⟨x, hx, h⟩
  have hxi := hx ⟨i, hi⟩
  rw [(quotientMap_eq_infty_iff x).mp h] at hxi
  exact (OnePoint.coe_ne_infty (v.1 ⟨i, hi⟩)) hxi.symm

theorem quotientCell_pairwiseDisjoint (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) :
    Pairwise (fun v w : GaugeLabel (A := A) I i hi => Disjoint (quotientCell v) (quotientCell w)) := by
  intro v w hvw
  apply Set.disjoint_left.mpr
  rintro q ⟨x, hx, hxq⟩ ⟨y, hy, hyq⟩
  rcases (quotientMap_eq_iff x y).mp (hxq.trans hyq.symm) with hxy | hxy
  · apply hvw
    apply Subtype.ext
    funext j
    exact OnePoint.coe_injective ((hx j).symm.trans ((congrFun hxy j.1).trans (hy j)))
  · have h := (hx ⟨i, hi⟩).symm.trans (congrFun hxy i)
    change (↑(v.1 ⟨i, hi⟩) : OnePoint (A i × Bool)) = onePointFlip (y i) at h
    rw [hy ⟨i, hi⟩] at h
    have hbits := congrArg Prod.snd (OnePoint.coe_injective h)
    change (v.1 ⟨i, hi⟩).2 = !(w.1 ⟨i, hi⟩).2 at hbits
    rw [v.2, w.2] at hbits
    cases hbits

theorem exists_quotientCell_iff (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) (q : CompactQuotient A n) :
    (∃ v : GaugeLabel (A := A) I i hi, q ∈ quotientCell v) ↔
      ∀ j ∈ I, q ∈ quotientMap '' finiteCoordinate j := by
  classical
  constructor
  · rintro ⟨v, x, hx, rfl⟩ j hj
    apply (quotientMap_mem_finiteCoordinate_image_iff x j).mpr
    rw [hx ⟨j, hj⟩]
    exact OnePoint.coe_ne_infty _
  · intro h
    have hqi := h i hi
    rw [← range_sliceMap i] at hqi
    obtain ⟨x, hxq⟩ := hqi
    change quotientMap x.1 = q at hxq
    have hxfinite (j : I) : x.1 j.1 ≠ OnePoint.infty := by
      apply (quotientMap_mem_finiteCoordinate_image_iff x.1 j.1).mp
      rw [hxq]
      exact h j.1 j.2
    choose d hd using fun j : I => OnePoint.ne_infty_iff_exists.mp (hxfinite j)
    have hd0 : (d ⟨i, hi⟩).2 = false := by
      obtain ⟨a, ha⟩ := x.2
      exact congrArg Prod.snd (OnePoint.coe_injective ((hd ⟨i, hi⟩).trans ha))
    exact ⟨⟨d, hd0⟩, x.1, (fun j => (hd j).symm), hxq⟩

/-- The corresponding cell in the punctured quotient. -/
def cell {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} {hi : i ∈ I}
    (v : GaugeLabel (A := A) I i hi) : Set (U A n) :=
  {q | q.1 ∈ quotientCell v}

theorem cell_pairwiseDisjoint (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) :
    Pairwise (fun v w : GaugeLabel (A := A) I i hi => Disjoint (cell v) (cell w)) := by
  intro v w hvw
  apply Set.disjoint_left.mpr
  intro q hqv hqw
  exact Set.disjoint_left.mp (quotientCell_pairwiseDisjoint I i hi hvw) hqv hqw

theorem cells_cover_intersection (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) :
    (⋃ v : GaugeLabel (A := A) I i hi, cell v) = {q : U A n | ∀ j ∈ I, q ∈ chart j} := by
  ext q
  simp only [Set.mem_iUnion, cell, Set.mem_setOf_eq, chart]
  exact exists_quotientCell_iff I i hi q.1

section Topology

variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

theorem isClopen_cylinder {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    IsClopen (cylinder v) := by
  have hs (j : I) : IsClopen ({(↑(v.1 j) : OnePoint (A j.1 × Bool))} : Set _) := by
    refine ⟨isClosed_singleton, ?_⟩
    simpa only [Set.image_singleton] using
      OnePoint.isOpenEmbedding_coe.isOpenMap {(v.1 j)} (isOpen_discrete _)
  have h := isClopen_iInter_of_finite (fun j : I =>
    (hs j).preimage (show Continuous (fun x : CompactProduct A n => x j.1) from continuous_apply j.1))
  convert h using 1
  ext x
  simp [cylinder]

theorem isClopen_quotientCell {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    IsClopen (quotientCell v) :=
  ⟨((isClopen_cylinder v).isClosed.isCompact.image continuous_quotientMap).isClosed,
    isOpenMap_quotientMap _ (isClopen_cylinder v).isOpen⟩

theorem isCompact_quotientCell {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    IsCompact (quotientCell v) := (isClopen_quotientCell v).isClosed.isCompact

theorem isClopen_cell {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    IsClopen (cell v) := (isClopen_quotientCell v).preimage continuous_subtype_val

theorem isCompact_cell {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    IsCompact (cell v) := by
  change IsCompact (Subtype.val ⁻¹' quotientCell v :
    Set {q : CompactQuotient A n // q ≠ quotientMap infty})
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have h : Subtype.val '' cell v = quotientCell v := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hq
      have hne : q ≠ quotientMap infty := by
        intro heq
        exact infty_notMem_quotientCell v (heq ▸ hq)
      exact ⟨⟨q, hne⟩, hq, rfl⟩
  change IsCompact (Subtype.val '' cell v)
  rw [h]
  exact isCompact_quotientCell v

/-- Compact-open cells suitable for sheaf-theoretic projectivity arguments. -/
def cellOpen {I : Finset (Fin (n + 1))}
    {i : Fin (n + 1)} {hi : i ∈ I} (v : GaugeLabel (A := A) I i hi) :
    TopologicalSpace.Opens (U A n) := ⟨cell v, (isClopen_cell v).isOpen⟩

end Topology

end Aoki.Geometry
