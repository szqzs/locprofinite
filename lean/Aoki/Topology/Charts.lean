import Aoki.Topology.Quotient

/-!
# Canonical representatives on the quotient charts

On the chart where coordinate `i` is finite, every orbit has a unique
representative whose `i`th Boolean bit is false.
-/

namespace Aoki.Geometry

universe u

variable {A : ℕ → Type u} {n : ℕ}

/-- The gauge slice where the specified finite coordinate has bit zero. -/
def canonicalSlice (i : Fin (n + 1)) : Set (CompactProduct A n) :=
  {x | ∃ a : A i, x i = (↑(a, false) : OnePoint (A i × Bool))}

theorem canonicalSlice_subset_finiteCoordinate (i : Fin (n + 1)) :
    canonicalSlice (A := A) i ⊆ finiteCoordinate i := by
  rintro x ⟨a, ha⟩
  change x i ≠ OnePoint.infty
  rw [ha]
  exact OnePoint.coe_ne_infty _

/-- The quotient map on canonical representatives. -/
def sliceMap (i : Fin (n + 1)) : canonicalSlice (A := A) i → CompactQuotient A n :=
  fun x => quotientMap x.1

theorem sliceMap_injective (i : Fin (n + 1)) : Function.Injective (sliceMap (A := A) i) := by
  intro x y h
  change quotientMap x.1 = quotientMap y.1 at h
  rcases (quotientMap_eq_iff x.1 y.1).mp h with hxy | hxy
  · exact Subtype.ext hxy
  · obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    have hi := congrFun hxy i
    change x.1 i = onePointFlip (y.1 i) at hi
    rw [ha, hb] at hi
    simp [coordinateFlip] at hi

theorem range_sliceMap (i : Fin (n + 1)) :
    Set.range (sliceMap (A := A) i) = quotientMap '' finiteCoordinate i := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, canonicalSlice_subset_finiteCoordinate i x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change x i ≠ OnePoint.infty at hx
    cases hi : x i with
    | infty => exact (hx hi).elim
    | coe z =>
      rcases z with ⟨a, b⟩
      cases b with
      | false => exact ⟨⟨x, a, hi⟩, rfl⟩
      | true =>
        refine ⟨⟨flip x, a, ?_⟩, ?_⟩
        · change onePointFlip (x i) = _
          rw [hi]
          rfl
        · exact (quotientMap_eq_iff (flip x) x).mpr (Or.inr rfl)

section Topology

variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

theorem isOpen_canonicalSlice (i : Fin (n + 1)) :
    IsOpen (canonicalSlice (A := A) i) := by
  have h : IsOpen (((↑) : A i × Bool → OnePoint (A i × Bool)) ''
      Set.range (fun a : A i => (a, false))) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete _)
  have hc : Continuous (fun x : CompactProduct A n => x i) := continuous_apply i
  convert h.preimage hc using 1
  ext x
  simp [canonicalSlice, eq_comm]

theorem isOpenEmbedding_sliceMap (i : Fin (n + 1)) :
    Topology.IsOpenEmbedding (sliceMap (A := A) i) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotientMap.comp continuous_subtype_val
  · exact sliceMap_injective i
  · exact isOpenMap_quotientMap.comp (isOpen_canonicalSlice i).isOpenEmbedding_subtypeVal.isOpenMap

/-- The actual chart is homeomorphic to its canonical gauge slice. -/
noncomputable def sliceHomeomorph (i : Fin (n + 1)) :
    canonicalSlice (A := A) i ≃ₜ (quotientMap '' finiteCoordinate (A := A) i) :=
  (isOpenEmbedding_sliceMap i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_sliceMap i))

/-- The compact product of all coordinates except the chosen chart coordinate. -/
abbrev ChartRemainder (A : ℕ → Type u) (n : ℕ) (i : Fin (n + 1)) :=
  (j : {j : Fin (n + 1) // j ≠ i}) → OnePoint (A j.1 × Bool)

/-- Insert the finite coordinate with Boolean bit false. -/
def insertFalse (i : Fin (n + 1)) :
    A i × ChartRemainder A n i → CompactProduct A n := fun z =>
  (Homeomorph.piSplitAt i (fun j : Fin (n + 1) => OnePoint (A j × Bool))).symm
    (↑(z.1, false), z.2)

omit [∀ (i : ℕ), DiscreteTopology (A i)] in
theorem isEmbedding_insertFalse (i : Fin (n + 1)) :
    Topology.IsEmbedding (insertFalse (A := A) i) := by
  have h : Topology.IsEmbedding (fun a : A i => (↑(a, false) : OnePoint (A i × Bool))) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp (isEmbedding_prodMkLeft false)
  exact (Homeomorph.piSplitAt i (fun j : Fin (n + 1) => OnePoint (A j × Bool))).symm.isEmbedding.comp
    (h.prodMap Topology.IsEmbedding.id)

omit [∀ (i : ℕ), DiscreteTopology (A i)] in
theorem range_insertFalse (i : Fin (n + 1)) :
    Set.range (insertFalse (A := A) i) = canonicalSlice i := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z.1, ?_⟩
    simp [insertFalse, Homeomorph.piSplitAt_symm_apply]
  · rintro ⟨a, ha⟩
    refine ⟨(a, fun j => x j.1), ?_⟩
    let h := Homeomorph.piSplitAt i (fun j : Fin (n + 1) => OnePoint (A j × Bool))
    apply h.injective
    change h (h.symm _) = h x
    rw [h.apply_symm_apply]
    exact Prod.ext ha.symm rfl

/-- A chart is a discrete family of copies of a compact profinite product. -/
noncomputable def chartProductHomeomorph (i : Fin (n + 1)) :
    (A i × ChartRemainder A n i) ≃ₜ (quotientMap '' finiteCoordinate (A := A) i) :=
  ((isEmbedding_insertFalse i).toHomeomorph.trans
    (Homeomorph.setCongr (range_insertFalse i))).trans (sliceHomeomorph i)

end Topology

end Aoki.Geometry
