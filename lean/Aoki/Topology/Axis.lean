import Aoki.Topology.Charts

/-!
# Discrete axes in the punctured quotient
-/

namespace Aoki.Geometry

universe u

variable {A : ℕ → Type u} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- The quotient axis with only the selected coordinate finite. -/
noncomputable def axisQuotient (i : Fin (n + 1)) (a : A i) : CompactQuotient A n :=
  ((chartProductHomeomorph i) (a, fun _ => OnePoint.infty)).1

theorem isEmbedding_axisQuotient (i : Fin (n + 1)) :
    Topology.IsEmbedding (axisQuotient (A := A) i) :=
  Topology.IsEmbedding.subtypeVal.comp ((chartProductHomeomorph i).isEmbedding.comp
    (isEmbedding_prodMkLeft (fun _ => OnePoint.infty)))

theorem axisQuotient_ne_infty (i : Fin (n + 1)) (a : A i) :
    axisQuotient i a ≠ quotientMap (infty : CompactProduct A n) := by
  intro h
  have hm := ((chartProductHomeomorph (A := A) i) (a, fun _ => OnePoint.infty)).2
  obtain ⟨x, hx, hq⟩ := hm
  have hxinf : x = (infty : CompactProduct A n) :=
    (quotientMap_eq_infty_iff x).mp (hq.trans h)
  change x i ≠ OnePoint.infty at hx
  exact hx (congrFun hxinf i)

/-- The same discrete axis, regarded as a map into the punctured space. -/
noncomputable def axis (i : Fin (n + 1)) (a : A i) : U A n :=
  ⟨axisQuotient i a, axisQuotient_ne_infty i a⟩

theorem isEmbedding_axis (i : Fin (n + 1)) :
    Topology.IsEmbedding (axis (A := A) i) :=
  (isEmbedding_axisQuotient i).codRestrict _ (axisQuotient_ne_infty i)

theorem axis_injective (i : Fin (n + 1)) : Function.Injective (axis (A := A) i) :=
  (isEmbedding_axis i).injective

theorem mk_base_le_mk_U (i : Fin (n + 1)) : Cardinal.mk (A i) ≤ Cardinal.mk (U A n) :=
  Cardinal.mk_le_of_injective (axis_injective i)

end Aoki.Geometry
