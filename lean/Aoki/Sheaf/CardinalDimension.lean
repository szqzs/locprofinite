import Aoki.Sheaf.FreeOpenExact
import Aoki.Sheaf.FreeOpenBasic
import Aoki.Sheaf.FreeOpenColimit
import Aoki.Sheaf.FreeOpenFiltration
import Aoki.Sheaf.CountableVanishing
import Aoki.Homological.TransfiniteDimension
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Cardinal bounds for the projective dimension of free open sheaves
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Aoki

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Cardinal

universe u

variable {X : TopCat.{u}}

/-- Adding a projective open raises the bound on the intersection by at most
one for the successive quotient. -/
theorem freeOpenUnionQuotient_dimension (V W : Opens X) (n : ℕ)
    [Projective (freeOpen W)]
    (h : HasProjectiveDimensionLE (freeOpen (V ⊓ W)) n) :
    HasProjectiveDimensionLE
      (cokernel (freeOpenMap (homOfLE (le_sup_left : V ≤ V ⊔ W)))) (n + 1) := by
  let f := freeOpenMap (homOfLE (inf_le_right : V ⊓ W ≤ W))
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  haveI : HasProjectiveDimensionLE (cokernel f) (n + 1) :=
    hS.hasProjectiveDimensionLT_X₃ (n + 1) h
      (hasProjectiveDimensionLT_of_ge (freeOpen W) 1 (n + 2) (by omega))
  exact hasProjectiveDimensionLT_of_iso (freeOpenUnionQuotientIso V W) (n + 2)

/-- A form of the successor quotient bound with an explicitly identified
target open, avoiding any dependence on the chosen inclusion proof. -/
theorem freeOpenUnionQuotient_dimension_of_eq (V W T : Opens X) (n : ℕ)
    (hT : T = V ⊔ W) (hVT : V ≤ T) [Projective (freeOpen W)]
    (h : HasProjectiveDimensionLE (freeOpen (V ⊓ W)) n) :
    HasProjectiveDimensionLE (cokernel (freeOpenMap (homOfLE hVT))) (n + 1) := by
  subst T
  exact freeOpenUnionQuotient_dimension V W n h

variable [T2Space X] [TotallyDisconnectedSpace X]

/-- A union of at most `aleph n` compact opens has projective dimension at
most `n`. The induction uses the initial ordinal of the indexing cardinal,
binary Mayer--Vietoris, and closure under transfinite extensions. -/
theorem freeOpen_iSup_projectiveDimensionLE (n : ℕ) {ι : Type u}
    (K : ι → Opens X) (hK : ∀ i, IsCompact (K i : Set X))
    (hcard : Cardinal.mk ι ≤ Cardinal.aleph n) :
    HasProjectiveDimensionLE (freeOpen (iSup K)) n := by
  classical
  induction n generalizing ι with
  | zero =>
    haveI : Countable ι := Cardinal.mk_le_aleph0_iff.mp (by simpa using hcard)
    letI := projective_freeOpen_iSup_of_countable K hK
    infer_instance
  | succ n ih =>
    let J := (Cardinal.aleph (n + 1)).ord.ToType
    have hJ : Cardinal.mk J = Cardinal.aleph (n + 1) := Cardinal.mk_ord_toType _
    obtain ⟨e⟩ : Nonempty (ι ↪ J) := (Cardinal.le_def ι J).mp (by simpa [hJ] using hcard)
    let L : J → Opens X := Function.extend e K ⊥
    have hL : ∀ j, IsCompact (L j : Set X) := by
      intro j
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        simpa [L, e.injective.extend_apply] using hK i
      · simp [L, Function.extend_apply' K ⊥ j hj]
    have hsup : iSup L = iSup K := iSup_extend_bot e.injective K
    haveI : Nonempty J := Ordinal.nonempty_toType_iff.mpr (by
      intro hz
      have hz' := congrArg Ordinal.card hz
      have hpos := Cardinal.aleph0_pos.trans_le (Cardinal.aleph0_le_aleph (n + 1))
      simpa using hpos.ne' (by simpa using hz'))
    letI : OrderBot J := WellFoundedLT.toOrderBot J
    letI : SuccOrder J := SuccOrder.ofLinearWellFoundedLT J
    letI : NoMaxOrder J := Cardinal.noMaxOrder (Cardinal.aleph0_le_aleph (n + 1))
    rw [← hsup, ← iSup_initialOpenUnion L]
    apply hasProjectiveDimensionLE_of_transfinite
      (freeOpenUnionCocone (initialOpenUnion L))
      (freeOpenUnionCoconeIsColimit (initialOpenUnion L))
      (by simpa using (freeOpen_bot_isZero (X := X)))
      (fun j hj => by change Mono (freeOpenMap _); infer_instance) (n + 1)
    intro j hj
    have hsmall : Cardinal.mk (Set.Iio j) ≤ Cardinal.aleph n := by
      have hlt : Cardinal.mk (Set.Iio j) < Cardinal.aleph (n + 1) := by
        simpa [hJ] using (Cardinal.mk_Iio_lt j (by simp [J]))
      simpa only [Nat.cast_add, Nat.cast_one, ← Cardinal.succ_aleph,
        Order.lt_succ_iff] using hlt
    have hinter : HasProjectiveDimensionLE
        (freeOpen (initialOpenUnion L j ⊓ L j)) n := by
      have heq : initialOpenUnion L j ⊓ L j = ⨆ i : Set.Iio j, L i.val ⊓ L j :=
        iSup_inf_eq _ _
      rw [heq]
      exact ih (fun i : Set.Iio j => L i.val ⊓ L j)
        (fun i => (hL i.val).inter (hL j)) hsmall
    letI := projective_freeOpen_of_isCompact (L j) (hL j)
    change HasProjectiveDimensionLE (cokernel (freeOpenMap
      (homOfLE ((initialOpenUnion L).monotone (Order.le_succ j))))) (n + 1)
    exact freeOpenUnionQuotient_dimension_of_eq (initialOpenUnion L j) (L j)
      (initialOpenUnion L (Order.succ j)) n (initialOpenUnion_succ L j hj) _ hinter

/-- A compact-open cover with at most `aleph n` members forces ordinary
sheaf cohomology to vanish in every degree strictly above `n`. -/
theorem sheaf_cohomology_eq_zero_of_compactOpen_cover_cardinal (n : ℕ)
    {ι : Type u} (K : ι → Opens X) (hK : ∀ i, IsCompact (K i : Set X))
    (hcard : Cardinal.mk ι ≤ Cardinal.aleph n) (hcover : iSup K = ⊤)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (d : ℕ) (hd : n < d)
    (a : CategoryTheory.Sheaf.H M d) : a = 0 := by
  haveI : HasProjectiveDimensionLE (freeOpen (⊤ : Opens X)) n := by
    rw [← hcover]
    exact freeOpen_iSup_projectiveDimensionLE n K hK hcard
  haveI : HasProjectiveDimensionLE
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) n :=
    hasProjectiveDimensionLT_of_iso (freeOpenTopIso X) (n + 1)
  exact a.eq_zero_of_hasProjectiveDimensionLT (n + 1) hd

variable [LocallyCompactSpace X]

/-- The cardinality upper bound for ordinary abelian sheaf cohomology on
a locally profinite Hausdorff space, in every finite cardinal degree. -/
theorem sheaf_cohomology_eq_zero_of_cardinal_le_aleph (n : ℕ)
    (hcard : Cardinal.mk X ≤ Cardinal.aleph n)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (d : ℕ) (hd : n < d)
    (a : CategoryTheory.Sheaf.H M d) : a = 0 := by
  obtain ⟨K, hK, hcover⟩ := Topology.exists_point_indexed_compactOpen_cover (X := X)
  exact sheaf_cohomology_eq_zero_of_compactOpen_cover_cardinal n K hK hcard hcover M d hd a

/-- The weight upper bound for ordinary abelian sheaf cohomology on a
locally profinite Hausdorff space. -/
theorem sheaf_cohomology_eq_zero_of_weight_le_aleph (n : ℕ)
    (hweight : Topology.weight X ≤ Cardinal.aleph n)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (d : ℕ) (hd : n < d)
    (a : CategoryTheory.Sheaf.H M d) : a = 0 := by
  have hcard : Cardinal.mk (CompactOpens X) ≤ Cardinal.aleph n :=
    Topology.mk_compactOpens_le_weight.trans
      (max_le (Cardinal.aleph0_le_aleph _) hweight)
  exact sheaf_cohomology_eq_zero_of_compactOpen_cover_cardinal n CompactOpens.toOpens
    (fun K => K.isCompact) hcard Topology.iSup_compactOpens_eq_top M d hd a

/-- Below `aleph r`, degree-`r` sheaf cohomology vanishes for positive `r`. -/
theorem sheaf_cohomology_eq_zero_of_cardinal_lt_aleph {r : ℕ} (hr : 0 < r)
    (hcard : Cardinal.mk X < Cardinal.aleph r)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (a : CategoryTheory.Sheaf.H M r) : a = 0 := by
  cases r with
  | zero => omega
  | succ n =>
    have hle : Cardinal.mk X ≤ Cardinal.aleph n := by
      simpa only [Nat.cast_add, Nat.cast_one, ← Cardinal.succ_aleph,
        Order.lt_succ_iff] using hcard
    exact sheaf_cohomology_eq_zero_of_cardinal_le_aleph n hle M (n + 1) (by omega) a

/-- The corresponding strict weight bound for positive-degree cohomology. -/
theorem sheaf_cohomology_eq_zero_of_weight_lt_aleph {r : ℕ} (hr : 0 < r)
    (hweight : Topology.weight X < Cardinal.aleph r)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (a : CategoryTheory.Sheaf.H M r) : a = 0 := by
  cases r with
  | zero => omega
  | succ n =>
    have hle : Topology.weight X ≤ Cardinal.aleph n := by
      simpa only [Nat.cast_add, Nat.cast_one, ← Cardinal.succ_aleph,
        Order.lt_succ_iff] using hweight
    exact sheaf_cohomology_eq_zero_of_weight_le_aleph n hle M (n + 1) (by omega) a

/-- Nonzero positive-degree cohomology forces the sharp cardinal lower bound. -/
theorem aleph_le_cardinal_of_nonzero_sheaf_cohomology {r : ℕ} (hr : 0 < r)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (a : CategoryTheory.Sheaf.H M r) (ha : a ≠ 0) :
    Cardinal.aleph r ≤ Cardinal.mk X := by
  by_contra h
  exact ha (sheaf_cohomology_eq_zero_of_cardinal_lt_aleph hr (lt_of_not_ge h) M a)

/-- Nonzero positive-degree cohomology forces the sharp weight lower bound. -/
theorem aleph_le_weight_of_nonzero_sheaf_cohomology {r : ℕ} (hr : 0 < r)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (a : CategoryTheory.Sheaf.H M r) (ha : a ≠ 0) :
    Cardinal.aleph r ≤ Topology.weight X := by
  by_contra h
  exact ha (sheaf_cohomology_eq_zero_of_weight_lt_aleph hr (lt_of_not_ge h) M a)

end Aoki
