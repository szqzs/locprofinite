import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.Topology.Sets.Opens

/-!
# The finite ordered Čech chain complex

This construction uses strictly increasing faces of a finite family of opens.
Only a covariant functor out of the category of opens and finite coproducts in a
preadditive target are required. Face identities and the chain-complex relation
are proved here; no exactness or cohomological comparison is asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace

namespace Aoki.Cech

universe u v w

section Alternating

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The alternating sum of the face maps of a semisimplicial family. -/
def alternatingDifferential (O : ℕ → C)
    (δ : ∀ n, Fin (n + 2) → (O (n + 1) ⟶ O n)) (n : ℕ) : O (n + 1) ⟶ O n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • δ n i

/-- Face identities suffice for the square-zero relation; no degeneracies are used. -/
theorem alternatingDifferential_sq (O : ℕ → C)
    (δ : ∀ n, Fin (n + 2) → (O (n + 1) ⟶ O n))
    (hδ : ∀ n (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc),
      δ (n + 1) j.succ ≫
          δ n (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) j.isLt)) =
        δ (n + 1) i ≫ δ n j)
    (n : ℕ) :
    alternatingDifferential O δ (n + 1) ≫ alternatingDifferential O δ n = 0 := by
  dsimp [alternatingDifferential]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [hδ]
      simpa [S] using! hij

end Alternating

/-- A degree-`k` face of the ordered set of `N` cover indices. -/
abbrev Face (N k : ℕ) := Fin (k + 1) ↪o Fin N

/-- Delete the `i`-th vertex of an increasing face. -/
def deleteFace {N n : ℕ} (s : Face N (n + 1)) (i : Fin (n + 2)) : Face N n :=
  (Fin.succAboveOrderEmb i).trans s

@[simp] theorem deleteFace_apply {N n : ℕ} (s : Face N (n + 1))
    (i : Fin (n + 2)) (j : Fin (n + 1)) : deleteFace s i j = s (i.succAbove j) := rfl

/-- The two orders of deleting two vertices agree. -/
theorem deleteFace_deleteFace {N n : ℕ} (s : Face N (n + 2))
    (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i ≤ j.castSucc) :
    deleteFace (deleteFace s j.succ)
        (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) j.isLt)) =
      deleteFace (deleteFace s i) j := by
  apply DFunLike.ext
  intro x
  apply congrArg s
  exact SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_δ'' h) x

section Ordered

variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

/-- The finite intersection attached to an increasing face. -/
def faceOpen {n : ℕ} (s : Face N n) : Opens X := ⨅ j, U (s j)

theorem faceOpen_le_delete {n : ℕ} (s : Face N (n + 1)) (i : Fin (n + 2)) :
    faceOpen U s ≤ faceOpen U (deleteFace s i) := by
  apply le_iInf
  intro j
  exact iInf_le (fun k => U (s k)) (i.succAbove j)

/-- The finite coproduct in one degree of the ordered complex. -/
abbrev orderedTerm (n : ℕ) : C := ∐ fun s : Face N n => F.obj (faceOpen U s)

/-- One face map, induced by deleting the corresponding cover index. -/
def orderedFace (n : ℕ) (i : Fin (n + 2)) : orderedTerm U F (n + 1) ⟶ orderedTerm U F n :=
  Sigma.desc fun s => F.map (homOfLE (faceOpen_le_delete U s i)) ≫
    Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) (deleteFace s i)

omit [Preadditive C] in
@[reassoc, simp]
theorem ι_orderedFace (n : ℕ) (i : Fin (n + 2)) (s : Face N (n + 1)) :
    Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s ≫ orderedFace U F n i =
      F.map (homOfLE (faceOpen_le_delete U s i)) ≫
        Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) (deleteFace s i) := by
  exact Sigma.ι_desc _ _

omit [Preadditive C] in
theorem map_ι_congr {n : ℕ} {V : Opens X} {s t : Face N n} (h : s = t)
    (hs : V ≤ faceOpen U s) (ht : V ≤ faceOpen U t) :
    F.map (homOfLE hs) ≫ Sigma.ι (fun q : Face N n => F.obj (faceOpen U q)) s =
      F.map (homOfLE ht) ≫ Sigma.ι (fun q : Face N n => F.obj (faceOpen U q)) t := by
  subst t
  rfl

omit [Preadditive C] in
/-- The concrete coproduct face maps obey the semisimplicial relation. -/
theorem orderedFace_comp (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (h : i ≤ j.castSucc) :
    orderedFace U F (n + 1) j.succ ≫
        orderedFace U F n
          (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) j.isLt)) =
      orderedFace U F (n + 1) i ≫ orderedFace U F n j := by
  apply Sigma.hom_ext
  intro s
  dsimp only [orderedFace, orderedTerm]
  simp only [Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc]
  rw [← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp]
  exact map_ι_congr U F (deleteFace_deleteFace s i j h) _ _

/-- The alternating differential of the finite ordered Čech complex. -/
def orderedDifferential (n : ℕ) : orderedTerm U F (n + 1) ⟶ orderedTerm U F n :=
  alternatingDifferential (orderedTerm U F) (orderedFace U F) n

theorem orderedDifferential_sq (n : ℕ) :
    orderedDifferential U F (n + 1) ≫ orderedDifferential U F n = 0 :=
  alternatingDifferential_sq _ _ (orderedFace_comp U F) n

/-- The ordered Čech chain complex of a finite open family and a covariant functor. -/
def orderedComplex : ChainComplex C ℕ :=
  ChainComplex.of (orderedTerm U F) (orderedDifferential U F) (orderedDifferential_sq U F)

@[simp] theorem orderedComplex_X (n : ℕ) : (orderedComplex U F).X n = orderedTerm U F n := rfl

@[simp] theorem orderedComplex_d (n : ℕ) :
    (orderedComplex U F).d (n + 1) n = orderedDifferential U F n := by
  simp [orderedComplex]

/-- There are no increasing `(k+1)`-tuples once `k ≥ N`. -/
theorem isEmpty_face {k : ℕ} (h : N ≤ k) : IsEmpty (Face N k) := by
  refine ⟨fun s => ?_⟩
  have hc := Fintype.card_le_of_injective s s.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- All chain objects in degrees at least the size of the cover are zero objects. -/
theorem orderedTerm_isZero {k : ℕ} (h : N ≤ k) : IsZero (orderedTerm U F k) := by
  letI := isEmpty_face h
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro s
  exact isEmptyElim s

theorem orderedComplex_isZero {k : ℕ} (h : N ≤ k) : IsZero ((orderedComplex U F).X k) :=
  orderedTerm_isZero U F h

end Ordered

end Aoki.Cech
