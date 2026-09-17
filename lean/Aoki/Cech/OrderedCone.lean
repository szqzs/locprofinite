import Aoki.Cech.Resolution
import Aoki.Sheaf.FreeOpenStalk
import Mathlib.Data.Fin.Tuple.Basic

/-! # Cone identities for ordered faces -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace
namespace Aoki.Cech
universe u v w

/-- Prepending a strictly smaller vertex preserves the increasing-face condition. -/
def prependFace {N n : ℕ} (p : Fin N) (s : Face N n) (h : p < s 0) : Face N (n + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cons p s) (by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact (lt_irrefl _ hab).elim
      | succ b => exact h.trans_le (s.monotone (Fin.zero_le b))
    | succ a =>
      cases b using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hab).elim
      | succ b => exact s.strictMono (Fin.succ_lt_succ_iff.mp hab))

@[simp] theorem prependFace_zero {N n : ℕ} (p : Fin N) (s : Face N n) (h : p < s 0) :
    prependFace p s h 0 = p := by simp [prependFace]

@[simp] theorem prependFace_succ {N n : ℕ} (p : Fin N) (s : Face N n) (h : p < s 0)
    (j : Fin (n + 1)) : prependFace p s h j.succ = s j := by simp [prependFace]

@[simp] theorem delete_prepend_zero {N n : ℕ} (p : Fin N) (s : Face N n) (h : p < s 0) :
    deleteFace (prependFace p s h) 0 = s := by
  apply DFunLike.ext
  intro j
  simp

@[simp] theorem delete_prepend_succ {N n : ℕ} (p : Fin N) (s : Face N (n + 1))
    (h : p < s 0) (j : Fin (n + 2)) :
    deleteFace (prependFace p s h) j.succ =
      prependFace p (deleteFace s j) (h.trans_le (s.monotone (Fin.zero_le _))) := by
  apply DFunLike.ext
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · simp [Fin.succ_succAbove_succ]

@[simp] theorem deleteFace_succ_zero {N n : ℕ} (s : Face N (n + 1)) (j : Fin (n + 1)) :
    deleteFace s j.succ 0 = s 0 := by simp

theorem prepend_delete_zero {N n : ℕ} (p : Fin N) (s : Face N (n + 1)) (h : s 0 = p) :
    prependFace p (deleteFace s 0)
      (by rw [← h]; exact s.strictMono (Fin.zero_lt_one)) = s := by
  apply DFunLike.ext
  intro j
  cases j using Fin.cases with
  | zero => simpa using h.symm
  | succ j => simp

section Coefficients
variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

theorem faceOpen_prepend {n : ℕ} (p : Fin N) (s : Face N n) (h : p < s 0) :
    faceOpen U (prependFace p s h) = U p ⊓ faceOpen U s := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · exact (iInf_le (fun j => U (prependFace p s h j)) 0).trans_eq (by simp)
    · refine le_iInf fun j => ?_
      exact (iInf_le (fun k => U (prependFace p s h k)) j.succ).trans_eq (by simp)
  · refine le_iInf fun j => ?_
    cases j using Fin.cases with
    | zero => simp only [prependFace_zero]; exact inf_le_left
    | succ j =>
      exact inf_le_right.trans ((iInf_le (fun k => U (s k)) j).trans_eq (by simp))

theorem faceOpen_prepend_le {n : ℕ} (p : Fin N) (s : Face N n) (h : p < s 0) :
    faceOpen U (prependFace p s h) ≤ faceOpen U s := by
  rw [faceOpen_prepend]
  exact inf_le_right

/-- A cone condition on the coefficient functor: adjoining `p` changes no coefficient. -/
abbrev HasConeCoefficients (p : Fin N) : Prop :=
  (∀ n (s : Face N n), s 0 < p → IsZero (F.obj (faceOpen U s))) ∧
  (∀ n (s : Face N n) (h : p < s 0),
    IsIso (F.map (homOfLE (faceOpen_prepend_le U p s h))))

/-- The contraction prepends the cone vertex whenever it is absent. -/
def orderedContraction (p : Fin N) (hp : HasConeCoefficients U F p) (n : ℕ) :
    orderedTerm U F n ⟶ orderedTerm U F (n + 1) :=
  Sigma.desc fun s => if h : p < s 0 then
    letI := hp.2 n s h
    inv (F.map (homOfLE (faceOpen_prepend_le U p s h))) ≫
      Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) (prependFace p s h)
  else 0

@[reassoc, simp] theorem ι_orderedContraction_lt (p : Fin N)
    (hp : HasConeCoefficients U F p) (n : ℕ) (s : Face N n) (h : p < s 0) :
    Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) s ≫ orderedContraction U F p hp n =
      @inv _ _ _ _ (F.map (homOfLE (faceOpen_prepend_le U p s h))) (hp.2 n s h) ≫
        Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) (prependFace p s h) := by
  dsimp only [orderedContraction, orderedTerm]
  rw [Sigma.ι_desc, dif_pos h]

@[reassoc, simp] theorem ι_orderedContraction_not_lt (p : Fin N)
    (hp : HasConeCoefficients U F p) (n : ℕ) (s : Face N n) (h : ¬ p < s 0) :
    Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) s ≫ orderedContraction U F p hp n = 0 := by
  dsimp only [orderedContraction, orderedTerm]
  rw [Sigma.ι_desc, dif_neg h]

omit [Preadditive C] [HasFiniteCoproducts C] in
theorem map_isIso_congr {V V' W : Opens X} (h : V = V') (hV : V ≤ W) (hV' : V' ≤ W)
    [IsIso (F.map (homOfLE hV))] : IsIso (F.map (homOfLE hV')) := by
  subst V'
  infer_instance

omit [Preadditive C] in
theorem inv_map_ι_congr {n : ℕ} {W : Opens X} {s t : Face N n} (h : s = t)
    (hs : faceOpen U s ≤ W) (ht : faceOpen U t ≤ W)
    [IsIso (F.map (homOfLE hs))] [IsIso (F.map (homOfLE ht))] :
    inv (F.map (homOfLE hs)) ≫ Sigma.ι (fun q : Face N n => F.obj (faceOpen U q)) s =
      inv (F.map (homOfLE ht)) ≫ Sigma.ι (fun q : Face N n => F.obj (faceOpen U q)) t := by
  subst t
  rfl

/-- The first face of a newly coned simplex returns that simplex. -/
@[reassoc] theorem contraction_firstFace_lt (p : Fin N)
    (hp : HasConeCoefficients U F p) (n : ℕ) (s : Face N n) (h : p < s 0) :
    Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) s ≫
      orderedContraction U F p hp n ≫ orderedFace U F n 0 =
        Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) s := by
  letI := hp.2 n s h
  erw [ι_orderedContraction_lt_assoc U F p hp n s h]
  erw [ι_orderedFace]
  erw [map_ι_congr U F (delete_prepend_zero p s h)
    (faceOpen_le_delete U _ 0) (faceOpen_prepend_le U p s h)]
  simp only [IsIso.inv_hom_id_assoc]

set_option maxHeartbeats 800000 in
/-- All other coned faces commute with deletion of a vertex. -/
@[reassoc] theorem contraction_face_succ_lt (p : Fin N)
    (hp : HasConeCoefficients U F p) (n : ℕ) (s : Face N (n + 1))
    (h : p < s 0) (j : Fin (n + 2)) :
    Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s ≫
      orderedContraction U F p hp (n + 1) ≫ orderedFace U F (n + 1) j.succ =
    Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s ≫
      orderedFace U F n j ≫ orderedContraction U F p hp n := by
  let hd : p < deleteFace s j 0 := h.trans_le (s.monotone (Fin.zero_le _))
  letI := hp.2 (n + 1) s h
  letI := hp.2 n (deleteFace s j) hd
  erw [ι_orderedContraction_lt_assoc U F p hp (n + 1) s h, ι_orderedFace,
    ι_orderedFace_assoc, ι_orderedContraction_lt U F p hp n (deleteFace s j) hd]
  have hle : faceOpen U (prependFace p s h) ≤ faceOpen U (prependFace p (deleteFace s j) hd) := by
    erw [faceOpen_prepend, faceOpen_prepend]
    exact inf_le_inf_left _ (faceOpen_le_delete U s j)
  erw [map_ι_congr U F (delete_prepend_succ p s h j) (faceOpen_le_delete U _ _) hle]
  erw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (IsIso.inv_comp_eq _).2
  rw [← Category.assoc]
  apply (IsIso.eq_comp_inv _).2
  simp only [← F.map_comp]
  congr 1


/-- Deleting the cone vertex and then coning returns a simplex containing that vertex. -/
@[reassoc] theorem firstFace_contraction_eq (p : Fin N)
    (hp : HasConeCoefficients U F p) (n : ℕ) (s : Face N (n + 1)) (h : s 0 = p) :
    Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s ≫
      orderedFace U F n 0 ≫ orderedContraction U F p hp n =
        Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s := by
  have hd : p < deleteFace s 0 0 := by rw [← h]; exact s.strictMono Fin.zero_lt_one
  letI := hp.2 n (deleteFace s 0) hd
  haveI : IsIso (F.map (homOfLE (faceOpen_le_delete U s 0))) :=
    map_isIso_congr F (congrArg (faceOpen U) (prepend_delete_zero p s h))
      (faceOpen_prepend_le U p (deleteFace s 0) hd) (faceOpen_le_delete U s 0)
  erw [ι_orderedFace_assoc, ι_orderedContraction_lt U F p hp n (deleteFace s 0) hd]
  erw [inv_map_ι_congr U F (prepend_delete_zero p s h) _ (faceOpen_le_delete U s 0)]
  simp

/-- Deleting any other vertex leaves the cone vertex present, so coning is zero. -/
@[reassoc] theorem face_succ_contraction_eq (p : Fin N)
    (hp : HasConeCoefficients U F p) (n : ℕ) (s : Face N (n + 1))
    (h : s 0 = p) (j : Fin (n + 1)) :
    Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s ≫
      orderedFace U F n j.succ ≫ orderedContraction U F p hp n = 0 := by
  erw [ι_orderedFace_assoc, ι_orderedContraction_not_lt]
  · simp
  · simp [h]

/-- The ordered cone gives a contracting homotopy in positive degrees. -/
theorem orderedContraction_identity (p : Fin N) (hp : HasConeCoefficients U F p) (n : ℕ) :
    orderedContraction U F p hp (n + 1) ≫ orderedDifferential U F (n + 1) +
      orderedDifferential U F n ≫ orderedContraction U F p hp n =
        𝟙 (orderedTerm U F (n + 1)) := by
  apply Sigma.hom_ext
  intro s
  rcases lt_trichotomy (s 0) p with hs | hs | hs
  · exact (hp.1 (n + 1) s hs).eq_of_src _ _
  · have hn : ¬ p < s 0 := by simp [hs]
    simp only [comp_add, Category.comp_id]
    rw [ι_orderedContraction_not_lt_assoc U F p hp (n + 1) s hn, zero_comp, zero_add]
    dsimp only [orderedDifferential, alternatingDifferential]
    simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp]
    erw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
      firstFace_contraction_eq U F p hp n s hs,
      face_succ_contraction_eq U F p hp n s hs, smul_zero, Finset.sum_const_zero, add_zero]
  · simp only [comp_add, Category.comp_id]
    dsimp only [orderedDifferential, alternatingDifferential]
    simp only [comp_sum, sum_comp, comp_zsmul, zsmul_comp]
    erw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
      contraction_firstFace_lt U F p hp (n + 1) s hs,
      contraction_face_succ_lt U F p hp n s hs,
      pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    exact neg_add_cancel_right _ _

end Coefficients

section Exactness
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A contraction identity implies exactness of a short complex. -/
theorem exact_of_contracting_identity
    (S : ShortComplex C) (hleft : S.X₂ ⟶ S.X₁) (hright : S.X₃ ⟶ S.X₂)
    (h : hleft ≫ S.f + S.g ≫ hright = 𝟙 S.X₂) : S.Exact := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  calc
    kernel.ι S.g ≫ cokernel.π S.f =
        kernel.ι S.g ≫ (hleft ≫ S.f + S.g ≫ hright) ≫ cokernel.π S.f := by rw [h]; simp
    _ = 0 := by simp [add_comp, Category.assoc, ← Category.assoc (kernel.ι S.g) S.g]

variable {X : Type w} [TopologicalSpace X]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

/-- With cone coefficients, the ordered complex is exact in each positive degree. -/
theorem orderedComplex_exactAt_succ
    (p : Fin N) (hp : HasConeCoefficients U F p) (n : ℕ) :
    (orderedComplex U F).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply exact_of_contracting_identity _
    (orderedContraction U F p hp (n + 1)) (orderedContraction U F p hp n)
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
  simp only [orderedComplex_X, orderedComplex_d]
  exact orderedContraction_identity U F p hp n

end Exactness
end Aoki.Cech
