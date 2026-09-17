import Aoki.Cech.Cocycle
import Aoki.Cech.Resolution
import Aoki.Sheaf.LocallyConstantScalar

/-!
# An explicit Alexander–Whitney chain lift

For the quotient's actual ordered free-module Čech resolution, the degree-one
lift deletes the first vertex and weights by the first transition function.
The cocycle identity proves its signed chain identity. Iterating the lift
produces exactly the consecutive-transition product cochains.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Aoki.Cech
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace Opposite Geometry

variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

theorem moduleSheaf_neg_eq_self {X : TopCat}
    {M N : TopCat.Sheaf (ModuleCat F) X} (f : M ⟶ N) : -f = f := by
  apply CategoryTheory.Sheaf.hom_ext
  ext W x
  change -((f.hom.app W).hom x) = (f.hom.app W).hom x
  rw [← neg_one_smul F, show (-1 : F) = 1 from by decide, one_smul]

theorem moduleSheaf_sign {X : TopCat}
    {M N : TopCat.Sheaf (ModuleCat F) X} (f : M ⟶ N) (k : ℕ) :
    (-1 : ℤ) ^ k • f = f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, neg_one_zsmul, moduleSheaf_neg_eq_self, ih]

/-- The adjacent edge scalar on a positive-dimensional face. -/
def firstTransition (k : ℕ) (s : Face (n + 1) (k + 1)) :
    LocallyConstant (faceOpen (chartOpen (A := A)) s) F :=
  transitionOnOpen _ (s 0) (s 1) (iInf_le _ 0) (iInf_le _ 1)

/-- Alexander–Whitney degree-one lift: weight the first face by the first edge. -/
def cupLift (k : ℕ) :
    orderedTerm (chartOpen (A := A) (n := n))
      (freeOpenModuleFunctor F (TopCat.of (U A n))) (k + 1) ⟶
    orderedTerm (chartOpen (A := A) (n := n))
      (freeOpenModuleFunctor F (TopCat.of (U A n))) k :=
  Sigma.desc fun s => locallyWeightedHom (firstTransition (A := A) k s)
    (freeOpenModuleMap F (X := TopCat.of (U A n)) (homOfLE (faceOpen_le_delete chartOpen s 0)) ≫
      Sigma.ι (fun t : Face (n + 1) k => freeOpenModule F (X := TopCat.of (U A n)) (faceOpen chartOpen t))
        (deleteFace s 0))

@[simp, reassoc] theorem ι_cupLift (k : ℕ) (s : Face (n + 1) (k + 1)) :
    Sigma.ι (fun t : Face (n + 1) (k + 1) => freeOpenModule F (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫
      cupLift (A := A) k =
    locallyWeightedHom (firstTransition (A := A) k s)
      (freeOpenModuleMap F (X := TopCat.of (U A n)) (homOfLE (faceOpen_le_delete chartOpen s 0)) ≫
        Sigma.ι (fun t : Face (n + 1) k => freeOpenModule F (X := TopCat.of (U A n)) (faceOpen chartOpen t))
          (deleteFace s 0)) := Sigma.ι_desc _ _

/-- In characteristic two the signs in the integral Čech differential disappear. -/
theorem moduleDifferential_eq_sum (k : ℕ) :
    orderedDifferential (chartOpen (A := A) (n := n))
      (freeOpenModuleFunctor F (TopCat.of (U A n))) k =
      ∑ i : Fin (k + 2), orderedFace chartOpen
        (freeOpenModuleFunctor F (TopCat.of (U A n))) k i := by
  simp only [orderedDifferential, alternatingDifferential, moduleSheaf_sign]

/-- A face inclusion into the corresponding summand. -/
def moduleFaceInclusion {k : ℕ} (V : Opens (U A n)) (s : Face (n + 1) k)
    (h : V ≤ faceOpen chartOpen s) :
    freeOpenModule F (X := TopCat.of (U A n)) V ⟶
      orderedTerm chartOpen (freeOpenModuleFunctor F (TopCat.of (U A n))) k :=
  freeOpenModuleMap F (homOfLE h) ≫
    Sigma.ι (fun t : Face (n + 1) k => freeOpenModule F (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s

theorem moduleFaceInclusion_congr {k : ℕ} {V : Opens (U A n)}
    {s t : Face (n + 1) k} (hst : s = t)
    (hs : V ≤ faceOpen chartOpen s) (ht : V ≤ faceOpen chartOpen t) :
    moduleFaceInclusion V s hs = moduleFaceInclusion V t ht := by subst t; rfl

theorem moduleMap_comp_faceInclusion {k : ℕ} {V W : Opens (U A n)} (i : V ⟶ W)
    (s : Face (n + 1) k) (h : W ≤ faceOpen chartOpen s) :
    freeOpenModuleMap F (X := TopCat.of (U A n)) i ≫ moduleFaceInclusion W s h =
      moduleFaceInclusion V s (i.le.trans h) := by
  dsimp only [moduleFaceInclusion]
  change (freeOpenModuleFunctor F (TopCat.of (U A n))).map i ≫
    (freeOpenModuleFunctor F (TopCat.of (U A n))).map (homOfLE h) ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

theorem moduleFaceInclusion_comp_face {k : ℕ} {V : Opens (U A n)}
    (s : Face (n + 1) (k + 1)) (h : V ≤ faceOpen chartOpen s) (i : Fin (k + 2)) :
    moduleFaceInclusion V s h ≫
        orderedFace chartOpen (freeOpenModuleFunctor F (TopCat.of (U A n))) k i =
      moduleFaceInclusion V (deleteFace s i) (h.trans (faceOpen_le_delete chartOpen s i)) := by
  dsimp only [moduleFaceInclusion]
  rw [Category.assoc]
  simp only [orderedFace, Sigma.ι_desc]
  exact moduleMap_comp_faceInclusion (homOfLE h) _ _

theorem moduleFaceInclusion_comp_lift {k : ℕ} {V : Opens (U A n)}
    (s : Face (n + 1) (k + 1)) (h : V ≤ faceOpen chartOpen s) :
    moduleFaceInclusion V s h ≫ cupLift k =
      locallyWeightedHom (restrictScalar (X := TopCat.of (U A n)) (homOfLE h) (firstTransition (A := A) k s))
        (moduleFaceInclusion V (deleteFace s 0)
          (h.trans (faceOpen_le_delete chartOpen s 0))) := by
  dsimp only [moduleFaceInclusion]
  rw [Category.assoc, ι_cupLift, locallyWeightedHom_precomp]
  congr 1
  exact moduleMap_comp_faceInclusion (homOfLE h) _ _

/-- Deleting a vertex after the first two preserves the first edge scalar. -/
theorem firstTransition_delete_late (k : ℕ) (s : Face (n + 1) (k + 2))
    (i : Fin (k + 1)) :
    restrictScalar (X := TopCat.of (U A n)) (homOfLE (faceOpen_le_delete chartOpen s i.succ.succ))
      (firstTransition (A := A) k (deleteFace s i.succ.succ)) = firstTransition (A := A) (k + 1) s := by
  apply LocallyConstant.ext
  intro q
  change quotientPairParity (s (i.succ.succ.succAbove 0))
      (s (i.succ.succ.succAbove 1)) q.val.val = quotientPairParity (s 0) (s 1) q.val.val
  have h0 : i.succ.succ.succAbove (0 : Fin (k + 2)) = 0 := by simp
  have h1 : i.succ.succ.succAbove (1 : Fin (k + 2)) = 1 := by
    change i.succ.succ.succAbove (0 : Fin (k + 1)).succ = _
    simp
  rw [h0, h1]

/-- The two leading deletion terms combine by the transition cocycle identity. -/
theorem firstTransition_delete_pair (k : ℕ) (s : Face (n + 1) (k + 2)) :
    restrictScalar (X := TopCat.of (U A n)) (homOfLE (faceOpen_le_delete chartOpen s 0))
        (firstTransition (A := A) k (deleteFace s 0)) +
      restrictScalar (X := TopCat.of (U A n)) (homOfLE (faceOpen_le_delete chartOpen s 1))
        (firstTransition (A := A) k (deleteFace s 1)) = firstTransition (A := A) (k + 1) s := by
  apply LocallyConstant.ext
  intro q
  change quotientPairParity (s 1) (s 2) q.val.val +
      quotientPairParity (s 0) (s 2) q.val.val = quotientPairParity (s 0) (s 1) q.val.val
  rw [← quotientPairParity_cocycle (s 0) (s 1) (s 2) q.val
    ((iInf_le (fun j => chartOpen (s j)) 0) q.property)
    ((iInf_le (fun j => chartOpen (s j)) 1) q.property)
    ((iInf_le (fun j => chartOpen (s j)) 2) q.property)]
  rw [add_left_comm, self_add, add_zero]

@[reassoc] theorem ι_moduleDifferential (k : ℕ) (s : Face (n + 1) (k + 1)) :
    Sigma.ι (fun t : Face (n + 1) (k + 1) =>
      freeOpenModule F (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫
        orderedDifferential chartOpen (freeOpenModuleFunctor F (TopCat.of (U A n))) k =
      ∑ i : Fin (k + 2), moduleFaceInclusion (faceOpen chartOpen s) (deleteFace s i)
        (faceOpen_le_delete chartOpen s i) := by
  rw [moduleDifferential_eq_sum, comp_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [orderedFace, Sigma.ι_desc]
  rfl

/-- The Alexander–Whitney lift commutes with the differential in characteristic two. -/
theorem cupLift_chain (k : ℕ) :
    orderedDifferential (chartOpen (A := A) (n := n))
        (freeOpenModuleFunctor F (TopCat.of (U A n))) (k + 1) ≫ cupLift k =
      cupLift (k + 1) ≫ orderedDifferential chartOpen
        (freeOpenModuleFunctor F (TopCat.of (U A n))) k := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, ← Category.assoc]
  erw [ι_moduleDifferential, ι_cupLift]
  rw [sum_comp, locallyWeightedHom_postcomp]
  change (∑ i : Fin (k + 3),
      moduleFaceInclusion (faceOpen chartOpen s) (deleteFace s i) _ ≫ cupLift k) =
    locallyWeightedHom (firstTransition (A := A) (k + 1) s)
      (moduleFaceInclusion (faceOpen chartOpen s) (deleteFace s 0) _ ≫ _)
  simp_rw [moduleFaceInclusion_comp_lift]
  rw [moduleDifferential_eq_sum, comp_sum, locallyWeightedHom_sum]
  simp_rw [moduleFaceInclusion_comp_face]
  conv_lhs => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ← add_assoc]
  conv_rhs => rw [Fin.sum_univ_succ]
  apply congrArg₂ (· + ·)
  · have he : deleteFace (deleteFace s (1 : Fin (k + 3))) 0 =
        deleteFace (deleteFace s 0) 0 := by
      exact deleteFace_deleteFace s 0 0 (by simp)
    have hm := moduleFaceInclusion_congr (A := A) (V := faceOpen chartOpen s) he
      ((faceOpen_le_delete chartOpen s 1).trans (faceOpen_le_delete chartOpen (deleteFace s 1) 0))
      ((faceOpen_le_delete chartOpen s 0).trans (faceOpen_le_delete chartOpen (deleteFace s 0) 0))
    erw [hm]
    rw [← locallyWeightedHom_add_scalar]
    congr 1
    exact firstTransition_delete_pair (A := A) k s
  · apply Finset.sum_congr rfl
    intro i _
    rw [firstTransition_delete_late]
    congr 1
    exact moduleFaceInclusion_congr
      (deleteFace_deleteFace s 0 i.succ (by simp)) _ _

/-- The usual signed degree-one chain-lift identity. -/
theorem cupLift_chain_signed (k : ℕ) :
    orderedDifferential (chartOpen (A := A) (n := n))
        (freeOpenModuleFunctor F (TopCat.of (U A n))) (k + 1) ≫ cupLift k =
      -(cupLift (k + 1) ≫ orderedDifferential chartOpen
        (freeOpenModuleFunctor F (TopCat.of (U A n))) k) := by
  rw [moduleSheaf_neg_eq_self, cupLift_chain]

/-- Iterating the lift and then augmenting. -/
def cupIterate : (k : ℕ) →
    orderedTerm (chartOpen (A := A) (n := n))
      (freeOpenModuleFunctor F (TopCat.of (U A n))) k ⟶
      freeOpenModule F (X := TopCat.of (U A n)) ⊤
  | 0 => orderedAugmentation chartOpen (freeOpenModuleFunctor F (TopCat.of (U A n)))
  | k + 1 => cupLift k ≫ cupIterate k

theorem powerTransition_apply (k : ℕ) (s : Face (n + 1) k)
    (q : faceOpen (chartOpen (A := A)) s) :
    powerTransition k s q =
      ∏ j : Fin k, quotientPairParity (s j.castSucc) (s j.succ) q.val.val :=
  map_prod (LocallyConstant.evalMonoidHom q) _ _

/-- The adjacent-edge product separates into its first edge and the tail product. -/
theorem powerTransition_succ (k : ℕ) (s : Face (n + 1) (k + 1)) :
    powerTransition (A := A) (k + 1) s = firstTransition (A := A) k s *
      restrictScalar (X := TopCat.of (U A n))
        (homOfLE (faceOpen_le_delete chartOpen s 0)) (powerTransition k (deleteFace s 0)) := by
  apply LocallyConstant.ext
  intro q
  change powerTransition (k + 1) s q = quotientPairParity (s 0) (s 1) q.val.val *
    powerTransition k (deleteFace s 0) ⟨q.val, _⟩
  rw [powerTransition_apply, powerTransition_apply, Fin.prod_univ_succ]
  congr 1

/-- Each iterated lift has exactly the expected product of transition scalars. -/
theorem ι_cupIterate (k : ℕ) (s : Face (n + 1) k) :
    Sigma.ι (fun t : Face (n + 1) k =>
      freeOpenModule F (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫ cupIterate k =
      locallyWeightedHom (powerTransition (A := A) k s)
        (freeOpenModuleMap F (X := TopCat.of (U A n)) (homOfLE le_top)) := by
  induction k with
  | zero =>
    simp only [cupIterate, orderedAugmentation, Sigma.ι_desc, powerTransition,
      Finset.univ_eq_empty, Finset.prod_empty, locallyWeightedHom_one]
    rfl
  | succ k ih =>
    rw [cupIterate, ← Category.assoc, ι_cupLift, locallyWeightedHom_postcomp]
    rw [Category.assoc, ih, locallyWeightedHom_precomp, ← locallyWeightedHom_mul,
      ← powerTransition_succ]
    congr 1
    change (freeOpenModuleFunctor F (TopCat.of (U A n))).map _ ≫
        (freeOpenModuleFunctor F (TopCat.of (U A n))).map _ = _
    rw [← Functor.map_comp]
    rfl

/-- Every iterated cup cochain is closed. -/
theorem cupIterate_cocycle (k : ℕ) :
    orderedDifferential (chartOpen (A := A) (n := n))
        (freeOpenModuleFunctor F (TopCat.of (U A n))) k ≫ cupIterate k = 0 := by
  induction k with
  | zero => exact orderedDifferential_comp_augmentation chartOpen _
  | succ k ih =>
    rw [cupIterate, ← Category.assoc, cupLift_chain, Category.assoc, ih, comp_zero]

end Aoki.Cech
