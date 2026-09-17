import Aoki.Cech.BoundaryObstruction
import Aoki.Cech.Cocycle

/-! # Evaluating actual ordered Čech cochains on all-finite configurations -/

noncomputable section

namespace Aoki.Cech

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace Geometry

set_option backward.isDefEq.respectTransparency false

variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

def fullFaceLift {k : ℕ} (s : Face (n + 1) k) (x : Config A n) :
    faceOpen (chartOpen (A := A)) s :=
  ⟨fullOrbit x, (mem_finite_iInf_opens _ _).mpr (fun j => fullOrbit_mem_chart x (s j))⟩

/-- Evaluate a represented constant-sheaf section as a field-valued function. -/
def sectionValue (W : Opens (U A n)) (q : W) :
    (freeOpen (X := TopCat.of (U A n)) W ⟶ constantF2Sheaf) →+ F :=
  (LocallyConstant.evalRingHom q).toAddMonoidHom.comp
    ((constantSheafSectionAddEquiv (TopCat.of (U A n)) F W).toAddMonoidHom.comp
      (freeOpenHomAddEquiv W constantF2Sheaf).toAddMonoidHom)

omit [∀ i, DiscreteTopology (A i)] in
theorem sectionValue_restrict {V W : Opens (U A n)} (i : V ⟶ W)
    (f : freeOpen (X := TopCat.of (U A n)) W ⟶ constantF2Sheaf) (q : V) :
    sectionValue V q (freeOpenMap i ≫ f) =
      sectionValue W ⟨q.val, (leOfHom i) q.property⟩ f := by
  change constantSheafSectionAddEquiv (TopCat.of (U A n)) F V
    (freeOpenHomEquiv V constantF2Sheaf (freeOpenMap i ≫ f)) q = _
  rw [freeOpenHomEquiv_restrict]
  exact constantSheafSectionAddEquiv_restrict (TopCat.of (U A n)) F i _ q

/-- Restrict a cochain to a face and evaluate it at an all-finite configuration. -/
def cochainValue {k : ℕ} (s : Face (n + 1) k) (x : Config A n) :
    (orderedTerm (chartOpen (A := A)) (freeOpenFunctor (TopCat.of (U A n))) k ⟶
      constantF2Sheaf) →+ F where
  toFun f := sectionValue (faceOpen chartOpen s) (fullFaceLift s x)
    (Sigma.ι (fun t : Face (n + 1) k => (freeOpenFunctor (TopCat.of (U A n))).obj
      (faceOpen chartOpen t)) s ≫ f)
  map_zero' := by simp
  map_add' f g := by simp [comp_add]

theorem cochainValue_face {k : ℕ} (s : Face (n + 1) (k + 1)) (x : Config A n)
    (i : Fin (k + 2))
    (f : orderedTerm (chartOpen (A := A)) (freeOpenFunctor (TopCat.of (U A n))) k ⟶
      constantF2Sheaf) :
    cochainValue s x (orderedFace chartOpen (freeOpenFunctor (TopCat.of (U A n))) k i ≫ f) =
      cochainValue (deleteFace s i) x f := by
  dsimp only [cochainValue, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  have h := ι_orderedFace_assoc (chartOpen (A := A))
    (freeOpenFunctor (TopCat.of (U A n))) k i s f
  exact (congrArg (sectionValue (faceOpen chartOpen s) (fullFaceLift s x)) h).trans
    (sectionValue_restrict _ _ _)

theorem neg_one_pow_smul_f2 (k : ℕ) (a : F) : (-1 : ℤ) ^ k • a = a := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, neg_one_zsmul, ZMod.neg_eq_self_mod_two, ih]

/-- In characteristic two the alternating differential evaluates as the sum
of restrictions to all deleted faces. -/
theorem cochainValue_differential {k : ℕ} (s : Face (n + 1) (k + 1)) (x : Config A n)
    (f : orderedTerm (chartOpen (A := A)) (freeOpenFunctor (TopCat.of (U A n))) k ⟶
      constantF2Sheaf) :
    cochainValue s x (orderedDifferential chartOpen (freeOpenFunctor (TopCat.of (U A n))) k ≫ f) =
      ∑ i : Fin (k + 2), cochainValue (deleteFace s i) x f := by
  simp only [orderedDifferential, alternatingDifferential, sum_comp, zsmul_comp,
    map_sum, map_zsmul, neg_one_pow_smul_f2, cochainValue_face]

/-- The unique full face of the finite cover. -/
def topFace (n : ℕ) : Face (n + 1) n where
  toFun := id
  inj' := Function.injective_id
  map_rel_iff' := Iff.rfl

@[simp] theorem topFace_apply (n : ℕ) (i : Fin (n + 1)) : topFace n i = i := rfl

theorem deletedOpen_le_topFace_delete (i : Fin (n + 2)) :
    deletedOpen (A := A) i ≤ faceOpen chartOpen (deleteFace (topFace (n + 1)) i) := by
  intro q hq
  apply (mem_finite_iInf_opens _ _).mpr
  intro j
  exact (mem_deletedOpen i q).mp hq (i.succAbove j) (i.succAbove_ne j)

/-- A lower cochain supplies an actual continuous section on each
deleted-face intersection. -/
def deletedCochainFunction
    (g : orderedTerm (chartOpen (A := A) (n := n + 1))
      (freeOpenFunctor (TopCat.of (U A (n + 1)))) n ⟶ constantF2Sheaf)
    (i : Fin (n + 2)) : C(deletedOpen (A := A) i, F) :=
  (constantSheafSectionAddEquiv (TopCat.of (U A (n + 1))) F (deletedOpen i)
    (freeOpenHomEquiv (deletedOpen i) constantF2Sheaf
      (freeOpenMap (homOfLE (deletedOpen_le_topFace_delete i)) ≫
        Sigma.ι (fun t : Face (n + 2) n => freeOpen (X := TopCat.of (U A (n + 1)))
          (faceOpen chartOpen t)) (deleteFace (topFace (n + 1)) i) ≫ g))).toContinuousMap

theorem deletedCochainFunction_eval
    (g : orderedTerm (chartOpen (A := A) (n := n + 1))
      (freeOpenFunctor (TopCat.of (U A (n + 1)))) n ⟶ constantF2Sheaf)
    (i : Fin (n + 2)) (x : Config A (n + 1)) :
    deletedCochainFunction g i (fullLift i x) =
      cochainValue (deleteFace (topFace (n + 1)) i) x g := by
  change sectionValue (deletedOpen i) (fullLift i x) (freeOpenMap _ ≫ _) = _
  exact sectionValue_restrict _ _ _

/-- An actual top-degree ordered Čech cochain with alternating values is not
a coboundary. The coefficients here are the actual constant F₂ sheaf. -/
theorem aleph_top_cochain_not_boundary (n : ℕ)
    (f : orderedTerm (chartOpen (A := AlephBase) (n := n + 1))
      (freeOpenFunctor (TopCat.of (U AlephBase (n + 1)))) (n + 1) ⟶ constantF2Sheaf)
    (hf : ∀ x : Config AlephBase (n + 1),
      cochainValue (topFace (n + 1)) x f = alternating (n + 1) x) :
    ¬ ∃ g : orderedTerm (chartOpen (A := AlephBase) (n := n + 1))
        (freeOpenFunctor (TopCat.of (U AlephBase (n + 1)))) n ⟶ constantF2Sheaf,
      orderedDifferential chartOpen (freeOpenFunctor (TopCat.of (U AlephBase (n + 1)))) n ≫ g = f := by
  rintro ⟨g, hg⟩
  apply aleph_no_continuous_deleted_decomposition (n + 1) (by omega)
  refine ⟨deletedCochainFunction g, ?_⟩
  intro x
  rw [← hf x, ← hg, cochainValue_differential]
  apply Finset.sum_congr rfl
  intro i _
  exact (deletedCochainFunction_eval g i x).symm

/-- The actual top cochain evaluates to the already formalized alternating
function, with no change of the coordinate convention. -/
theorem powerCochain_top_value (x : Config A n) :
    cochainValue (topFace n) x (powerCochain n) = alternating n x := by
  apply Eq.trans _ (alternating_eq_tuple_product n x).symm
  exact powerCochain_face_eval_finite n (topFace n) (fullFaceLift (topFace n) x)
    (fullPoint x) (configEquivTuple n x) rfl (fun _ => rfl)

/-- The concrete alternating-product top cochain is not a coboundary. -/
theorem aleph_powerCochain_not_boundary (n : ℕ) :
    ¬ ∃ g : orderedTerm (chartOpen (A := AlephBase) (n := n + 1))
        (freeOpenFunctor (TopCat.of (U AlephBase (n + 1)))) n ⟶ constantF2Sheaf,
      orderedDifferential chartOpen (freeOpenFunctor (TopCat.of (U AlephBase (n + 1)))) n ≫ g =
        powerCochain (n + 1) :=
  aleph_top_cochain_not_boundary n (powerCochain (n + 1)) powerCochain_top_value

/-- In the top degree every cochain is closed because the next term is zero. -/
theorem powerCochain_top_cocycle :
    orderedDifferential (chartOpen (A := A) (n := n))
      (freeOpenFunctor (TopCat.of (U A n))) n ≫ powerCochain n = 0 :=
  (orderedTerm_isZero (chartOpen (A := A)) (freeOpenFunctor (TopCat.of (U A n)))
    (k := n + 1) le_rfl).eq_of_src _ _

end Aoki.Cech
