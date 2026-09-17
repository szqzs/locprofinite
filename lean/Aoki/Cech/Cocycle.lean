import Aoki.Sheaf.ChartProjectivity
import Aoki.Sheaf.LocallyConstant
import Mathlib.Topology.Instances.ZMod

/-!
# The actual degree-one cocycle on the quotient charts

The transition functions are the sums of the two finite-coordinate bits.
They descend to the orbit space, are locally constant on chart intersections,
and satisfy the cocycle identity. The coefficient sheaf is mathlib's constant
abelian sheaf, identified explicitly with locally constant functions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Aoki.Cech

open CategoryTheory TopologicalSpace Opposite Geometry

variable {A : ℕ → Type} {n : ℕ}

/-- Pair parity on the compact product, with a harmless zero value outside
the two finite-coordinate charts. -/
def pairParity (i j : Fin (n + 1)) (x : CompactProduct A n) : F :=
  (x i).elim 0 (fun a => (x j).elim 0 (fun b => bit a.2 + bit b.2))

theorem pairParity_flip (i j : Fin (n + 1)) (x : CompactProduct A n) :
    pairParity i j (Geometry.flip x) = pairParity i j x := by
  cases hi : x i <;> cases hj : x j <;>
    simp [pairParity, Geometry.flip, hi, hj, coordinateFlip, bit_not,
      add_add_add_comm]

theorem pairParity_of_finite (i j : Fin (n + 1)) (x : CompactProduct A n)
    (a : A i × Bool) (b : A j × Bool) (hi : x i = ↑a) (hj : x j = ↑b) :
    pairParity i j x = bit a.2 + bit b.2 := by
  simp [pairParity, hi, hj]

theorem pairParity_eq_of_quotientMap_eq (i j : Fin (n + 1))
    {x y : CompactProduct A n} (h : quotientMap x = quotientMap y) :
    pairParity i j x = pairParity i j y := by
  rcases (quotientMap_eq_iff x y).mp h with rfl | rfl
  · rfl
  · exact pairParity_flip i j y

/-- The parity function on the genuine orbit quotient. -/
def quotientPairParity (i j : Fin (n + 1)) : CompactQuotient A n → F :=
  Quotient.lift (pairParity i j)
    (fun _ _ h => pairParity_eq_of_quotientMap_eq i j (Quotient.sound h))

@[simp] theorem quotientPairParity_mk (i j : Fin (n + 1)) (x : CompactProduct A n) :
    quotientPairParity i j (quotientMap x) = pairParity i j x := rfl

/-- On each compact-open gauge cell the transition function is constant. -/
theorem quotientPairParity_on_cell {I : Finset (Fin (n + 1))}
    {g : Fin (n + 1)} {hg : g ∈ I} (v : GaugeLabel (A := A) I g hg)
    (i j : Fin (n + 1)) (hi : i ∈ I) (hj : j ∈ I)
    {q : U A n} (hq : q ∈ cell v) :
    quotientPairParity i j q.val = bit (v.val ⟨i, hi⟩).2 + bit (v.val ⟨j, hj⟩).2 := by
  obtain ⟨x, hx, hq⟩ := hq
  rw [← hq, quotientPairParity_mk]
  exact pairParity_of_finite i j x _ _ (hx ⟨i, hi⟩) (hx ⟨j, hj⟩)

section Topology

variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- Restricting pair parity to any open lying in both charts is locally constant. -/
def transitionOnOpen (W : Opens (U A n)) (i j : Fin (n + 1))
    (hi : W ≤ chartOpen i) (hj : W ≤ chartOpen j) : LocallyConstant W F where
  toFun q := quotientPairParity i j q.val.val
  isLocallyConstant := by
    classical
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro q
    let I : Finset (Fin (n + 1)) := {i, j}
    have hq : ∀ k ∈ I, q.val ∈ chart k := by
      intro k hk
      simp only [I, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi q.property
      · exact hj q.property
    obtain ⟨v, hv⟩ := (exists_quotientCell_iff I i (by simp [I]) q.val.val).mpr hq
    let S : Set W := Subtype.val ⁻¹' cell v
    refine ⟨S, (isClopen_cell v).isOpen.preimage continuous_subtype_val, hv, ?_⟩
    intro q' hq'
    exact (quotientPairParity_on_cell v i j (by simp [I]) (by simp [I]) hq').trans
      (quotientPairParity_on_cell v i j (by simp [I]) (by simp [I]) hv).symm

@[simp] theorem transitionOnOpen_apply (W : Opens (U A n)) (i j : Fin (n + 1))
    (hi : W ≤ chartOpen i) (hj : W ≤ chartOpen j) (q : W) :
    transitionOnOpen W i j hi hj q = quotientPairParity i j q.val.val := rfl

omit [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)] in
/-- The transition identity on every triple intersection. -/
theorem quotientPairParity_cocycle (i j k : Fin (n + 1)) (q : U A n)
    (hi : q ∈ chart i) (hj : q ∈ chart j) (hk : q ∈ chart k) :
    quotientPairParity i j q.val + quotientPairParity j k q.val =
      quotientPairParity i k q.val := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.val
  change quotientMap x = q.val at hx
  have hxi : x i ≠ OnePoint.infty :=
    (quotientMap_mem_finiteCoordinate_image_iff x i).mp (hx.symm ▸ hi)
  have hxj : x j ≠ OnePoint.infty :=
    (quotientMap_mem_finiteCoordinate_image_iff x j).mp (hx.symm ▸ hj)
  have hxk : x k ≠ OnePoint.infty :=
    (quotientMap_mem_finiteCoordinate_image_iff x k).mp (hx.symm ▸ hk)
  obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp hxi
  obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.mp hxj
  obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hxk
  rw [← hx, quotientPairParity_mk, quotientPairParity_mk, quotientPairParity_mk,
    pairParity_of_finite i j x a b ha.symm hb.symm,
    pairParity_of_finite j k x b c hb.symm hc.symm,
    pairParity_of_finite i k x a c ha.symm hc.symm]
  rw [add_assoc, ← add_assoc (bit b.2), self_add, zero_add]

/-- The coefficient object is the actual constant abelian sheaf with values F₂. -/
def constantF2Sheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of (U A n)) :=
  (constantSheaf (Opens.grothendieckTopology (U A n)) AddCommGrpCat).obj
    (AddCommGrpCat.of F)

/-- A transition function as a section of the actual constant sheaf. -/
def transitionSection (W : Opens (U A n)) (i j : Fin (n + 1))
    (hi : W ≤ chartOpen i) (hj : W ≤ chartOpen j) :
    (constantF2Sheaf (A := A) (n := n)).obj.obj (op W) :=
  (constantSheafSectionAddEquiv (TopCat.of (U A n)) F W).symm
    (transitionOnOpen W i j hi hj)

/-- The section represented as a morphism from the free sheaf on its open. -/
def transitionHom (W : Opens (U A n)) (i j : Fin (n + 1))
    (hi : W ≤ chartOpen i) (hj : W ≤ chartOpen j) :
    freeOpen (X := TopCat.of (U A n)) W ⟶ constantF2Sheaf :=
  (freeOpenHomEquiv W constantF2Sheaf).symm (transitionSection W i j hi hj)

/-- Restriction of the represented section has the expected quotient-function value. -/
theorem transitionHom_restrict_eval {V W : Opens (U A n)} (ι : V ⟶ W)
    (i j : Fin (n + 1)) (hi : W ≤ chartOpen i) (hj : W ≤ chartOpen j) (q : V) :
    constantSheafSectionAddEquiv (TopCat.of (U A n)) F V
      (freeOpenHomEquiv V constantF2Sheaf
        (freeOpenMap ι ≫ transitionHom W i j hi hj)) q =
      quotientPairParity i j q.val.val := by
  rw [freeOpenHomEquiv_restrict]
  dsimp only [constantF2Sheaf]
  erw [constantSheafSectionAddEquiv_restrict]
  simp [transitionHom, transitionSection, constantF2Sheaf]

/-- The transition section associated with an increasing edge of the cover. -/
def edgeTransitionHom (s : Face (n + 1) 1) :
    freeOpen (X := TopCat.of (U A n)) (faceOpen chartOpen s) ⟶ constantF2Sheaf :=
  transitionHom (faceOpen chartOpen s) (s 0) (s 1)
    (iInf_le _ 0) (iInf_le _ 1)

/-- The degree-one ordered Čech cochain determined by the quotient torsor. -/
def transitionCochain :
    orderedTerm (chartOpen (A := A) (n := n)) (freeOpenFunctor (TopCat.of (U A n))) 1 ⟶
      constantF2Sheaf :=
  Limits.Sigma.desc edgeTransitionHom

@[reassoc, simp] theorem ι_transitionCochain (s : Face (n + 1) 1) :
    Limits.Sigma.ι (fun t : Face (n + 1) 1 =>
        freeOpen (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫
      transitionCochain = edgeTransitionHom (A := A) s :=
  Limits.Sigma.ι_desc _ _

/-- The transition cochain is closed for the actual ordered Čech differential. -/
theorem transitionCochain_cocycle :
    orderedDifferential (chartOpen (A := A) (n := n))
        (freeOpenFunctor (TopCat.of (U A n))) 1 ≫ transitionCochain = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  dsimp only [orderedDifferential, alternatingDifferential]
  erw [Fin.sum_univ_three]
  simp only [
    CategoryTheory.Preadditive.add_comp, CategoryTheory.Preadditive.comp_add,
    CategoryTheory.Preadditive.zsmul_comp, CategoryTheory.Preadditive.comp_zsmul,
    ι_orderedFace_assoc, transitionCochain, Limits.Sigma.ι_desc,
    Limits.comp_zero]
  norm_num
  apply (freeOpenHomAddEquiv (faceOpen chartOpen s) constantF2Sheaf).injective
  apply (constantSheafSectionAddEquiv (TopCat.of (U A n)) F (faceOpen chartOpen s)).injective
  apply LocallyConstant.ext
  intro q
  simp only [map_add, map_neg, map_zero, LocallyConstant.add_apply, LocallyConstant.neg_apply,
    LocallyConstant.zero_apply]
  simp only [freeOpenHomAddEquiv, AddEquiv.coe_mk, edgeTransitionHom]
  erw [transitionHom_restrict_eval, transitionHom_restrict_eval, transitionHom_restrict_eval]
  change quotientPairParity (s 1) (s 2) q.val.val +
      -quotientPairParity (s 0) (s 2) q.val.val +
      quotientPairParity (s 0) (s 1) q.val.val = 0
  rw [← quotientPairParity_cocycle (s 0) (s 1) (s 2) q.val
    ((show faceOpen (chartOpen (A := A)) s ≤ chartOpen (s 0) from iInf_le _ 0) q.property)
    ((show faceOpen (chartOpen (A := A)) s ≤ chartOpen (s 1) from iInf_le _ 1) q.property)
    ((show faceOpen (chartOpen (A := A)) s ≤ chartOpen (s 2) from iInf_le _ 2) q.property)]
  abel

/-- The ordered product of consecutive transition functions on a face.
This is the usual Čech representative of a repeated degree-one cup product;
its comparison with a cohomological cup product is a separate step. -/
def powerTransition (k : ℕ) (s : Face (n + 1) k) :
    LocallyConstant (faceOpen (chartOpen (A := A)) s) F :=
  ∏ j : Fin k, transitionOnOpen (faceOpen chartOpen s) (s j.castSucc) (s j.succ)
    (iInf_le _ j.castSucc) (iInf_le _ j.succ)

/-- The face product as a morphism into the actual constant coefficient sheaf. -/
def powerTransitionHom (k : ℕ) (s : Face (n + 1) k) :
    freeOpen (X := TopCat.of (U A n)) (faceOpen chartOpen s) ⟶ constantF2Sheaf :=
  (freeOpenHomEquiv _ constantF2Sheaf).symm
    ((constantSheafSectionAddEquiv (TopCat.of (U A n)) F _).symm
      (powerTransition k s))

/-- The degree-`k` cochain given by products of adjacent transition functions. -/
def powerCochain (k : ℕ) :
    orderedTerm (chartOpen (A := A) (n := n)) (freeOpenFunctor (TopCat.of (U A n))) k ⟶
      constantF2Sheaf :=
  Limits.Sigma.desc (powerTransitionHom k)

@[reassoc, simp] theorem ι_powerCochain (k : ℕ) (s : Face (n + 1) k) :
    Limits.Sigma.ι (fun t : Face (n + 1) k =>
        freeOpen (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫
      powerCochain k = powerTransitionHom (A := A) k s :=
  Limits.Sigma.ι_desc _ _

/-- Explicit evaluation of a face of the product cochain. -/
theorem powerCochain_face_eval (k : ℕ) (s : Face (n + 1) k)
    (q : faceOpen (chartOpen (A := A)) s) :
    constantSheafSectionAddEquiv (TopCat.of (U A n)) F (faceOpen chartOpen s)
      (freeOpenHomEquiv _ constantF2Sheaf
        (Limits.Sigma.ι (fun t : Face (n + 1) k =>
          freeOpen (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫ powerCochain k)) q =
      ∏ j : Fin k, quotientPairParity (s j.castSucc) (s j.succ) q.val.val := by
  rw [ι_powerCochain]
  simp only [powerTransitionHom, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact map_prod (LocallyConstant.evalMonoidHom q) _ _

/-- On a chosen finite representative the product cochain is exactly the
product of adjacent bit differences used in the combinatorial proof. -/
theorem powerCochain_face_eval_finite (k : ℕ) (s : Face (n + 1) k)
    (q : faceOpen (chartOpen (A := A)) s) (x : CompactProduct A n)
    (a : (j : Fin (k + 1)) → A (s j) × Bool)
    (hq : quotientMap x = q.val.val) (ha : ∀ j, x (s j) = ↑(a j)) :
    constantSheafSectionAddEquiv (TopCat.of (U A n)) F (faceOpen chartOpen s)
      (freeOpenHomEquiv _ constantF2Sheaf
        (Limits.Sigma.ι (fun t : Face (n + 1) k =>
          freeOpen (X := TopCat.of (U A n)) (faceOpen chartOpen t)) s ≫ powerCochain k)) q =
      ∏ j : Fin k, (bit (a j.castSucc).2 + bit (a j.succ).2) := by
  rw [powerCochain_face_eval, ← hq]
  apply Finset.prod_congr rfl
  intro j _
  exact pairParity_of_finite _ _ x _ _ (ha j.castSucc) (ha j.succ)

end Topology

end Aoki.Cech
