import Aoki.Homological.ResolutionCochain
import Aoki.Homological.CocycleComposition

/-! # Yoneda products from componentwise chain lifts -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace Aoki.Homological
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {X Y Z : C} (R : ProjectiveResolution X) (S : ProjectiveResolution Y)

def resolutionSingleCocycle {n : ℕ} (f : R.complex.X n ⟶ Y)
    (hf : R.complex.d (n+1) n ≫ f = 0) :
    Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) (n : ℤ) :=
  Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
    (-(n+1 : ℕ)) (by omega)
    (by
      rw [R.cochainComplex_d (-((n+1 : ℕ):ℤ)) (-n) (n+1) n rfl rfl]
      simp [hf])

def resolutionSingleHom {n : ℕ} (f : R.complex.X n ⟶ Y)
    (hf : R.complex.d (n+1) n ≫ f = 0) :
    ShiftedHom R.cochainComplex ((singleFunctor C 0).obj Y) (n : ℤ) :=
  Cocycle.equivHomShift.symm (resolutionSingleCocycle R f hf)

@[simp] theorem extOfShiftedHom_resolutionSingleHom {n : ℕ} (f : R.complex.X n ⟶ Y)
    (hf : R.complex.d (n+1) n ≫ f = 0) :
    extOfShiftedHom R (resolutionSingleHom R f hf) = R.extMk f (n+1) rfl hf := by
  simp only [extOfShiftedHom, resolutionSingleHom, AddEquiv.apply_symm_apply]
  rfl

/-- Equality of cocycle representatives gives equality of their Ext classes,
without unfolding the projective-resolution comparison. -/
theorem extMk_congr {n : ℕ} (f g : R.complex.X n ⟶ Y) (h : f = g)
    (hf : R.complex.d (n+1) n ≫ f = 0) (hg : R.complex.d (n+1) n ≫ g = 0) :
    R.extMk f (n+1) rfl hf = R.extMk g (n+1) rfl hg := by
  subst g
  rfl

variable (L : ∀ k, R.complex.X (k+1) ⟶ S.complex.X k)
variable (hL : ∀ k, L (k+1) ≫ S.complex.d (k+1) k +
  R.complex.d (k+2) (k+1) ≫ L k = 0)

include hL in
omit [HasExt C] in
theorem lift_one_closed : R.complex.d 2 1 ≫ (L 0 ≫ S.π.f 0) = 0 := by
  have hh := congrArg (fun f => f ≫ S.π.f 0) (hL 0)
  simpa only [add_comp, Category.assoc, S.complex_d_comp_π_f_zero,
    comp_zero, zero_add, zero_comp] using hh

omit [HasExt C] in
theorem resolutionCocycleOne_postcomp :
    (resolutionCocycleOne R S L hL).postcomp S.π' =
      resolutionSingleCocycle R (Y := Y) (L 0 ≫ S.π.f 0) (lift_one_closed R S L hL) := by
  ext : 1
  apply (Cochain.toSingleEquiv (show (-1 : ℤ) + 1 = 0 by omega)).injective
  change (((resolutionCocycleOne R S L hL).postcomp S.π' :
      Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) 1) :
      Cochain R.cochainComplex ((singleFunctor C 0).obj Y) 1).v (-1) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom =
    ((resolutionSingleCocycle R (Y := Y) (L 0 ≫ S.π.f 0) (lift_one_closed R S L hL) :
      Cochain R.cochainComplex ((singleFunctor C 0).obj Y) 1).v (-1) 0 (by omega)) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom
  simp only [Cocycle.postcomp, Cocycle.mk_coe, resolutionCocycleOne,
    Cochain.comp_v _ _ (add_zero (1:ℤ)) (-1) 0 0 (by omega) rfl,
    Cochain.ofHom_v, resolutionSingleCocycle, Cocycle.toSingleMk_coe,
    Category.assoc]
  rw [resolutionCochainOne_v' R S L (-1) 0 0 (by omega) rfl, S.π'_f_zero]
  simp

omit [HasExt C] in
theorem resolutionLiftOne_lifts :
    ShiftedHom.comp (resolutionLiftOne R S L hL)
      (ShiftedHom.mk₀ (0 : ℤ) rfl S.π') (zero_add _) =
      resolutionSingleHom R (Y := Y) (L 0 ≫ S.π.f 0) (lift_one_closed R S L hL) := by
  rw [ShiftedHom.comp_mk₀]
  change Cocycle.equivHomShift.symm (resolutionCocycleOne R S L hL) ≫ S.π'⟦(1:ℤ)⟧' = _
  rw [← Cocycle.equivHomShift_symm_postcomp, resolutionCocycleOne_postcomp]
  rfl

include hL in
omit [HasExt C] in
theorem lift_comp_closed {n : ℕ} (f : S.complex.X n ⟶ Z)
    (hf : S.complex.d (n+1) n ≫ f = 0) :
    R.complex.d (n+1+1) (n+1) ≫ (L n ≫ f) = 0 := by
  have hh := congrArg (fun g => g ≫ f) (hL n)
  simpa only [add_comp, Category.assoc, hf, comp_zero, zero_add, zero_comp] using hh

omit [HasExt C] in
theorem resolutionCocycleOne_comp {n : ℕ} (f : S.complex.X n ⟶ Z)
    (hf : S.complex.d (n+1) n ≫ f = 0) :
    cocycleComp (resolutionCocycleOne R S L hL) (resolutionSingleCocycle S f hf)
      (show (1:ℤ) + n = (n+1:ℕ) by omega) =
    resolutionSingleCocycle R (L n ≫ f) (lift_comp_closed R S L hL f hf) := by
  ext : 1
  apply (Cochain.toSingleEquiv (show (-((n+1:ℕ):ℤ)) + (n+1:ℕ) = 0 by omega)).injective
  change ((cocycleComp (resolutionCocycleOne R S L hL) (resolutionSingleCocycle S f hf)
      (show (1:ℤ) + n = (n+1:ℕ) by omega) :
      Cochain R.cochainComplex ((singleFunctor C 0).obj Z) (n+1:ℕ)).v
      (-((n+1:ℕ):ℤ)) 0 (by omega)) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).hom =
    ((resolutionSingleCocycle R (L n ≫ f) (lift_comp_closed R S L hL f hf) :
      Cochain R.cochainComplex ((singleFunctor C 0).obj Z) (n+1:ℕ)).v
      (-((n+1:ℕ):ℤ)) 0 (by omega)) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Z).hom
  simp only [cocycleComp, Cocycle.mk_coe, resolutionCocycleOne,
    resolutionSingleCocycle, Cocycle.toSingleMk_coe,
    Cochain.comp_v _ _ (show (1:ℤ) + n = (n+1:ℕ) by omega)
      (-((n+1:ℕ):ℤ)) (-n) 0 (by omega) (by omega),
    resolutionCochainOne_v, Cochain.toSingleMk_v, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual positive Yoneda product, computed by a signed degree-one chain lift. -/
theorem extMk_comp_of_lift {n : ℕ} (f : S.complex.X n ⟶ Z)
    (hf : S.complex.d (n+1) n ≫ f = 0) :
    (R.extMk (L 0 ≫ S.π.f 0) 2 rfl (lift_one_closed R S L hL)).comp
      (S.extMk f (n+1) rfl hf) (show 1+n=n+1 by omega) =
    R.extMk (L n ≫ f) (n+1+1) rfl (lift_comp_closed R S L hL f hf) := by
  rw [← extOfShiftedHom_resolutionSingleHom, ← extOfShiftedHom_resolutionSingleHom]
  rw [extOfShiftedHom_comp R S (show 1+n=n+1 by omega) _ _
    (resolutionLiftOne R S L hL) (resolutionLiftOne_lifts R S L hL)]
  change extOfShiftedHom R
    (ShiftedHom.comp (Cocycle.equivHomShift.symm (resolutionCocycleOne R S L hL))
      (Cocycle.equivHomShift.symm (resolutionSingleCocycle S f hf)) _) = _
  rw [← cocycleComp_equivHomShift _ _ (show (1:ℤ) + n = (n+1:ℕ) by omega),
    resolutionCocycleOne_comp]
  exact extOfShiftedHom_resolutionSingleHom R _ _

end Aoki.Homological
