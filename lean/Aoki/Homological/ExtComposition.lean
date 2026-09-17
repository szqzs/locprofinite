import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Yoneda composition computed by a lift on a projective resolution

A positive-degree morphism on a projective resolution can be composed before
passing to Ext. The lifting condition below is an equality of actual cochain
complex morphisms, not an assumption about the desired Ext product.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace Aoki.Homological
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {X Y Z : C}

/-- A shifted cochain morphism out of a projective resolution defines an Ext class. -/
def extOfShiftedHom (R : ProjectiveResolution X) {n : ℕ}
    (f : ShiftedHom R.cochainComplex ((singleFunctor C 0).obj Y) (n : ℤ)) : Ext X Y n :=
  R.extEquivCohomologyClass.symm (.mk (Cocycle.equivHomShift f))

set_option backward.isDefEq.respectTransparency false in
/-- The derived-category morphism represented by the cochain map. -/
theorem extOfShiftedHom_hom [HasDerivedCategory C] (R : ProjectiveResolution X) {n : ℕ}
    (f : ShiftedHom R.cochainComplex ((singleFunctor C 0).obj Y) (n : ℤ)) :
    (extOfShiftedHom R f).hom =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (DerivedCategory.Q.map R.π'))).comp
        (ShiftedHom.map f DerivedCategory.Q) (add_zero _) := by
  rw [extOfShiftedHom, ProjectiveResolution.extEquivCohomologyClass_symm_mk_hom]
  simp only [AddEquiv.symm_apply_apply, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    ]
  erw [ShiftedHom.comp_mk₀_id]

section Shifted
variable {D : Type*} [Category* D] [HasShift D ℤ]
variable {A B A' B' T : D}

/-- Cancellation of the middle resolution in a product of shifted fractions. -/
theorem shifted_fraction_comp (p : A' ⟶ A) (q : B' ⟶ B) [IsIso p] [IsIso q]
    {a b c : ℤ} (h : b + a = c)
    (l : ShiftedHom A' B' a) (g : ShiftedHom B' T b) :
    ((ShiftedHom.mk₀ (0 : ℤ) rfl (inv p)).comp
      (l.comp (ShiftedHom.mk₀ 0 rfl q) (zero_add _)) (add_zero _)).comp
        ((ShiftedHom.mk₀ 0 rfl (inv q)).comp g (add_zero _)) h =
    (ShiftedHom.mk₀ 0 rfl (inv p)).comp (l.comp g h) (add_zero _) := by
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc]

end Shifted

set_option backward.isDefEq.respectTransparency false in
/-- Yoneda products are computed by composing with any actual lift to the second resolution. -/
theorem extOfShiftedHom_comp (R : ProjectiveResolution X) (S : ProjectiveResolution Y)
    {a b c : ℕ} (h : a + b = c)
    (f : ShiftedHom R.cochainComplex ((singleFunctor C 0).obj Y) (a : ℤ))
    (g : ShiftedHom S.cochainComplex ((singleFunctor C 0).obj Z) (b : ℤ))
    (lift : ShiftedHom R.cochainComplex S.cochainComplex (a : ℤ))
    (hlift : lift.comp (ShiftedHom.mk₀ (0 : ℤ) rfl S.π') (zero_add _) = f) :
    (extOfShiftedHom R f).comp (extOfShiftedHom S g) h =
      extOfShiftedHom R (lift.comp g (by omega)) := by
  have := HasDerivedCategory.standard C
  ext
  subst f
  simp only [Ext.comp_hom, extOfShiftedHom_hom, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  exact shifted_fraction_comp (DerivedCategory.Q.map R.π') (DerivedCategory.Q.map S.π')
    (by omega) (ShiftedHom.map lift DerivedCategory.Q) (ShiftedHom.map g DerivedCategory.Q)

end Aoki.Homological
