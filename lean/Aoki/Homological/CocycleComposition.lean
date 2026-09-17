import Aoki.Homological.ExtComposition

/-! # Composition of arbitrary-degree cocycles and shifted morphisms -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex CochainComplex.HomComplex
namespace Aoki.Homological
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L M : CochainComplex C ℤ}

/-- The usual composition of cochains preserves cocycles in arbitrary degrees. -/
def cocycleComp {a b c : ℤ} (z : Cocycle K L a) (w : Cocycle L M b) (h : a + b = c) :
    Cocycle K M c :=
  Cocycle.mk ((z : Cochain K L a).comp w h) (c + 1) rfl (by
    rw [δ_comp _ _ h (a + 1) (b + 1) (c + 1) rfl rfl rfl]
    simp)

/-- Passing from cocycles to shifted morphisms respects composition. -/
theorem cocycleComp_equivHomShift {a b c : ℤ} (z : Cocycle K L a) (w : Cocycle L M b)
    (h : a + b = c) :
    Cocycle.equivHomShift.symm (cocycleComp z w h) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm z) (Cocycle.equivHomShift.symm w) (by omega) := by
  ext p
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cocycle.rightShift_coe,
    Cochain.rightShift_v _ _ _ _ p p (add_zero p) (p + c) rfl,
    Cocycle.mk_coe, cocycleComp, Cochain.comp_v _ _ h p (p + a) (p + c) rfl (by omega),
    ShiftedHom.comp, HomologicalComplex.comp_f, shiftFunctor_map_f',
    shiftFunctorAdd'_inv_app_f']
  rw [Cochain.rightShift_v _ _ _ _ p p (add_zero p) (p + a) rfl,
    Cochain.rightShift_v _ _ _ _ (p + a) (p + a) (add_zero _) (p + c) (by omega)]
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, Category.assoc]

end Aoki.Homological
