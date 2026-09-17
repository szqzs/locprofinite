import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Repeated Yoneda products of a degree-one class -/

noncomputable section

namespace Aoki.Homological

open CategoryTheory CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X : C}

/-- Powers under the actual Yoneda product, with the identity in degree zero. -/
def yonedaPower (η : Ext X X 1) : (r : ℕ) → Ext X X r
  | 0 => Ext.mk₀ (𝟙 X)
  | r + 1 => η.comp (yonedaPower η r) (by omega)

@[simp] theorem yonedaPower_zero (η : Ext X X 1) :
    yonedaPower η 0 = Ext.mk₀ (𝟙 X) := rfl

@[simp] theorem yonedaPower_succ (η : Ext X X 1) (r : ℕ) :
    yonedaPower η (r + 1) = η.comp (yonedaPower η r) (by omega) := rfl

@[simp] theorem yonedaPower_one (η : Ext X X 1) : yonedaPower η 1 = η :=
  Ext.comp_mk₀_id η

end Aoki.Homological
