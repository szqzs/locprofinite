import Aoki.Cech.Cocycle
import Aoki.Cech.ModuleComparison
import Aoki.Sheaf.LocallyConstantScalar

/-! # Locally constant scalar multiplication under the coefficient comparison -/

noncomputable section

namespace Aoki

open CategoryTheory TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

variable {X : TopCat} (M : TopCat.Sheaf (ModuleCat F) X)

local notation "Mab" => ((sheafCompose (Opens.grothendieckTopology X)
  (forget₂ (ModuleCat F) AddCommGrpCat)).obj M)

local notation "F₂X" =>
  ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of F))

/-- An additive map out of an F₂ module respects its two scalar actions. -/
theorem additive_map_f2_smul {G : Type*} [AddCommGroup G] [Module F G]
    (e : G →+ F) (a : F) (s : G) : e (a • s) = a * e s := by
  fin_cases a <;> simp

/-- Evaluation after a coefficient morphism, as an additive map on sections. -/
def coefficientSectionValue (φ : Mab ⟶ F₂X)
    (W : Opens X) (x : W) : M.obj.obj (op W) →+ F :=
  ((LocallyConstant.evalRingHom x).toAddMonoidHom.comp
    (constantSheafSectionAddEquiv X F W).toAddMonoidHom).comp
      (φ.hom.app (op W)).hom

theorem coefficientSectionValue_restrict (φ : Mab ⟶ F₂X)
    {V W : Opens X} (i : V ⟶ W) (s : M.obj.obj (op W)) (x : V) :
    coefficientSectionValue M φ V x (M.obj.map i.op s) =
      coefficientSectionValue M φ W ⟨x.val, (leOfHom i) x.property⟩ s := by
  have h := ConcreteCategory.congr_hom (φ.hom.naturality i.op) s
  change (φ.hom.app (op V)) (M.obj.map i.op s) =
    (F₂X).obj.map i.op ((φ.hom.app (op W)) s) at h
  change constantSheafSectionAddEquiv X F V
      ((φ.hom.app (op V)) (M.obj.map i.op s)) x = _
  rw [h]
  exact constantSheafSectionAddEquiv_restrict X F i _ x

/-- A coefficient comparison sends the glued scalar action to pointwise
multiplication of locally constant functions. -/
theorem coefficientSectionValue_locallyConstantSMul
    (φ : Mab ⟶ F₂X) (W : Opens X)
    (z : LocallyConstant W F) (s : M.obj.obj (op W)) (x : W) :
    coefficientSectionValue M φ W x (locallyConstantSMul M z s) =
      z x * coefficientSectionValue M φ W x s := by
  let V := scalarFiber z (z x)
  let i : V ⟶ W := homOfLE (scalarFiber_le z (z x))
  let y : V := ⟨x.val, (mem_scalarFiber z (z x) x).mpr rfl⟩
  have h₁ := coefficientSectionValue_restrict M φ i (locallyConstantSMul M z s) y
  have h₂ := coefficientSectionValue_restrict M φ i s y
  change coefficientSectionValue M φ W ⟨y.val, (leOfHom i) y.property⟩
    (locallyConstantSMul M z s) = _
  rw [← h₁]
  change coefficientSectionValue M φ V y
    (M.obj.map (homOfLE (scalarFiber_le z (z x))).op (locallyConstantSMul M z s)) = _
  rw [locallyConstantSMul_restrict_fiber, additive_map_f2_smul, h₂]

/-- The representing-map comparison sends a weighted map to the product of
the scalar and the original coefficient function. -/
theorem coefficientSectionValue_locallyWeightedHom
    (φ : Mab ⟶ F₂X) (W : Opens X)
    (z : LocallyConstant W F) (f : freeOpenModule F W ⟶ M) (x : W) :
    coefficientSectionValue M φ W x
      (freeOpenModuleHomEquiv F W M (locallyWeightedHom z f)) =
      z x * coefficientSectionValue M φ W x (freeOpenModuleHomEquiv F W M f) := by
  rw [locallyWeightedHom_section, coefficientSectionValue_locallyConstantSMul]

/-- The section-valued Hom comparison has exactly the coefficient evaluation
used above. -/
theorem coefficientSectionValue_comparison
    (φ : Mab ⟶ F₂X) (W : Opens X)
    (f : freeOpenModule F W ⟶ M) (x : W) :
    constantSheafSectionAddEquiv X F W
      (freeOpenHomEquiv W (F₂X)
        (moduleFreeOpenHomComparison F W M f ≫ φ)) x =
      coefficientSectionValue M φ W x (freeOpenModuleHomEquiv F W M f) := by
  rw [freeOpenHomEquiv_naturality, freeOpenHomEquiv_moduleFreeOpenHomComparison]
  rfl

end Aoki
