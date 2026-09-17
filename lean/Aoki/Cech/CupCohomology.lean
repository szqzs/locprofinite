import Aoki.Cech.CupExt
import Aoki.Cech.NonzeroClass
import Aoki.Sheaf.ModuleConstantComparison

/-!
# The Yoneda cup algebra in ordinary sheaf cohomology

The represented module on the whole space is isomorphic to the constant
rank-one module. Its endomorphism Ext algebra therefore gives the ordinary
sheaf cup product. The comparison below is induced by the identical section
Hom complexes of the actual module and integral projective resolutions.
-/

noncomputable section

namespace Aoki.Cech

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Geometry Homological

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Hom

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Postcomposition with an isomorphism as an additive equivalence. -/
def postcompHomAddEquiv (P : C) {Y Z : C} (e : Y ≅ Z) : (P ⟶ Y) ≃+ (P ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp

/-- Precomposition with the inverse of an isomorphism. -/
def precompHomAddEquiv {P Q : C} (e : P ≅ Q) (Y : C) : (P ⟶ Y) ≃+ (Q ⟶ Y) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp

end Hom

variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

local instance : HasExt.{0}
    (TopCat.Sheaf (ModuleCat F) (TopCat.of (U A n))) :=
  hasExtModuleSheaves F (TopCat.of (U A n))
local instance : HasExt.{0}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology (U A n)) AddCommGrpCat) :=
  hasExtAbelianSheaves (TopCat.of (U A n))
local instance : HasExt.{0} (TopCat.Sheaf AddCommGrpCat (TopCat.of (U A n))) :=
  hasExtAbelianSheaves (TopCat.of (U A n))

/-- The identical section Hom complexes, including the constant-F₂ coefficient
identification. -/
def cupCochainEquiv (k : ℕ) :
    ((quotientCupResolution (A := A) (n := n)).complex.X k ⟶
      freeOpenModule F (X := TopCat.of (U A n)) ⊤) ≃+
    ((quotientIntegralResolution A n).complex.X k ⟶ constantF2Sheaf) :=
  (moduleCechHomEquiv F (X := TopCat.of (U A n)) chartOpen
    (freeOpenModule F (X := TopCat.of (U A n)) ⊤) k).trans
      (postcompHomAddEquiv _ (underlyingFreeOpenModuleTopIso F (TopCat.of (U A n))))

theorem cupCochainEquiv_d (k : ℕ)
    (f : (quotientCupResolution (A := A) (n := n)).complex.X k ⟶
      freeOpenModule F (X := TopCat.of (U A n)) ⊤) :
    cupCochainEquiv (k + 1) (quotientCupResolution.complex.d (k + 1) k ≫ f) =
      (quotientIntegralResolution A n).complex.d (k + 1) k ≫ cupCochainEquiv k f := by
  simp only [quotientCupResolution, freeOpenModuleProjectiveResolution_complex,
    quotientIntegralResolution_complex, orderedComplex_d]
  change moduleCechHomEquiv F (X := TopCat.of (U A n)) (chartOpen (A := A) (n := n))
      (freeOpenModule F (X := TopCat.of (U A n)) ⊤) (k + 1)
      (orderedDifferential chartOpen (freeOpenModuleFunctor F (TopCat.of (U A n))) k ≫ f) ≫ _ =
    orderedDifferential chartOpen (freeOpenFunctor (TopCat.of (U A n))) k ≫
      (moduleCechHomEquiv F (X := TopCat.of (U A n)) (chartOpen (A := A) (n := n))
        (freeOpenModule F (X := TopCat.of (U A n)) ⊤) k f ≫ _)
  rw [moduleCechHomEquiv_d, Category.assoc]

/-- The section-induced identification of the module Yoneda algebra with
ordinary constant-F₂ sheaf cohomology. -/
def cupCohomologyAddEquiv : (k : ℕ) →
    Ext.{0} (freeOpenModule F (X := TopCat.of (U A n)) ⊤)
      (freeOpenModule F (X := TopCat.of (U A n)) ⊤) k ≃+
        CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) k
  | 0 => Ext.addEquiv₀.trans
      ((moduleFreeOpenHomComparison F (⊤ : Opens (U A n))
        (freeOpenModule F (X := TopCat.of (U A n)) ⊤)).trans
        ((postcompHomAddEquiv _ (underlyingFreeOpenModuleTopIso F (TopCat.of (U A n)))).trans
          ((precompHomAddEquiv (freeOpenTopIso (TopCat.of (U A n))) constantF2Sheaf).trans
            Ext.addEquiv₀.symm)))
  | k + 1 => resolutionExtAddEquiv
      (Y := freeOpenModule F (X := TopCat.of (U A n)) ⊤)
      (Y' := constantF2Sheaf (A := A) (n := n))
      (quotientCupResolution (A := A) (n := n)) (quotientIntegralResolution A n)
      (cupCochainEquiv (A := A) (n := n)) (cupCochainEquiv_d (A := A) (n := n)) k

/-- The comparison acts on a positive-degree class by its explicit cochain
comparison, with no product-compatibility hypothesis. -/
theorem cupCohomologyAddEquiv_extMk (k : ℕ)
    (f : (quotientCupResolution (A := A) (n := n)).complex.X (k + 1) ⟶
      freeOpenModule F (X := TopCat.of (U A n)) ⊤)
    (hf : quotientCupResolution.complex.d (k + 2) (k + 1) ≫ f = 0) :
    cupCohomologyAddEquiv (k + 1)
      (quotientCupResolution.extMk f (k + 2) rfl hf) =
      (quotientIntegralResolution A n).extMk (cupCochainEquiv (k + 1) f) (k + 2) rfl
        (by rw [← cupCochainEquiv_d, hf, map_zero]) :=
  resolutionExtAddEquiv_extMk (quotientCupResolution (A := A) (n := n))
    (quotientIntegralResolution A n)
    (cupCochainEquiv (A := A) (n := n)) (cupCochainEquiv_d (A := A) (n := n)) k f hf

/-- The usual sheaf cup product, realized as Yoneda composition for the
constant rank-one module and transported through the section comparison. -/
def cupProduct {a b c : ℕ}
    (α : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) a)
    (β : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) b)
    (h : a + b = c) :
    CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) c :=
  cupCohomologyAddEquiv c
    (((cupCohomologyAddEquiv a).symm α).comp ((cupCohomologyAddEquiv b).symm β) h)

/-- Repeated cup powers of an ordinary degree-one sheaf-cohomology class. -/
def cupPower (η : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) 1)
    (r : ℕ) : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) r :=
  cupCohomologyAddEquiv r (yonedaPower ((cupCohomologyAddEquiv 1).symm η) r)

@[simp] theorem cupPower_one
    (η : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) 1) :
    cupPower η 1 = η := by simp [cupPower]

theorem cupPower_succ
    (η : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) 1) (r : ℕ) :
    cupPower η (r + 1) = cupProduct η (cupPower η r) (by omega) := by
  simp [cupPower, cupProduct]

end Aoki.Cech
