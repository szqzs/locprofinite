import Aoki.Cech.ResolutionHomComparison
import Aoki.Cech.ModuleSheafResolution
import Aoki.Cech.SheafResolution
import Aoki.Sheaf.ModuleChartProjectivity
import Aoki.Sheaf.CohomologyVanishing

/-!
# Comparing module and ordinary sheaf cohomology

The integral and module free-open resolutions have identical section-valued
Hom complexes. This file constructs that additive comparison explicitly, before
passing to Ext through the genuine projective resolutions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Abelian TopologicalSpace Opposite

namespace Aoki

set_option backward.isDefEq.respectTransparency false

universe u

variable (R : Type u) [CommRing R] {X : TopCat.{u}}

/-- Forget the module structure on a sheaf while retaining its abelian groups. -/
def underlyingModuleSheafFunctor (X : TopCat.{u}) :
    TopCat.Sheaf (ModuleCat.{u} R) X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

abbrev underlyingModuleSheaf (M : TopCat.Sheaf (ModuleCat.{u} R) X) :
    TopCat.Sheaf AddCommGrpCat.{u} X := (underlyingModuleSheafFunctor R X).obj M

/-- Both representing objects encode precisely the same section. -/
def moduleFreeOpenHomComparison (W : Opens X) (M : TopCat.Sheaf (ModuleCat.{u} R) X) :
    (freeOpenModule R W ⟶ M) ≃+ (freeOpen W ⟶ underlyingModuleSheaf R M) :=
  (freeOpenModuleHomAddEquiv R W M).trans
    (freeOpenHomAddEquiv W (underlyingModuleSheaf R M)).symm

@[simp] theorem freeOpenHomEquiv_moduleFreeOpenHomComparison (W : Opens X)
    (M : TopCat.Sheaf (ModuleCat.{u} R) X) (f : freeOpenModule R W ⟶ M) :
    freeOpenHomEquiv W (underlyingModuleSheaf R M)
      (moduleFreeOpenHomComparison R W M f) = freeOpenModuleHomEquiv R W M f :=
  (freeOpenHomAddEquiv W (underlyingModuleSheaf R M)).apply_symm_apply _

/-- The section comparison commutes with restriction along an inclusion. -/
theorem moduleFreeOpenHomComparison_restrict {V W : Opens X} (i : V ⟶ W)
    (M : TopCat.Sheaf (ModuleCat.{u} R) X) (f : freeOpenModule R W ⟶ M) :
    moduleFreeOpenHomComparison R V M (freeOpenModuleMap R i ≫ f) =
      freeOpenMap i ≫ moduleFreeOpenHomComparison R W M f := by
  apply (freeOpenHomEquiv V (underlyingModuleSheaf R M)).injective
  rw [freeOpenHomEquiv_moduleFreeOpenHomComparison, freeOpenModuleHomEquiv_restrict,
    freeOpenHomEquiv_restrict, freeOpenHomEquiv_moduleFreeOpenHomComparison]
  rfl

/-- Fix the natural universe of Ext groups of module sheaves. -/
instance hasExtModuleSheaves (X : TopCat.{u}) :
    HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  hasExt_of_enoughInjectives _

namespace Cech

section Coproduct

universe v w
variable {C : Type v} [Category.{w} C] [Preadditive C]
variable {ι : Type*} (Z : ι → C) [HasCoproduct Z] (Y : C)

/-- Maps from a coproduct, as an additive equivalence. -/
def coproductHomAddEquiv : (∐ Z ⟶ Y) ≃+ (∀ i, Z i ⟶ Y) where
  toFun f i := Sigma.ι Z i ≫ f
  invFun f := Sigma.desc f
  left_inv f := by apply Sigma.hom_ext; intro i; exact Sigma.ι_desc _ _
  right_inv f := by funext i; exact Sigma.ι_desc _ _
  map_add' f g := by funext i; simp

end Coproduct

variable {N : ℕ} (U : Fin N → Opens X) (M : TopCat.Sheaf (ModuleCat.{u} R) X)

local instance : HasExt.{u} (TopCat.Sheaf (ModuleCat.{u} R) X) := hasExtModuleSheaves R X
local instance : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := hasExtAbelianSheaves X

/-- The degreewise comparison between the module and integral Hom complexes. -/
def moduleCechHomEquiv (n : ℕ) :
    (orderedTerm U (freeOpenModuleFunctor R X) n ⟶ M) ≃+
      (orderedTerm U (freeOpenFunctor X) n ⟶ underlyingModuleSheaf R M) :=
  (coproductHomAddEquiv (fun s : Face N n => freeOpenModule R (faceOpen U s)) M).trans
    ((AddEquiv.piCongrRight (fun s : Face N n =>
      moduleFreeOpenHomComparison R (faceOpen U s) M)).trans
        (coproductHomAddEquiv (fun s : Face N n => freeOpen (faceOpen U s))
          (underlyingModuleSheaf R M)).symm)

@[reassoc]
theorem ι_moduleCechHomEquiv (n : ℕ)
    (f : orderedTerm U (freeOpenModuleFunctor R X) n ⟶ M) (s : Face N n) :
    Sigma.ι (fun t : Face N n => freeOpen (faceOpen U t)) s ≫
      moduleCechHomEquiv R U M n f =
        moduleFreeOpenHomComparison R (faceOpen U s) M
          (Sigma.ι (fun t : Face N n => freeOpenModule R (faceOpen U t)) s ≫ f) := by
  exact Sigma.ι_desc _ _

section Differential

universe v w
variable {C : Type v} [Category.{w} C] [Preadditive C] [HasFiniteCoproducts C]
variable (F : Opens X ⥤ C) {Y : C}

/-- The differential evaluated on one face, followed by a coefficient morphism. -/
theorem ι_orderedDifferential_comp (n : ℕ) (s : Face N (n + 1))
    (f : orderedTerm U F n ⟶ Y) :
    Sigma.ι (fun t : Face N (n + 1) => F.obj (faceOpen U t)) s ≫
      orderedDifferential U F n ≫ f =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (F.map (homOfLE (faceOpen_le_delete U s i)) ≫
            Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) (deleteFace s i) ≫ f) := by
  simp only [orderedDifferential, alternatingDifferential, sum_comp, comp_sum,
    zsmul_comp, comp_zsmul, ι_orderedFace_assoc]

end Differential

set_option maxHeartbeats 800000 in
/-- The two differentials agree under the section comparison. -/
theorem moduleCechHomEquiv_d (n : ℕ)
    (f : orderedTerm U (freeOpenModuleFunctor R X) n ⟶ M) :
    moduleCechHomEquiv R U M (n + 1)
        (orderedDifferential U (freeOpenModuleFunctor R X) n ≫ f) =
      orderedDifferential U (freeOpenFunctor X) n ≫ moduleCechHomEquiv R U M n f := by
  apply Sigma.hom_ext
  intro s
  erw [ι_moduleCechHomEquiv]
  erw [ι_orderedDifferential_comp U (freeOpenModuleFunctor R X) n s f]
  rw [ι_orderedDifferential_comp]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change moduleFreeOpenHomComparison R (faceOpen U s) M
      (freeOpenModuleMap R (homOfLE (faceOpen_le_delete U s i)) ≫ _) =
    freeOpenMap (homOfLE (faceOpen_le_delete U s i)) ≫ _
  rw [moduleFreeOpenHomComparison_restrict]
  erw [ι_moduleCechHomEquiv]
  rfl


/-- Changing the first argument of Ext by an isomorphism. -/
def extFirstAddEquiv {C : Type*} [Category.{u} C] [Abelian C] [HasExt.{u} C]
    {Z Z' : C} (e : Z ≅ Z') (Y : C) (n : ℕ) : Ext Z' Y n ≃+ Ext Z Y n :=
  (((extFunctor n).mapIso e.op).app Y).addCommGroupIsoToAddEquiv

/-- The section comparison on actual free-open resolutions, including degree zero. -/
def moduleFreeOpenExtAddEquiv (hcover : iSup U = ⊤)
    (hprojR : ∀ n (s : Face N n), Projective (freeOpenModule R (faceOpen U s)))
    (hprojZ : ∀ n (s : Face N n), Projective (freeOpen (faceOpen U s))) :
    (n : ℕ) → Ext (freeOpenModule R (⊤ : Opens X)) M n ≃+
      Ext (freeOpen (⊤ : Opens X)) (underlyingModuleSheaf R M) n
  | 0 => Ext.addEquiv₀.trans ((moduleFreeOpenHomComparison R ⊤ M).trans Ext.addEquiv₀.symm)
  | n + 1 => resolutionExtAddEquiv (Y := M) (Y' := underlyingModuleSheaf R M)
      (freeOpenModuleProjectiveResolution R (X := X) U hcover hprojR)
      (freeOpenProjectiveResolution (X := X) U hcover hprojZ)
      (moduleCechHomEquiv R U M)
      (fun k f => by
        change moduleCechHomEquiv R U M (k + 1)
          ((orderedComplex U (freeOpenModuleFunctor R X)).d (k + 1) k ≫ f) =
          (orderedComplex U (freeOpenFunctor X)).d (k + 1) k ≫
            moduleCechHomEquiv R U M k f
        simpa only [orderedComplex_d] using moduleCechHomEquiv_d R U M k f) n

/-- The comparison sends an actual represented module Ext class to the same
section-valued cocycle on the integral resolution. -/
theorem moduleFreeOpenExtAddEquiv_extMk (hcover : iSup U = ⊤)
    (hprojR : ∀ n (s : Face N n), Projective (freeOpenModule R (faceOpen U s)))
    (hprojZ : ∀ n (s : Face N n), Projective (freeOpen (faceOpen U s)))
    (n : ℕ) (f : orderedTerm U (freeOpenModuleFunctor R X) (n + 1) ⟶ M)
    (hf : orderedDifferential U (freeOpenModuleFunctor R X) (n + 1) ≫ f = 0) :
    moduleFreeOpenExtAddEquiv R U M hcover hprojR hprojZ (n + 1)
      ((freeOpenModuleProjectiveResolution R U hcover hprojR).extMk f (n + 2) rfl
        (by simpa only [freeOpenModuleProjectiveResolution_complex, orderedComplex_d] using hf)) =
      (freeOpenProjectiveResolution U hcover hprojZ).extMk
        (moduleCechHomEquiv R U M (n + 1) f) (n + 2) rfl
        (by
          change (orderedComplex U (freeOpenFunctor X)).d (n + 2) (n + 1) ≫ _ = 0
          rw [orderedComplex_d, ← moduleCechHomEquiv_d, hf, map_zero]) := by
  exact resolutionExtAddEquiv_extMk
    (freeOpenModuleProjectiveResolution R (X := X) U hcover hprojR)
    (freeOpenProjectiveResolution (X := X) U hcover hprojZ)
    (moduleCechHomEquiv R U M) _ n f _

/-- A finite cover by represented projectives identifies module Ext from the
constant rank-one sheaf with ordinary sheaf cohomology of the underlying groups. -/
def moduleSheafCohomologyAddEquiv (hcover : iSup U = ⊤)
    (hprojR : ∀ n (s : Face N n), Projective (freeOpenModule R (faceOpen U s)))
    (hprojZ : ∀ n (s : Face N n), Projective (freeOpen (faceOpen U s))) (n : ℕ) :
    Ext ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)) M n ≃+ CategoryTheory.Sheaf.H (underlyingModuleSheaf R M) n :=
  (extFirstAddEquiv (freeOpenModuleTopIso R X) M n).trans
    ((moduleFreeOpenExtAddEquiv R U M hcover hprojR hprojZ n).trans
      (extFirstAddEquiv (freeOpenTopIso X) (underlyingModuleSheaf R M) n).symm)

end Cech

namespace Geometry

variable {A : ℕ → Type u} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

local instance : HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology (U A n))
    (ModuleCat.{u} R)) :=
  hasExtModuleSheaves R (TopCat.of (U A n))
local instance : HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology (U A n))
    AddCommGrpCat.{u}) :=
  hasExtAbelianSheaves (TopCat.of (U A n))

/-- The actual quotient cover supplies all module projectivity inputs. -/
theorem module_chart_face_projective (k : ℕ) (s : Cech.Face (n + 1) k) :
    Projective (freeOpenModule R (X := TopCat.of (U A n)) (Cech.faceOpen chartOpen s)) := by
  rw [faceOpen_chartOpen]
  exact projective_freeOpenModule_chartIntersection R _
    (Finset.Nonempty.image Finset.univ_nonempty s)

/-- The actual quotient cover supplies all integral projectivity inputs. -/
theorem integral_chart_face_projective (k : ℕ) (s : Cech.Face (n + 1) k) :
    Projective (freeOpen (X := TopCat.of (U A n)) (Cech.faceOpen chartOpen s)) := by
  rw [faceOpen_chartOpen]
  exact projective_freeOpen_chartIntersection _
    (Finset.Nonempty.image Finset.univ_nonempty s)

/-- On the concrete quotient space, the comparison has no assumed exactness or
projectivity hypotheses: both are provided by its proved geometric cover. -/
def quotientModuleCohomologyAddEquiv
    (M : TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of (U A n))) (k : ℕ) :
    Ext ((constantSheaf (Opens.grothendieckTopology (U A n)) (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)) M k ≃+ CategoryTheory.Sheaf.H (underlyingModuleSheaf R M) k :=
  Cech.moduleSheafCohomologyAddEquiv R (X := TopCat.of (U A n))
    (chartOpen (A := A) (n := n)) M (iSup_chartOpen (A := A) (n := n))
    (module_chart_face_projective R (A := A) (n := n))
    (integral_chart_face_projective (A := A) (n := n)) k

end Geometry
end Aoki
