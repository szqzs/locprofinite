import Aoki.Cech.ModuleComparison
import Aoki.Sheaf.LocallyConstant

/-! # The underlying abelian sheaf of the constant rank-one module -/

noncomputable section

namespace Aoki

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})

instance moduleForget_preservesSheafification :
    (Opens.grothendieckTopology X).PreservesSheafification
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  GrothendieckTopology.instPreservesSheafification _ _

/-- Forgetting the module structure commutes with forming the constant sheaf. -/
def underlyingConstantModuleIso :
    underlyingModuleSheaf R
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of R) :=
  (constantCommuteCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).app (ModuleCat.of R R)

/-- The underlying abelian sheaf of the top represented free module is the
ordinary constant abelian sheaf with value `R`. -/
def underlyingFreeOpenModuleTopIso :
    underlyingModuleSheaf R (freeOpenModule R (⊤ : Opens X)) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of R) :=
  (underlyingModuleSheafFunctor R X).mapIso (freeOpenModuleTopIso R X) ≪≫
    underlyingConstantModuleIso R X

variable [TopologicalSpace R] [DiscreteTopology R]

/-- Sections of the top free module, viewed as locally constant functions. -/
def freeOpenModuleTopSectionAddEquiv (W : Opens X) :
    (freeOpenModule R (⊤ : Opens X)).obj.obj (op W) ≃+ LocallyConstant W R :=
  (((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op W)).mapIso
    (underlyingFreeOpenModuleTopIso R X)).addCommGroupIsoToAddEquiv).trans
      (constantSheafSectionAddEquiv X R W)

/-- The coefficient identification commutes with restriction. -/
theorem freeOpenModuleTopSectionAddEquiv_restrict {V W : Opens X} (i : V ⟶ W)
    (s : (freeOpenModule R (⊤ : Opens X)).obj.obj (op W)) (x : V) :
    freeOpenModuleTopSectionAddEquiv R X V
      ((freeOpenModule R (⊤ : Opens X)).obj.map i.op s) x =
      freeOpenModuleTopSectionAddEquiv R X W s ⟨x.val, (leOfHom i) x.property⟩ := by
  have h := ConcreteCategory.congr_hom
    ((underlyingFreeOpenModuleTopIso R X).hom.hom.naturality i.op) s
  change constantSheafSectionAddEquiv X R V
    ((underlyingFreeOpenModuleTopIso R X).hom.hom.app (op V)
      ((freeOpenModule R (⊤ : Opens X)).obj.map i.op s)) x = _
  change (underlyingFreeOpenModuleTopIso R X).hom.hom.app (op V)
      ((freeOpenModule R (⊤ : Opens X)).obj.map i.op s) =
    (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of R)).obj.map i.op)
        ((underlyingFreeOpenModuleTopIso R X).hom.hom.app (op W) s) at h
  rw [h]
  exact constantSheafSectionAddEquiv_restrict X R i _ x


/-- Sheafifying a constant element gives the corresponding constant function. -/
theorem constantSheafSectionAddEquiv_toSheafify (W : Opens X) (r : R) (x : W) :
    constantSheafSectionAddEquiv X R W
      ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of R))).app (op W) r) x = r := by
  have h : toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of R)) ≫
        (constantSheafLocallyConstantIso X R).hom.hom =
          constantToLocallyConstant X R := by
    change toSheafify (Opens.grothendieckTopology X) _ ≫
      sheafifyMap (Opens.grothendieckTopology X) (constantToLocallyConstant X R) ≫
        (isoSheafify (Opens.grothendieckTopology X) (locallyConstantAbSheaf X R).property).inv = _
    rw [← toSheafify_naturality_assoc]
    erw [← isoSheafify_hom (Opens.grothendieckTopology X) (locallyConstantAbSheaf X R).property]
    rw [Iso.hom_inv_id, Category.comp_id]
  have hh := ConcreteCategory.congr_hom (NatTrans.congr_app h (op W)) r
  exact congrArg (fun f => f.hom x) hh

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The constant-sheaf comparison preserves the sheafification of a constant element. -/
theorem underlyingConstantModuleIso_toSheafify (W : Opens X) (r : R) :
    (underlyingConstantModuleIso R X).hom.hom.app (op W)
      ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of R R))).app (op W) r) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of R))).app (op W) r := by
  let J := Opens.grothendieckTopology X
  let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let P := (Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of R R)
  have h : Functor.whiskerRight (toSheafify J P) F ≫
      (underlyingConstantModuleIso R X).hom.hom =
        (Functor.constComp (Opens X)ᵒᵖ (ModuleCat.of R R) F).hom ≫
          toSheafify J ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of R)) := by
    change Functor.whiskerRight (toSheafify J P) F ≫
      (sheafifyComposeIso J F P).inv ≫
        sheafifyMap J (Functor.constComp (Opens X)ᵒᵖ (ModuleCat.of R R) F).hom = _
    rw [← Category.assoc, sheafComposeIso_inv_fac, ← toSheafify_naturality]
    rfl
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op W)) r

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The representing isomorphism sends the universal generator to the constant one section. -/
theorem freeOpenModuleHomEquiv_topIso :
    freeOpenModuleHomEquiv R (⊤ : Opens X)
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)) (freeOpenModuleTopIso R X).hom =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of R R))).app (op ⊤) (1 : R) := by
  change (freeOpenModuleHomEquiv R (⊤ : Opens X) _)
    ((freeOpenModuleHomEquiv R (⊤ : Opens X) _).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The universal section represented by `W → top` has constant value one. -/
theorem freeOpenModuleTopSectionAddEquiv_generator (W : Opens X) (x : W) :
    freeOpenModuleTopSectionAddEquiv R X W
      (freeOpenModuleHomEquiv R W (freeOpenModule R (⊤ : Opens X))
        (freeOpenModuleMap R (homOfLE (show W ≤ ⊤ from le_top)))) x = 1 := by
  have htop : freeOpenModuleTopSectionAddEquiv R X (⊤ : Opens X)
      (freeOpenModuleHomEquiv R ⊤ (freeOpenModule R (⊤ : Opens X)) (𝟙 _))
        ⟨x.val, trivial⟩ = 1 := by
    change constantSheafSectionAddEquiv X R ⊤
      ((underlyingConstantModuleIso R X).hom.hom.app (op ⊤)
        ((freeOpenModuleTopIso R X).hom.hom.app (op ⊤)
          (freeOpenModuleHomEquiv R ⊤ (freeOpenModule R (⊤ : Opens X)) (𝟙 _)))) _ = 1
    rw [← freeOpenModuleHomEquiv_naturality, Category.id_comp,
      freeOpenModuleHomEquiv_topIso, underlyingConstantModuleIso_toSheafify]
    exact constantSheafSectionAddEquiv_toSheafify R X ⊤ 1 _
  have hr := freeOpenModuleHomEquiv_restrict R
    (homOfLE (show W ≤ ⊤ from le_top)) (freeOpenModule R (⊤ : Opens X)) (𝟙 _)
  rw [Category.comp_id] at hr
  rw [hr, freeOpenModuleTopSectionAddEquiv_restrict]
  exact htop

end Aoki
