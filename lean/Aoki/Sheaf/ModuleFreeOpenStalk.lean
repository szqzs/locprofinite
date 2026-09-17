import Aoki.Sheaf.ModuleFreeOpen
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Stalks of the free module sheaf represented by an open

The stalk is zero outside the open, and its map to the free rank-one module stalk of
all of the space is an isomorphism inside the open. The proof uses the
stalk–skyscraper adjunction, so it also identifies all inclusion maps naturally.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Aoki

universe u
variable (R : Type u) [CommRing R] {X : TopCat.{u}}

/-- The stalk functor for module sheaves at a point. -/
abbrev moduleStalk (x : X) : TopCat.Sheaf (ModuleCat.{u} R) X ⥤ (ModuleCat.{u} R) :=
  TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙ TopCat.Presheaf.stalkFunctor _ x

/-- The adjunction computes maps out of a represented free stalk as skyscraper sections. -/
def freeOpenModuleStalkHomEquiv (W : Opens X) (x : X) (M : (ModuleCat.{u} R)) :
    ((moduleStalk R x).obj (freeOpenModule R W) ⟶ M) ≃
      (skyscraperSheaf x M).obj.obj (op W) := by
  classical
  exact ((stalkSkyscraperSheafAdjunction x).homEquiv (freeOpenModule R W) M).trans
    (freeOpenModuleHomEquiv R W (skyscraperSheaf x M))

/-- The preceding equivalence carries inclusions to skyscraper restrictions. -/
theorem freeOpenModuleStalkHomEquiv_restrict {V W : Opens X} (i : V ⟶ W) (x : X)
    (M : (ModuleCat.{u} R)) (f : (moduleStalk R x).obj (freeOpenModule R W) ⟶ M) :
    freeOpenModuleStalkHomEquiv R V x M ((moduleStalk R x).map (freeOpenModuleMap R i) ≫ f) =
      (skyscraperSheaf x M).obj.map i.op (freeOpenModuleStalkHomEquiv R W x M f) := by
  classical
  dsimp only [freeOpenModuleStalkHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact freeOpenModuleHomEquiv_restrict R i _ _

/-- Away from its representing open, the free module sheaf has zero stalk. -/
theorem freeOpenModule_stalk_isZero (W : Opens X) (x : X) (hx : x ∉ W) :
    IsZero ((moduleStalk R x).obj (freeOpenModule R W)) := by
  classical
  apply (IsZero.iff_id_eq_zero _).2
  apply (freeOpenModuleStalkHomEquiv R W x _).injective
  have hz := (isTerminalSkyscraperSheafObjObjOfNotMem
    (A := (moduleStalk R x).obj (freeOpenModule R W)) hx).isZero
  haveI := ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

/-- An inclusion induces an isomorphism of free stalks whenever its source contains the point. -/
theorem freeOpenModule_stalk_map_isIso {V W : Opens X} (i : V ⟶ W) (x : X) (hx : x ∈ V) :
    IsIso ((moduleStalk R x).map (freeOpenModuleMap R i)) := by
  classical
  apply isIso_of_coyoneda_map_bijective
  intro M
  let eV := freeOpenModuleStalkHomEquiv R V x M
  let eW := freeOpenModuleStalkHomEquiv R W x M
  let r := (skyscraperSheaf x M).obj.map i.op
  have hr : IsIso r := by
    change IsIso ((skyscraperPresheaf x M).map i.op)
    erw [skyscraperPresheaf_map, dif_pos hx]
    exact (eqToIso (show (skyscraperPresheaf x M).obj (op W) =
      (skyscraperPresheaf x M).obj (op V) from by
        dsimp [skyscraperPresheaf]
        rw [if_pos hx, if_pos (i.le hx)])).isIso_hom
  have hb := (ConcreteCategory.isIso_iff_bijective r).1 hr
  constructor
  · intro f g hfg
    apply eW.injective
    apply hb.1
    simpa only [eV, eW, r, ← freeOpenModuleStalkHomEquiv_restrict R] using congrArg eV hfg
  · intro f
    obtain ⟨m, hm⟩ := hb.2 (eV f)
    refine ⟨eW.symm m, ?_⟩
    apply eV.injective
    rw [show eV ((moduleStalk R x).map (freeOpenModuleMap R i) ≫ eW.symm m) =
      r (eW (eW.symm m)) from freeOpenModuleStalkHomEquiv_restrict R i x M _]
    simpa using hm

/-- Inside `W`, its free stalk is canonically the free stalk on the entire space. -/
def freeOpenModuleStalkTopIso (W : Opens X) (x : X) (hx : x ∈ W) :
    (moduleStalk R x).obj (freeOpenModule R W) ≅ (moduleStalk R x).obj (freeOpenModule R (⊤ : Opens X)) := by
  haveI := freeOpenModule_stalk_map_isIso R (homOfLE (show W ≤ ⊤ from le_top)) x hx
  exact asIso ((moduleStalk R x).map (freeOpenModuleMap R (homOfLE le_top)))

@[simp] theorem freeOpenModuleStalkTopIso_hom (W : Opens X) (x : X) (hx : x ∈ W) :
    (freeOpenModuleStalkTopIso R W x hx).hom =
      (moduleStalk R x).map (freeOpenModuleMap R (homOfLE (show W ≤ ⊤ from le_top))) := rfl

end Aoki
