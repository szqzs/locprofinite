import Aoki.Sheaf.FreeOpen
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Stalks of the free abelian sheaf represented by an open

The stalk is zero outside the open, and its map to the free integral stalk of
all of the space is an isomorphism inside the open. The proof uses the
stalk–skyscraper adjunction, so it also identifies all inclusion maps naturally.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Aoki

universe u
variable {X : TopCat.{u}}

/-- The stalk functor for abelian sheaves at a point. -/
abbrev abelianStalk (x : X) : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor _ x

/-- The adjunction computes maps out of a represented free stalk as skyscraper sections. -/
def freeOpenStalkHomEquiv (W : Opens X) (x : X) (M : AddCommGrpCat.{u}) :
    ((abelianStalk x).obj (freeOpen W) ⟶ M) ≃
      (skyscraperSheaf x M).obj.obj (op W) := by
  classical
  exact ((stalkSkyscraperSheafAdjunction x).homEquiv (freeOpen W) M).trans
    (freeOpenHomEquiv W (skyscraperSheaf x M))

/-- The preceding equivalence carries inclusions to skyscraper restrictions. -/
theorem freeOpenStalkHomEquiv_restrict {V W : Opens X} (i : V ⟶ W) (x : X)
    (M : AddCommGrpCat.{u}) (f : (abelianStalk x).obj (freeOpen W) ⟶ M) :
    freeOpenStalkHomEquiv V x M ((abelianStalk x).map (freeOpenMap i) ≫ f) =
      (skyscraperSheaf x M).obj.map i.op (freeOpenStalkHomEquiv W x M f) := by
  classical
  dsimp only [freeOpenStalkHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact freeOpenHomEquiv_restrict i _ _

/-- Away from its representing open, the free abelian sheaf has zero stalk. -/
theorem freeOpen_stalk_isZero (W : Opens X) (x : X) (hx : x ∉ W) :
    IsZero ((abelianStalk x).obj (freeOpen W)) := by
  classical
  apply (IsZero.iff_id_eq_zero _).2
  apply (freeOpenStalkHomEquiv W x _).injective
  have hz := (isTerminalSkyscraperSheafObjObjOfNotMem
    (A := (abelianStalk x).obj (freeOpen W)) hx).isZero
  haveI := AddCommGrpCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

/-- An inclusion induces an isomorphism of free stalks whenever its source contains the point. -/
theorem freeOpen_stalk_map_isIso {V W : Opens X} (i : V ⟶ W) (x : X) (hx : x ∈ V) :
    IsIso ((abelianStalk x).map (freeOpenMap i)) := by
  classical
  apply isIso_of_coyoneda_map_bijective
  intro M
  let eV := freeOpenStalkHomEquiv V x M
  let eW := freeOpenStalkHomEquiv W x M
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
    simpa only [eV, eW, r, ← freeOpenStalkHomEquiv_restrict] using congrArg eV hfg
  · intro f
    obtain ⟨m, hm⟩ := hb.2 (eV f)
    refine ⟨eW.symm m, ?_⟩
    apply eV.injective
    rw [show eV ((abelianStalk x).map (freeOpenMap i) ≫ eW.symm m) =
      r (eW (eW.symm m)) from freeOpenStalkHomEquiv_restrict i x M _]
    simpa using hm

/-- Inside `W`, its free stalk is canonically the free stalk on the entire space. -/
def freeOpenStalkTopIso (W : Opens X) (x : X) (hx : x ∈ W) :
    (abelianStalk x).obj (freeOpen W) ≅ (abelianStalk x).obj (freeOpen (⊤ : Opens X)) := by
  haveI := freeOpen_stalk_map_isIso (homOfLE (show W ≤ ⊤ from le_top)) x hx
  exact asIso ((abelianStalk x).map (freeOpenMap (homOfLE le_top)))

@[simp] theorem freeOpenStalkTopIso_hom (W : Opens X) (x : X) (hx : x ∈ W) :
    (freeOpenStalkTopIso W x hx).hom =
      (abelianStalk x).map (freeOpenMap (homOfLE (show W ≤ ⊤ from le_top))) := rfl

end Aoki
