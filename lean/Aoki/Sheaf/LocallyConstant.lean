import Aoki.Sheaf.FreeOpen
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.ContinuousMap.LocallyConstant

/-!
# The constant abelian sheaf as locally constant functions

For a discrete commutative ring, the constant abelian sheaf is canonically
isomorphic to the sheaf of continuous (equivalently, locally constant) functions.
The comparison is proved by sheafifying the locally bijective constant-function
map. In particular, no injectivity assertion is made on the empty open set.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Aoki

open CategoryTheory TopologicalSpace Opposite

universe u

variable (X : TopCat.{u}) (R : Type u) [CommRing R]
  [TopologicalSpace R] [DiscreteTopology R]

/-- Continuous functions, regarded as an abelian presheaf. -/
def locallyConstantAbPresheaf : X.Presheaf AddCommGrpCat.{u} :=
  TopCat.presheafToTopCommRing X (TopCommRingCat.of R) ⋙
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- Continuous functions into a discrete ring form an abelian sheaf. -/
def locallyConstantAbSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨locallyConstantAbPresheaf X R, by
    apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
    exact (TopCat.sheafToTop (X := X) (TopCat.of R)).property⟩

/-- The map sending a constant-presheaf section to the constant function. -/
def constantToLocallyConstant :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of R) ⟶
      locallyConstantAbPresheaf X R where
  app U := AddCommGrpCat.ofHom
    { toFun := fun r => TopCat.ofHom (ContinuousMap.const _ r)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality _ _ _ := by ext r; rfl

instance constantToLocallyConstant_locallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constantToLocallyConstant X R) where
  equalizerSieve_mem {U} r s h x hx := by
    have hrs : r = s := congrArg (fun f => f.hom ⟨x, hx⟩) h
    refine ⟨U.unop, 𝟙 _, ?_, hx⟩
    exact hrs

instance constantToLocallyConstant_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constantToLocallyConstant X R) where
  imageSieve_mem {U} f x hx := by
    let a : R := f.hom ⟨x, hx⟩
    let S : Set U := {y | f.hom y = a}
    have hS : IsOpen S := f.hom.continuous.isOpen_preimage _ (isOpen_discrete {a})
    let V : Opens X := ⟨Subtype.val '' S, U.isOpenEmbedding'.isOpenMap _ hS⟩
    have hVU : V ≤ U := by rintro y ⟨z, _, rfl⟩; exact z.property
    refine ⟨V, homOfLE hVU, ⟨a, ?_⟩, ?_⟩
    · apply TopCat.hom_ext
      ext y
      obtain ⟨z, hz, he⟩ := y.property
      change a = f.hom ⟨y.val, hVU y.property⟩
      have he' : z = (⟨y.val, hVU y.property⟩ : U) := Subtype.ext he
      exact (he' ▸ hz).symm
    · exact ⟨⟨x, hx⟩, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The constant abelian sheaf is the sheaf of locally constant functions. -/
def constantSheafLocallyConstantIso :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of R) ≅ locallyConstantAbSheaf X R := by
  let f := constantToLocallyConstant X R
  haveI : IsIso ((presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map f) :=
    (GrothendieckTopology.W_iff _ f).mp
      (GrothendieckTopology.W_of_isLocallyBijective _ f)
  exact asIso ((presheafToSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).map f) ≪≫ (sheafificationIso (locallyConstantAbSheaf X R)).symm

/-- A section of the function sheaf is explicitly a locally constant function. -/
def locallyConstantSectionAddEquiv (U : Opens X) :
    (locallyConstantAbSheaf X R).obj.obj (op U) ≃+ LocallyConstant U R where
  toFun f := ⟨(show C(U, R) from f.hom),
    (IsLocallyConstant.iff_continuous (show C(U, R) from f.hom)).mpr f.hom.continuous⟩
  invFun f := TopCat.ofHom f.toContinuousMap
  left_inv f := by rfl
  right_inv f := by rfl
  map_add' _ _ := rfl

@[simp] theorem locallyConstantSectionAddEquiv_apply (U : Opens X)
    (s : (locallyConstantAbSheaf X R).obj.obj (op U)) (x : U) :
    locallyConstantSectionAddEquiv X R U s x = s.hom x := rfl

/-- The section equivalence respects restriction to a smaller open. -/
theorem locallyConstantSectionAddEquiv_restrict {V U : Opens X} (i : V ⟶ U)
    (s : (locallyConstantAbSheaf X R).obj.obj (op U)) (x : V) :
    locallyConstantSectionAddEquiv X R V
        ((locallyConstantAbSheaf X R).obj.map i.op s) x =
      locallyConstantSectionAddEquiv X R U s ⟨x.val, (leOfHom i) x.property⟩ := rfl

/-- Explicit additive description of sections of the actual constant sheaf. -/
def constantSheafSectionAddEquiv (U : Opens X) :
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of R)).obj.obj (op U) ≃+ LocallyConstant U R :=
  (Iso.addCommGroupIsoToAddEquiv
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).mapIso
      (constantSheafLocallyConstantIso X R))).trans
    (locallyConstantSectionAddEquiv X R U)

/-- Restriction of a constant-sheaf section is restriction of its locally
constant function. -/
theorem constantSheafSectionAddEquiv_restrict {V U : Opens X} (i : V ⟶ U)
    (s : ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of R)).obj.obj (op U)) (x : V) :
    constantSheafSectionAddEquiv X R V
        (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of R)).obj.map i.op s) x =
      constantSheafSectionAddEquiv X R U s ⟨x.val, (leOfHom i) x.property⟩ := by
  have h := ConcreteCategory.congr_hom
    ((constantSheafLocallyConstantIso X R).hom.hom.naturality i.op) s
  exact congrArg (fun f => f.hom x) h

end Aoki
