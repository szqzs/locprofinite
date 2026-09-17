import Aoki.Cech.OrderedComplex
import Aoki.Sheaf.FreeOpen
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Augmentation of the ordered Čech complex

This file constructs the augmentation and its chain-map condition, and records
projectivity of the chain objects when the represented open intersections are
projective. Exactness and a projective-resolution structure require separate
proofs; they are not hypotheses disguised as conclusions in these constructions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace

namespace Aoki.Cech

universe u v w

section Augmentation

variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

/-- The sum of the maps from the single opens to the entire space. -/
def orderedAugmentation : orderedTerm U F 0 ⟶ F.obj ⊤ :=
  Sigma.desc fun _ => F.map (homOfLE le_top)

omit [Preadditive C] in
@[reassoc, simp]
theorem ι_orderedAugmentation (s : Face N 0) :
    Sigma.ι (fun t : Face N 0 => F.obj (faceOpen U t)) s ≫ orderedAugmentation U F =
      F.map (homOfLE (show faceOpen U s ≤ ⊤ from le_top)) :=
  Sigma.ι_desc _ _

omit [Preadditive C] in
theorem orderedFace_comp_augmentation (i : Fin 2) :
    orderedFace U F 0 i ≫ orderedAugmentation U F =
      Sigma.desc (fun s : Face N 1 =>
        F.map (homOfLE (show faceOpen U s ≤ ⊤ from le_top))) := by
  apply Sigma.hom_ext
  intro s
  dsimp only [orderedFace, orderedAugmentation, orderedTerm]
  simp only [Category.assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
  rw [← F.map_comp]
  rfl

/-- The first differential lands in the kernel of the augmentation. -/
theorem orderedDifferential_comp_augmentation :
    orderedDifferential U F 0 ≫ orderedAugmentation U F = 0 := by
  dsimp only [orderedDifferential, alternatingDifferential]
  erw [Fin.sum_univ_two]
  simp only [
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    add_comp, neg_comp, orderedFace_comp_augmentation, add_neg_cancel]

variable [HasZeroObject C]

/-- The augmentation as a morphism to the complex concentrated in degree zero. -/
def orderedAugmentationHom :
    orderedComplex U F ⟶ (ChainComplex.single₀ C).obj (F.obj ⊤) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨orderedAugmentation U F, by
      rw [orderedComplex_d]
      exact orderedDifferential_comp_augmentation U F⟩

@[simp] theorem orderedAugmentationHom_f_zero :
    (orderedAugmentationHom U F).f 0 = orderedAugmentation U F :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end Augmentation

section FreeOpen

variable {X : TopCat.{u}} {N : ℕ} (U : Fin N → Opens X)

/-- The singleton face attached to a cover index. -/
def vertexFace (i : Fin N) : Face N 0 where
  toFun := fun _ => i
  inj' := by
    intro a b _
    apply Fin.ext
    omega
  map_rel_iff' := by
    intro a b
    constructor
    · intro _
      exact Fin.le_iff_val_le_val.mpr (by omega)
    · intro _
      exact le_rfl

@[simp] theorem faceOpen_vertexFace (i : Fin N) : faceOpen U (vertexFace i) = U i := by
  change (⨅ _ : Fin 1, U i) = U i
  simp

/-- The ordered chain complex of the integral free sheaves on the cover intersections. -/
def freeOpenComplex : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  orderedComplex U (freeOpenFunctor X)

/-- Its canonical augmentation to the free integral sheaf on the entire space. -/
def freeOpenAugmentation :
    freeOpenComplex U ⟶
      (ChainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
        (freeOpen (⊤ : Opens X)) :=
  orderedAugmentationHom U (freeOpenFunctor X)

set_option maxHeartbeats 800000 in
/-- If the opens cover the space, the degree-zero augmentation is an epimorphism. -/
theorem epi_freeOpenAugmentation_zero (hcover : iSup U = ⊤) :
    Epi (orderedAugmentation U (freeOpenFunctor X)) := by
  constructor
  intro M f g hfg
  apply (freeOpenHomEquiv (⊤ : Opens X) M).injective
  apply TopCat.Presheaf.IsSheaf.section_ext M.property
  intro x hx
  have hxcover : x ∈ iSup U := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
  let s : Face N 0 := vertexFace i
  refine ⟨faceOpen U s, le_top, ?_, ?_⟩
  · simpa [s] using hi
  · have h := congrArg (fun k =>
      Sigma.ι (fun t : Face N 0 => freeOpen (faceOpen U t)) s ≫ k) hfg
    change (Sigma.ι (fun t : Face N 0 => (freeOpenFunctor X).obj (faceOpen U t)) s ≫
      orderedAugmentation U (freeOpenFunctor X)) ≫ f =
      (Sigma.ι (fun t : Face N 0 => (freeOpenFunctor X).obj (faceOpen U t)) s ≫
      orderedAugmentation U (freeOpenFunctor X)) ≫ g at h
    rw [ι_orderedAugmentation] at h
    have hs := congrArg (freeOpenHomEquiv (faceOpen U s) M) h
    change freeOpenHomEquiv (faceOpen U s) M
      (freeOpenMap (homOfLE (show faceOpen U s ≤ ⊤ from le_top)) ≫ f) =
      freeOpenHomEquiv (faceOpen U s) M
        (freeOpenMap (homOfLE (show faceOpen U s ≤ ⊤ from le_top)) ≫ g) at hs
    rw [freeOpenHomEquiv_restrict, freeOpenHomEquiv_restrict] at hs
    exact hs

/-- Transport the augmentation to the constant integral sheaf. -/
def integralAugmentation :
    freeOpenComplex U ⟶
      (ChainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} X)).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) :=
  freeOpenAugmentation U ≫
    (ChainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{u} X)).map (freeOpenTopIso X).hom

/-- Finite coproducts of projective represented intersections are projective. -/
theorem freeOpenComplex_projective
    (hproj : ∀ n (s : Face N n), Projective (freeOpen (faceOpen U s)))
    (n : ℕ) : Projective ((freeOpenComplex U).X n) := by
  letI : ∀ s : Face N n, Projective ((freeOpenFunctor X).obj (faceOpen U s)) := hproj n
  change Projective (∐ fun s : Face N n => (freeOpenFunctor X).obj (faceOpen U s))
  constructor
  intro M Q f p hp
  refine ⟨Sigma.desc (fun s => Projective.factorThru
    (Sigma.ι (fun t : Face N n => (freeOpenFunctor X).obj (faceOpen U t)) s ≫ f) p), ?_⟩
  apply Sigma.hom_ext
  intro s
  simp only [Sigma.ι_desc_assoc, Projective.factorThru_comp]

/-- The augmented complex is bounded by the number of members of the cover. -/
theorem freeOpenComplex_isZero {k : ℕ} (h : N ≤ k) : IsZero ((freeOpenComplex U).X k) :=
  orderedComplex_isZero U (freeOpenFunctor X) h

end FreeOpen

end Aoki.Cech
