import Aoki.Cech.OrderedCone

/-! # The augmentation of the ordered cone contraction -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace
namespace Aoki.Cech
universe u v w

theorem face_zero_eq_vertex {N : ℕ} (s : Face N 0) : s = vertexFace (s 0) := by
  apply DFunLike.ext
  intro j
  have : j = 0 := by apply Fin.ext; omega
  subst j
  rfl

@[simp] theorem delete_prepend_one {N : ℕ} (p : Fin N) (s : Face N 0) (h : p < s 0) :
    deleteFace (prependFace p s h) 1 = vertexFace p := by
  apply DFunLike.ext
  intro j
  have : j = 0 := by apply Fin.ext; omega
  subst j
  simp [vertexFace]

section Coefficients
variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

/-- The section of augmentation at the cone vertex. -/
def coneAugmentationSection (p : Fin N)
    [IsIso (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top)))] :
    F.obj ⊤ ⟶ orderedTerm U F 0 :=
  inv (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top))) ≫
    Sigma.ι (fun s : Face N 0 => F.obj (faceOpen U s)) (vertexFace p)

omit [Preadditive C] in
@[reassoc] theorem coneAugmentationSection_comp (p : Fin N)
    [IsIso (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top)))] :
    coneAugmentationSection U F p ≫ orderedAugmentation U F = 𝟙 _ := by
  simp [coneAugmentationSection]

/-- The remaining face of a coned edge agrees with its augmentation section. -/
@[reassoc] theorem contraction_secondFace_zero (p : Fin N)
    (hp : HasConeCoefficients U F p)
    [IsIso (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top)))]
    (s : Face N 0) (h : p < s 0) :
    Sigma.ι (fun t : Face N 0 => F.obj (faceOpen U t)) s ≫
      orderedContraction U F p hp 0 ≫ orderedFace U F 0 1 =
    Sigma.ι (fun t : Face N 0 => F.obj (faceOpen U t)) s ≫
      orderedAugmentation U F ≫ coneAugmentationSection U F p := by
  letI := hp.2 0 s h
  rw [ι_orderedContraction_lt_assoc U F p hp 0 s h, ι_orderedFace,
    ι_orderedAugmentation_assoc]
  have hl : faceOpen U (prependFace p s h) ≤ faceOpen U (vertexFace p) := by
    exact (faceOpen_le_delete U (prependFace p s h) 1).trans_eq
      (congrArg (faceOpen U) (delete_prepend_one p s h))
  rw [map_ι_congr U F (delete_prepend_one p s h) _ hl]
  dsimp only [coneAugmentationSection]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (IsIso.inv_comp_eq _).2
  rw [← Category.assoc]
  apply (IsIso.eq_comp_inv _).2
  simp only [← F.map_comp]
  congr 1

/-- The cone identity in degree zero includes the augmentation. -/
theorem orderedContraction_augmentation_identity (p : Fin N)
    (hp : HasConeCoefficients U F p)
    [IsIso (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top)))] :
    orderedContraction U F p hp 0 ≫ orderedDifferential U F 0 +
      orderedAugmentation U F ≫ coneAugmentationSection U F p =
        𝟙 (orderedTerm U F 0) := by
  apply Sigma.hom_ext
  intro s
  rcases lt_trichotomy (s 0) p with hs | hs | hs
  · exact (hp.1 0 s hs).eq_of_src _ _
  · have he : s = vertexFace p := by rw [face_zero_eq_vertex s, hs]
    subst s
    have hn : ¬ p < vertexFace p 0 := by simp [vertexFace]
    simp only [comp_add, Category.comp_id,
      ι_orderedContraction_not_lt_assoc U F p hp 0 (vertexFace p) hn,
      zero_comp, zero_add, ι_orderedAugmentation_assoc, coneAugmentationSection,
      IsIso.hom_inv_id_assoc]
  · simp only [comp_add, Category.comp_id]
    dsimp only [orderedDifferential, alternatingDifferential]
    simp only [comp_sum, comp_zsmul]
    erw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
      contraction_firstFace_lt U F p hp 0 s hs,
      contraction_secondFace_zero U F p hp s hs]
    exact neg_add_cancel_right _ _

end Coefficients

section Exactness
variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

/-- Cone coefficients make the augmented degree-zero sequence exact. -/
theorem orderedAugmentation_exact (p : Fin N) (hp : HasConeCoefficients U F p)
    [IsIso (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top)))] :
    (ShortComplex.mk (orderedDifferential U F 0) (orderedAugmentation U F)
      (orderedDifferential_comp_augmentation U F)).Exact :=
  exact_of_contracting_identity _ (orderedContraction U F p hp 0)
    (coneAugmentationSection U F p) (orderedContraction_augmentation_identity U F p hp)

end Exactness
end Aoki.Cech
