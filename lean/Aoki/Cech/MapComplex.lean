import Aoki.Cech.Resolution
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Homology.Additive

/-!
# Applying an additive functor to the ordered Čech complex

The comparison is formed from finite-coproduct comparison isomorphisms. It
commutes with every face map, hence with the differential and augmentation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open TopologicalSpace

namespace Aoki.Cech

set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteCoproducts D]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)
variable (G : C ⥤ D) [G.Additive] [PreservesFiniteCoproducts G]

/-- The coproduct comparison in degree `n`. -/
def orderedTermMapIso (n : ℕ) :
    orderedTerm U (F ⋙ G) n ≅ G.obj (orderedTerm U F n) :=
  asIso (sigmaComparison G (fun s : Face N n => F.obj (faceOpen U s)))

omit [Preadditive C] [Preadditive D] [G.Additive] in
@[simp] theorem orderedTermMapIso_hom (n : ℕ) :
    (orderedTermMapIso U F G n).hom =
      sigmaComparison G (fun s : Face N n => F.obj (faceOpen U s)) := rfl

omit [Preadditive C] [Preadditive D] [G.Additive] in
/-- Each individual face commutes with the coproduct comparison. -/
theorem orderedFace_map (n : ℕ) (i : Fin (n + 2)) :
    orderedFace U (F ⋙ G) n i ≫ (orderedTermMapIso U F G n).hom =
      (orderedTermMapIso U F G (n + 1)).hom ≫ G.map (orderedFace U F n i) := by
  apply Sigma.hom_ext
  intro s
  rw [ι_orderedFace_assoc]
  dsimp only [orderedTermMapIso, asIso_hom, Functor.comp_map]
  change (G.map (F.map (homOfLE (faceOpen_le_delete U s i))) ≫
      Sigma.ι (fun t : Face N n => G.obj (F.obj (faceOpen U t))) (deleteFace s i) ≫
        sigmaComparison G (fun t : Face N n => F.obj (faceOpen U t))) =
    Sigma.ι (fun t : Face N (n + 1) => G.obj (F.obj (faceOpen U t))) s ≫
      sigmaComparison G (fun t : Face N (n + 1) => F.obj (faceOpen U t)) ≫
        G.map (orderedFace U F n i)
  erw [ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc]
  simp only [← G.map_comp, ι_orderedFace]

/-- Additivity carries the alternating differential through the comparison. -/
theorem orderedDifferential_map (n : ℕ) :
    orderedDifferential U (F ⋙ G) n ≫ (orderedTermMapIso U F G n).hom =
      (orderedTermMapIso U F G (n + 1)).hom ≫ G.map (orderedDifferential U F n) := by
  simp only [orderedDifferential, alternatingDifferential, sum_comp, zsmul_comp,
    G.map_sum, G.map_zsmul, comp_sum, comp_zsmul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun f => (-1 : ℤ) ^ (i : ℕ) • f)
    (orderedFace_map U F G n i))

/-- Applying `G` to the complex agrees with using the composite coefficient functor. -/
def orderedComplexMapIso :
    orderedComplex U (F ⋙ G) ≅
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj (orderedComplex U F) :=
  HomologicalComplex.Hom.isoOfComponents (orderedTermMapIso U F G) (by
    rintro i j (rfl : j + 1 = i)
    change (orderedTermMapIso U F G (j + 1)).hom ≫
      G.map ((orderedComplex U F).d (j + 1) j) =
      (orderedComplex U (F ⋙ G)).d (j + 1) j ≫ (orderedTermMapIso U F G j).hom
    rw [orderedComplex_d, orderedComplex_d]
    exact (orderedDifferential_map U F G j).symm)

@[simp] theorem orderedComplexMapIso_hom_f (n : ℕ) :
    (orderedComplexMapIso U F G).hom.f n = (orderedTermMapIso U F G n).hom := rfl

omit [Preadditive C] [Preadditive D] [G.Additive] in
/-- Compatibility with the degree-zero augmentation. -/
theorem orderedAugmentation_map :
    (orderedTermMapIso U F G 0).hom ≫ G.map (orderedAugmentation U F) =
      orderedAugmentation U (F ⋙ G) := by
  apply Sigma.hom_ext
  intro s
  rw [ι_orderedAugmentation]
  dsimp only [orderedTermMapIso, asIso_hom, Functor.comp_map]
  change Sigma.ι (fun s : Face N 0 => G.obj (F.obj (faceOpen U s))) s ≫
    sigmaComparison G (fun s : Face N 0 => F.obj (faceOpen U s)) ≫
      G.map (orderedAugmentation U F) = G.map (F.map (homOfLE le_top))
  erw [ι_comp_sigmaComparison_assoc]
  rw [← G.map_comp, ι_orderedAugmentation]

end Aoki.Cech
