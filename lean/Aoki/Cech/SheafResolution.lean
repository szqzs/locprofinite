import Aoki.Cech.StalkCone
import Aoki.Cech.MapComplex
import Aoki.Cech.ProjectiveResolution

/-!
# The integral ordered Čech resolution

The augmented ordered complex of the free abelian sheaves on a finite open
cover is exact. This is proved on every stalk using the explicit contraction at
the least active cover index. When its terms are projective, it is an actual
projective resolution of the free integral sheaf on the whole space.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Aoki.Cech
universe u
variable {X : TopCat.{u}} {N : ℕ} (U : Fin N → Opens X)

/-- The ordered free-sheaf complex is exact in every positive degree. -/
theorem freeOpenComplex_exactAt_succ (hcover : iSup U = ⊤) (n : ℕ) :
    (orderedComplex U (freeOpenFunctor X)).ExactAt (n + 1) := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    ((orderedComplex U (freeOpenFunctor X)).sc (n + 1))).2
  intro x
  have h := orderedComplex_exactAt_succ_of_support U (freeOpenFunctor X ⋙ abelianStalk x) x
    (fun W hx => freeOpen_stalk_isZero W x hx)
    (fun i hx => freeOpen_stalk_map_isIso i x hx) hcover n
  exact h.of_iso (orderedComplexMapIso U (freeOpenFunctor X) (abelianStalk x))

/-- Exactness at degree zero of the augmented free-sheaf complex. -/
theorem freeOpenAugmentation_exact (hcover : iSup U = ⊤) :
    (ShortComplex.mk (orderedDifferential U (freeOpenFunctor X) 0)
      (orderedAugmentation U (freeOpenFunctor X))
      (orderedDifferential_comp_augmentation U (freeOpenFunctor X))).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  let G := abelianStalk x
  have h := orderedAugmentation_exact_of_support U (freeOpenFunctor X ⋙ G) x
    (fun W hx => freeOpen_stalk_isZero W x hx)
    (fun i hx => freeOpen_stalk_map_isIso i x hx) hcover
  apply ShortComplex.exact_of_iso _ h
  refine ShortComplex.isoMk (orderedTermMapIso U (freeOpenFunctor X) G 1)
    (orderedTermMapIso U (freeOpenFunctor X) G 0) (Iso.refl _) ?_ ?_
  · exact (orderedDifferential_map U (freeOpenFunctor X) G 0).symm
  · exact (orderedAugmentation_map U (freeOpenFunctor X) G).trans (Category.comp_id _).symm

/-- The projective resolution attached to a finite cover whose intersections are projective. -/
def freeOpenProjectiveResolution (hcover : iSup U = ⊤)
    (hproj : ∀ n (s : Face N n), Projective (freeOpen (faceOpen U s))) :
    ProjectiveResolution (freeOpen (⊤ : Opens X)) := by
  letI := epi_freeOpenAugmentation_zero U hcover
  exact orderedProjectiveResolution U (freeOpenFunctor X) hproj
    (freeOpenComplex_exactAt_succ U hcover) (freeOpenAugmentation_exact U hcover)

@[simp] theorem freeOpenProjectiveResolution_complex (hcover : iSup U = ⊤)
    (hproj : ∀ n (s : Face N n), Projective (freeOpen (faceOpen U s))) :
    (freeOpenProjectiveResolution U hcover hproj).complex =
      orderedComplex U (freeOpenFunctor X) := rfl

end Aoki.Cech
