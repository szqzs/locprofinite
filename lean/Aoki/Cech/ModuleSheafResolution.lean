import Aoki.Cech.StalkCone
import Aoki.Cech.MapComplex
import Aoki.Cech.ProjectiveResolution
import Aoki.Sheaf.ModuleFreeOpenStalk

/-!
# The ordered Čech resolution with module coefficients

The augmented ordered complex of the free module sheaves on a finite open
cover is exact. This is proved on every stalk using the explicit contraction at
the least active cover index. When its terms are projective, it is an actual
projective resolution of the free rank-one module sheaf on the whole space.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Aoki.Cech
universe u
variable (R : Type u) [CommRing R]
variable {X : TopCat.{u}} {N : ℕ} (U : Fin N → Opens X)

set_option maxHeartbeats 800000 in
/-- If the opens cover the space, the degree-zero augmentation is an epimorphism. -/
theorem epi_freeOpenModuleAugmentation_zero (hcover : iSup U = ⊤) :
    Epi (orderedAugmentation U (freeOpenModuleFunctor R X)) := by
  constructor
  intro M f g hfg
  apply (freeOpenModuleHomEquiv R (⊤ : Opens X) M).injective
  apply TopCat.Presheaf.IsSheaf.section_ext M.property
  intro x hx
  have hxcover : x ∈ iSup U := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
  let s : Face N 0 := vertexFace i
  refine ⟨faceOpen U s, le_top, ?_, ?_⟩
  · simpa [s] using hi
  · have h := congrArg (fun k =>
      Sigma.ι (fun t : Face N 0 => freeOpenModule R (faceOpen U t)) s ≫ k) hfg
    change (Sigma.ι (fun t : Face N 0 => (freeOpenModuleFunctor R X).obj (faceOpen U t)) s ≫
      orderedAugmentation U (freeOpenModuleFunctor R X)) ≫ f =
      (Sigma.ι (fun t : Face N 0 => (freeOpenModuleFunctor R X).obj (faceOpen U t)) s ≫
      orderedAugmentation U (freeOpenModuleFunctor R X)) ≫ g at h
    rw [ι_orderedAugmentation] at h
    have hs := congrArg (freeOpenModuleHomEquiv R (faceOpen U s) M) h
    change freeOpenModuleHomEquiv R (faceOpen U s) M
      (freeOpenModuleMap R (homOfLE (show faceOpen U s ≤ ⊤ from le_top)) ≫ f) =
      freeOpenModuleHomEquiv R (faceOpen U s) M
        (freeOpenModuleMap R (homOfLE (show faceOpen U s ≤ ⊤ from le_top)) ≫ g) at hs
    rw [freeOpenModuleHomEquiv_restrict, freeOpenModuleHomEquiv_restrict] at hs
    exact hs


/-- The ordered free-sheaf complex is exact in every positive degree. -/
theorem freeOpenModuleComplex_exactAt_succ (hcover : iSup U = ⊤) (n : ℕ) :
    (orderedComplex U (freeOpenModuleFunctor R X)).ExactAt (n + 1) := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    ((orderedComplex U (freeOpenModuleFunctor R X)).sc (n + 1))).2
  intro x
  have h := orderedComplex_exactAt_succ_of_support U (freeOpenModuleFunctor R X ⋙ moduleStalk R x) x
    (fun W hx => freeOpenModule_stalk_isZero R W x hx)
    (fun i hx => freeOpenModule_stalk_map_isIso R i x hx) hcover n
  exact h.of_iso (orderedComplexMapIso U (freeOpenModuleFunctor R X) (moduleStalk R x))

/-- Exactness at degree zero of the augmented free-sheaf complex. -/
theorem freeOpenModuleAugmentation_exact (hcover : iSup U = ⊤) :
    (ShortComplex.mk (orderedDifferential U (freeOpenModuleFunctor R X) 0)
      (orderedAugmentation U (freeOpenModuleFunctor R X))
      (orderedDifferential_comp_augmentation U (freeOpenModuleFunctor R X))).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  let G := moduleStalk R x
  have h := orderedAugmentation_exact_of_support U (freeOpenModuleFunctor R X ⋙ G) x
    (fun W hx => freeOpenModule_stalk_isZero R W x hx)
    (fun i hx => freeOpenModule_stalk_map_isIso R i x hx) hcover
  apply ShortComplex.exact_of_iso _ h
  refine ShortComplex.isoMk (orderedTermMapIso U (freeOpenModuleFunctor R X) G 1)
    (orderedTermMapIso U (freeOpenModuleFunctor R X) G 0) (Iso.refl _) ?_ ?_
  · exact (orderedDifferential_map U (freeOpenModuleFunctor R X) G 0).symm
  · exact (orderedAugmentation_map U (freeOpenModuleFunctor R X) G).trans (Category.comp_id _).symm

/-- The projective resolution attached to a finite cover whose intersections are projective. -/
def freeOpenModuleProjectiveResolution (hcover : iSup U = ⊤)
    (hproj : ∀ n (s : Face N n), Projective (freeOpenModule R (faceOpen U s))) :
    ProjectiveResolution (freeOpenModule R (⊤ : Opens X)) := by
  letI := epi_freeOpenModuleAugmentation_zero R U hcover
  exact orderedProjectiveResolution U (freeOpenModuleFunctor R X) hproj
    (freeOpenModuleComplex_exactAt_succ R U hcover) (freeOpenModuleAugmentation_exact R U hcover)

@[simp] theorem freeOpenModuleProjectiveResolution_complex (hcover : iSup U = ⊤)
    (hproj : ∀ n (s : Face N n), Projective (freeOpenModule R (faceOpen U s))) :
    (freeOpenModuleProjectiveResolution R U hcover hproj).complex =
      orderedComplex U (freeOpenModuleFunctor R X) := rfl

end Aoki.Cech
