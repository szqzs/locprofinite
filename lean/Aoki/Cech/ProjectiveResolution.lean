import Aoki.Cech.Resolution

/-! # Packaging exact ordered complexes as projective resolutions -/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Aoki.Cech
universe u v w
variable {X : Type w} [TopologicalSpace X]
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {N : ℕ} (U : Fin N → Opens X) (F : Opens X ⥤ C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the augmented sequence is precisely the missing quasi-isomorphism condition. -/
theorem orderedAugmentation_quasiIso
    (hexact : ∀ n, (orderedComplex U F).ExactAt (n + 1))
    (haug : (ShortComplex.mk (orderedDifferential U F 0) (orderedAugmentation U F)
      (orderedDifferential_comp_augmentation U F)).Exact)
    [Epi (orderedAugmentation U F)] : QuasiIso (orderedAugmentationHom U F) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · constructor
      · dsimp only [HomologicalComplex.shortComplexFunctor']
        simpa only [orderedComplex_X, orderedComplex_d, orderedAugmentationHom_f_zero,
          ChainComplex.single₀_obj_zero] using haug
      · simpa only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
          orderedAugmentationHom_f_zero] using (inferInstance : Epi (orderedAugmentation U F))
    · simp
    · simp
    · simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact hexact n

/-- A bounded ordered projective resolution, once its augmented exactness is established. -/
def orderedProjectiveResolution
    (hproj : ∀ n (s : Face N n), Projective (F.obj (faceOpen U s)))
    (hexact : ∀ n, (orderedComplex U F).ExactAt (n + 1))
    (haug : (ShortComplex.mk (orderedDifferential U F 0) (orderedAugmentation U F)
      (orderedDifferential_comp_augmentation U F)).Exact)
    [Epi (orderedAugmentation U F)] : ProjectiveResolution (F.obj ⊤) where
  complex := orderedComplex U F
  projective n := by
    letI : ∀ s : Face N n, Projective (F.obj (faceOpen U s)) := hproj n
    change Projective (orderedTerm U F n)
    constructor
    intro M Q f p hp
    refine ⟨Sigma.desc (fun s => Projective.factorThru
      (Sigma.ι (fun t : Face N n => F.obj (faceOpen U t)) s ≫ f) p), ?_⟩
    apply Sigma.hom_ext
    intro s
    simp only [Sigma.ι_desc_assoc, Projective.factorThru_comp]
  π := orderedAugmentationHom U F
  quasiIso := orderedAugmentation_quasiIso U F hexact haug

end Aoki.Cech
