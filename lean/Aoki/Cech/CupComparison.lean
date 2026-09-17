import Aoki.Cech.CupProduct
import Aoki.Cech.ScalarComparison
import Aoki.Sheaf.ModuleConstantComparison

/-!
# The iterated chain lift and the explicit product cochains

The section comparison from module to abelian Čech cochains sends the
Alexander–Whitney iterates to the adjacent-transition product cochains.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Aoki.Cech

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Geometry

variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- A coefficient identification normalized on the local rank-one generator
identifies the iterated lift with the explicit product cochain. -/
theorem cupIterate_comparison_of_normalized
    (φ : underlyingModuleSheaf F
      (freeOpenModule F (X := TopCat.of (U A n)) (⊤ : Opens (U A n))) ⟶
        constantF2Sheaf (A := A) (n := n))
    (hφ : ∀ (W : Opens (U A n)) (q : W),
      coefficientSectionValue (freeOpenModule F (X := TopCat.of (U A n)) ⊤) φ W q
        (freeOpenModuleHomEquiv F (X := TopCat.of (U A n)) W _
          (freeOpenModuleMap F (X := TopCat.of (U A n)) (homOfLE (show W ≤ ⊤ from le_top)))) = 1)
    (k : ℕ) :
    moduleCechHomEquiv F (chartOpen (A := A) (n := n))
        (freeOpenModule F (X := TopCat.of (U A n)) ⊤) k (cupIterate k) ≫ φ =
      powerCochain k := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc]
  erw [ι_moduleCechHomEquiv, ι_powerCochain]
  apply (freeOpenHomEquiv (faceOpen chartOpen s) constantF2Sheaf).injective
  apply (constantSheafSectionAddEquiv (TopCat.of (U A n)) F (faceOpen chartOpen s)).injective
  apply LocallyConstant.ext
  intro q
  erw [coefficientSectionValue_comparison]
  rw [ι_cupIterate, coefficientSectionValue_locallyWeightedHom, hφ, mul_one]
  simp only [powerTransitionHom, Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Under the canonical coefficient identification, the iterated chain lift
is exactly the explicit adjacent-transition product cochain. -/
theorem cupIterate_comparison (k : ℕ) :
    moduleCechHomEquiv F (chartOpen (A := A) (n := n))
        (freeOpenModule F (X := TopCat.of (U A n)) ⊤) k (cupIterate k) ≫
      (underlyingFreeOpenModuleTopIso F (TopCat.of (U A n))).hom = powerCochain k := by
  apply cupIterate_comparison_of_normalized
  intro W q
  exact freeOpenModuleTopSectionAddEquiv_generator F (TopCat.of (U A n)) W q

end Aoki.Cech
