import Aoki.Cech.CupProduct
import Aoki.Cech.ModuleComparison
import Aoki.Homological.ExtMkComposition
import Aoki.Homological.ExtPowers

/-! # The computed cocycles are actual Yoneda powers

The projective resolution and its Alexander–Whitney lift are both constructed
from the quotient chart cover. No compatibility with Ext multiplication is
assumed: it is proved using the generic derived-category composition theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Aoki.Cech
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.Abelian
open TopologicalSpace Geometry Homological
variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

local instance : HasExt.{0} (TopCat.Sheaf (ModuleCat F) (TopCat.of (U A n))) :=
  hasExtModuleSheaves F (TopCat.of (U A n))

/-- The proved projective resolution associated to the concrete quotient cover. -/
abbrev quotientCupResolution : ProjectiveResolution
    (freeOpenModule F (X := TopCat.of (U A n)) ⊤) :=
  freeOpenModuleProjectiveResolution F chartOpen iSup_chartOpen
    (module_chart_face_projective F (A := A) (n := n))

@[simp] theorem quotientCupResolution_d (k : ℕ) :
    (quotientCupResolution (A := A) (n := n)).complex.d (k+1) k =
      orderedDifferential (chartOpen (A := A) (n := n))
        (freeOpenModuleFunctor F (TopCat.of (U A n))) k :=
  orderedComplex_d _ _ k

/-- Signed lift identity in the exact form used for Yoneda composition. -/
theorem cupLift_signed_sum (k : ℕ) :
    cupLift (A := A) (n := n) (k+1) ≫ quotientCupResolution.complex.d (k+1) k +
      quotientCupResolution.complex.d (k+2) (k+1) ≫ cupLift k = 0 := by
  erw [quotientCupResolution_d, quotientCupResolution_d, cupLift_chain_signed]
  exact add_neg_cancel _

/-- The class of the explicit iterated transition-product cochain. -/
def cupExtClass (k : ℕ) :
    Ext (freeOpenModule F (X := TopCat.of (U A n)) ⊤)
      (freeOpenModule F (X := TopCat.of (U A n)) ⊤) k :=
  (quotientCupResolution (A := A) (n := n)).extMk (cupIterate (A := A) (n := n) k)
    (k+1) rfl (by rw [quotientCupResolution_d]; exact cupIterate_cocycle k)

/-- Composition with the degree-one class advances the computed cup cochain. -/
theorem cupExtClass_comp (k : ℕ) :
    (cupExtClass (A := A) (n := n) 1).comp (cupExtClass k) (show 1+k=k+1 by omega) =
      cupExtClass (k+1) := by
  have hh := extMk_comp_of_lift (quotientCupResolution (A := A) (n := n))
    (quotientCupResolution (A := A) (n := n))
    (cupLift (A := A) (n := n)) (cupLift_signed_sum (A := A) (n := n))
    (cupIterate (A := A) (n := n) k)
    (by rw [quotientCupResolution_d]; exact cupIterate_cocycle k)
  exact hh

/-- Every positive power is represented by the actual explicit cup cochain. -/
theorem yonedaPower_cupExtClass (r : ℕ) :
    yonedaPower (cupExtClass (A := A) (n := n) 1) (r+1) = cupExtClass (r+1) := by
  induction r with
  | zero => exact yonedaPower_one _
  | succ r ih =>
    rw [yonedaPower_succ, ih]
    exact cupExtClass_comp (r+1)

end Aoki.Cech
