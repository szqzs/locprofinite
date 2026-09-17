import Aoki.Cech.CupCohomology
import Aoki.Cech.CupComparison
import Aoki.Cech.PowerOne

/-! # Nonvanishing of the actual repeated degree-one cup power -/

noncomputable section

namespace Aoki.Cech

open CategoryTheory CategoryTheory.Abelian TopologicalSpace Geometry Homological

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

local instance : HasExt.{0} (TopCat.Sheaf (ModuleCat F) (TopCat.of (U A n))) :=
  hasExtModuleSheaves F (TopCat.of (U A n))
local instance : HasExt.{0}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology (U A n)) AddCommGrpCat) :=
  hasExtAbelianSheaves (TopCat.of (U A n))

@[simp] theorem cupCochainEquiv_cupIterate (k : ℕ) :
    cupCochainEquiv (A := A) (n := n) k (cupIterate k) = powerCochain k :=
  cupIterate_comparison k

/-- The module degree-one class is precisely the original ordinary transition
class under the proved cohomology comparison. -/
theorem cupCohomologyAddEquiv_degreeOne :
    cupCohomologyAddEquiv (A := A) (n := n) 1 (cupExtClass 1) = degreeOneClass A n := by
  refine (cupCohomologyAddEquiv_extMk (A := A) (n := n) 0 (cupIterate 1)
    (by rw [quotientCupResolution_d]; exact cupIterate_cocycle 1)).trans ?_
  apply extMk_congr
  exact (cupCochainEquiv_cupIterate (A := A) (n := n) 1).trans powerCochain_one

/-- In top positive degree, the comparison identifies the module iterate with
the ordinary nonboundary class already proved nonzero. -/
theorem cupCohomologyAddEquiv_top (r : ℕ) :
    cupCohomologyAddEquiv (A := A) (n := r + 1) (r + 1) (cupExtClass (r + 1)) =
      topPowerClass A (r + 1) := by
  refine (cupCohomologyAddEquiv_extMk (A := A) (n := r + 1) r (cupIterate (r + 1))
    (by rw [quotientCupResolution_d]; exact cupIterate_cocycle (r + 1))).trans ?_
  apply extMk_congr
  exact cupCochainEquiv_cupIterate (A := A) (n := r + 1) (r + 1)

/-- The top class is the repeated cup power of the explicit degree-one class. -/
theorem cupPower_degreeOneClass_top (hn : 0 < n) :
    cupPower (degreeOneClass A n) n = topPowerClass A n := by
  cases n with
  | zero => omega
  | succ r =>
    rw [cupPower, ← cupCohomologyAddEquiv_degreeOne, AddEquiv.symm_apply_apply,
      yonedaPower_cupExtClass, cupCohomologyAddEquiv_top]

/-- The actual r-th cup power is nonzero for the sharp aleph-r example. -/
theorem aleph_cupPower_ne_zero (r : ℕ) (hr : 0 < r) :
    cupPower (degreeOneClass AlephBase r) r ≠ 0 := by
  rw [cupPower_degreeOneClass_top hr]
  cases r with
  | zero => omega
  | succ k => exact aleph_topPowerClass_ne_zero k

/-- The next cup power vanishes by the bounded projective resolution. -/
theorem cupPower_next_eq_zero :
    cupPower (degreeOneClass A n) (n + 1) = 0 :=
  quotient_sheaf_cohomology_eq_zero_above A n _ (n + 1) (by omega) _

end Aoki.Cech
