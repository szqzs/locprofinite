import Aoki.Cech.NonzeroClass
import Aoki.Sheaf.CardinalDimension
import Aoki.Topology.GeometrySize

/-!
# Sharp size bounds for nonzero ordinary sheaf cohomology

The example is the actual punctured involution quotient, with its quotient
topology. The cohomology group is Mathlib's ordinary abelian sheaf cohomology.
The additional identification as a repeated degree-one cup power is separate.
-/

noncomputable section

namespace Aoki

open CategoryTheory TopologicalSpace Geometry Cech

local instance (r : ℕ) : HasExt.{0}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology (U AlephBase r))
      AddCommGrpCat.{0}) := hasExtAbelianSheaves (TopCat.of (U AlephBase r))

/-- A locally profinite Hausdorff example of the exact sharp size in each
positive degree, carrying nonzero ordinary constant-F₂ sheaf cohomology. -/
theorem sharp_cohomological_example (r : ℕ) (hr : 0 < r) :
    Cardinal.mk (U AlephBase r) = Cardinal.aleph r ∧
    Topology.weight (U AlephBase r) = Cardinal.aleph r ∧
    ∃ α : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := AlephBase) (n := r)) r,
      α ≠ 0 := by
  refine ⟨mk_U r, weight_U r, ?_⟩
  cases r with
  | zero => omega
  | succ n => exact ⟨topPowerClass AlephBase (n + 1), aleph_topPowerClass_ne_zero n⟩

/-- The constructed example has cohomological dimension at most its index,
for all abelian coefficient sheaves. -/
theorem sharp_example_vanishing (r : ℕ)
    (M : TopCat.Sheaf AddCommGrpCat (TopCat.of (U AlephBase r)))
    (d : ℕ) (hd : r < d) (α : CategoryTheory.Sheaf.H.{0} M d) : α = 0 :=
  quotient_sheaf_cohomology_eq_zero_above AlephBase r M d hd α

universe u

/-- Nonzero ordinary cohomology in positive degree forces both size bounds
on every locally profinite Hausdorff space, with arbitrary abelian coefficients. -/
theorem cohomological_size_bounds {X : TopCat.{u}} [T2Space X]
    [TotallyDisconnectedSpace X] [LocallyCompactSpace X] {r : ℕ} (hr : 0 < r)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (α : CategoryTheory.Sheaf.H M r)
    (hα : α ≠ 0) :
    Cardinal.aleph r ≤ Cardinal.mk X ∧ Cardinal.aleph r ≤ Topology.weight X :=
  ⟨aleph_le_cardinal_of_nonzero_sheaf_cohomology hr M α hα,
    aleph_le_weight_of_nonzero_sheaf_cohomology hr M α hα⟩

end Aoki
