import Aoki.Cech.CupNonvanishing
import Aoki.CohomologicalSharpness

/-!
# The sharp answer to Aoki's Question 2.14

For every positive integer `r`, the explicit punctured diagonal-involution
quotient is a Hausdorff locally profinite space of cardinality and weight
`aleph r`. Its explicit degree-one constant-F₂ class has nonzero `r`-th cup
power and zero `(r+1)`-st cup power. Nonzero degree-`r` sheaf cohomology on any
Hausdorff locally profinite space forces both of these size bounds.

The cup operation is the actual Yoneda product of module sheaves transported
through the proved comparison with ordinary abelian sheaf cohomology. All
geometric, exactness, projectivity, cocycle, and product identifications are
proved in the imported development; none are hypotheses of the final theorem.
-/

noncomputable section

namespace Aoki

open CategoryTheory TopologicalSpace Geometry Cech

local instance (r : ℕ) : HasExt.{0}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology (U AlephBase r))
      AddCommGrpCat.{0}) := hasExtAbelianSheaves (TopCat.of (U AlephBase r))

/-- The sharp locally profinite examples: the exhibited degree-one class has
nonzero `r`-th power and zero `(r+1)`-st power, at size and weight `aleph r`. -/
theorem aoki_question_2_14 (r : ℕ) (hr : 0 < r) :
    T2Space (U AlephBase r) ∧
    TotallyDisconnectedSpace (U AlephBase r) ∧
    LocallyCompactSpace (U AlephBase r) ∧
    Cardinal.mk (U AlephBase r) = Cardinal.aleph r ∧
    Topology.weight (U AlephBase r) = Cardinal.aleph r ∧
    ∃ η : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := AlephBase) (n := r)) 1,
      cupPower η r ≠ 0 ∧ cupPower η (r + 1) = 0 := by
  refine ⟨inferInstance, inferInstance, inferInstance, mk_U r, weight_U r, ?_⟩
  exact ⟨degreeOneClass AlephBase r, aleph_cupPower_ne_zero r hr,
    cupPower_next_eq_zero (A := AlephBase) (n := r)⟩

universe u

/-- The universal cardinality and weight lower bounds, with arbitrary abelian
coefficients; thus the sizes in `aoki_question_2_14` are minimal. -/
theorem aoki_question_2_14_minimality {X : TopCat.{u}} [T2Space X]
    [TotallyDisconnectedSpace X] [LocallyCompactSpace X] {r : ℕ} (hr : 0 < r)
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (α : CategoryTheory.Sheaf.H M r)
    (hα : α ≠ 0) :
    Cardinal.aleph r ≤ Cardinal.mk X ∧ Cardinal.aleph r ≤ Topology.weight X :=
  cohomological_size_bounds hr M α hα

/-- All abelian coefficient sheaves on the explicit example have zero
cohomology in degrees larger than its index. -/
theorem aoki_example_cohomology_above (r : ℕ)
    (M : TopCat.Sheaf AddCommGrpCat (TopCat.of (U AlephBase r)))
    (d : ℕ) (hd : r < d) (α : CategoryTheory.Sheaf.H.{0} M d) : α = 0 :=
  sharp_example_vanishing r M d hd α

end Aoki
