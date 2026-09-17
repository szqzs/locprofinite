import Mathlib.Topology.Compactification.OnePoint.Basic
import Aoki.AlmostConstant

/-!
# Almost-constant functions and one-point compactifications

The topology bridge used in the Aoki construction: a map from a discrete space
to a discrete target extends continuously across the point at infinity exactly
when it is constant outside a finite set.
-/

namespace Aoki

open Filter Topology

universe u v

/-- The prescribed extension taking value `c` at infinity.
`OnePoint.elim` is the `Option.elim` recursor for the one-point compactification. -/
def onePointExtension {X : Type u} {Y : Type v} (f : X → Y) (c : Y) : OnePoint X → Y :=
  fun z => z.elim c f

@[simp] theorem onePointExtension_coe {X : Type u} {Y : Type v}
    (f : X → Y) (c : Y) (x : X) : onePointExtension f c (x : OnePoint X) = f x := rfl

@[simp] theorem onePointExtension_infty {X : Type u} {Y : Type v}
    (f : X → Y) (c : Y) : onePointExtension f c OnePoint.infty = c := rfl

/-- For discrete source and target, continuity of the prescribed extension is
equivalent to eventual equality to its value at infinity along `cofinite`. -/
theorem continuous_onePointExtension_iff_eventually {X : Type u} {Y : Type v}
    [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : X → Y) (c : Y) :
    Continuous (onePointExtension f c) ↔ ∀ᶠ x in cofinite, f x = c := by
  rw [OnePoint.continuous_iff_from_discrete]
  simp only [onePointExtension_coe, onePointExtension_infty, nhds_discrete]
  exact Filter.tendsto_pure

/-- Finite exceptional sets and eventual constancy along `cofinite` agree. -/
theorem almostConstant_iff_exists_eventually {X : Type u} (f : X → F) :
    AlmostConstant f ↔ ∃ c : F, ∀ᶠ x in cofinite, f x = c := by
  classical
  constructor
  · rintro ⟨c, N, hN⟩
    exact ⟨c, N.eventually_cofinite_notMem.mono hN⟩
  · rintro ⟨c, hc⟩
    have hfinite : {x | f x ≠ c}.Finite := Filter.eventually_cofinite.mp hc
    refine ⟨c, hfinite.toFinset, ?_⟩
    intro x hx
    by_contra hne
    exact hx (hfinite.mem_toFinset.mpr hne)

/-- An almost-constant function has a continuous extension with a prescribed
eventual value at infinity, using the explicit `onePointExtension`. -/
theorem almostConstant_iff_exists_continuous_onePointExtension {X : Type u}
    [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [DiscreteTopology F] (f : X → F) :
    AlmostConstant f ↔ ∃ c : F, Continuous (onePointExtension f c) := by
  simp only [continuous_onePointExtension_iff_eventually,
    almostConstant_iff_exists_eventually]

/-- Restricting a continuous map on a one-point compactification to its discrete
part gives an almost-constant function. -/
theorem almostConstant_of_continuous_onePoint {X : Type u}
    [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [DiscreteTopology F]
    {g : OnePoint X → F} (hg : Continuous g) :
    AlmostConstant (fun x : X => g (x : OnePoint X)) := by
  apply (almostConstant_iff_exists_eventually _).mpr
  refine ⟨g OnePoint.infty, ?_⟩
  have h := (OnePoint.continuous_iff_from_discrete g).mp hg
  simpa only [nhds_discrete, Filter.tendsto_pure] using h

/-- Exact topological characterization of the algebraic `AlmostConstant`
predicate used in the nondecomposition proof. -/
theorem almostConstant_iff_exists_continuous_extension {X : Type u}
    [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [DiscreteTopology F] (f : X → F) :
    AlmostConstant f ↔
      ∃ g : OnePoint X → F, Continuous g ∧ ∀ x : X, g (x : OnePoint X) = f x := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := (almostConstant_iff_exists_continuous_onePointExtension f).mp hf
    exact ⟨onePointExtension f c, hc, fun _ => rfl⟩
  · rintro ⟨g, hg, hgf⟩
    simpa only [hgf] using almostConstant_of_continuous_onePoint hg

/-- Fixing all other coordinates in a continuous function gives the
section-wise almost-constant condition used in the boundary obstruction.
This is only an implication from joint continuity; no converse is asserted. -/
theorem almostConstant_sections_of_continuous {P : Type v} {X : Type u}
    [TopologicalSpace P] [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace F] [DiscreteTopology F]
    {g : P × OnePoint X → F} (hg : Continuous g) (p : P) :
    AlmostConstant (fun x : X => g (p, (x : OnePoint X))) := by
  apply almostConstant_of_continuous_onePoint (g := fun z : OnePoint X => g (p, z))
  exact hg.comp (continuous_const.prodMk continuous_id)

end Aoki
