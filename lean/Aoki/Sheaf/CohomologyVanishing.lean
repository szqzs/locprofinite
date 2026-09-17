import Aoki.Sheaf.ProjectiveOpen
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Actual sheaf cohomology vanishing

These results concern Mathlib's `CategoryTheory.Sheaf.H`, defined as Ext from
the constant integral sheaf. In particular they establish the countable-cover
base case of the proposed cardinal induction for the sharp lower bound.
-/

noncomputable section

namespace Aoki

open CategoryTheory CategoryTheory.Abelian TopologicalSpace

universe u

/-- Fix the natural universe of Ext for abelian sheaves on a space. -/
instance hasExtAbelianSheaves (X : TopCat.{u}) :
    HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

variable {X : TopCat.{u}} [T2Space X] [TotallyDisconnectedSpace X]

omit [T2Space X] [TotallyDisconnectedSpace X] in
/-- A projective free sheaf on the whole space makes all positive-degree
ordinary sheaf cohomology vanish, for arbitrary abelian coefficients. -/
theorem sheaf_cohomology_eq_zero_of_projective_top
    (h : Projective (freeOpen (⊤ : Opens X)))
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 := by
  letI : Projective (C := CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) := Projective.of_iso (freeOpenTopIso X) h
  exact Ext.eq_zero_of_projective a

/-- Every profinite space has zero positive-degree sheaf cohomology. -/
theorem sheaf_cohomology_eq_zero_of_compact [CompactSpace X]
    (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 :=
  sheaf_cohomology_eq_zero_of_projective_top
    (projective_freeOpen_of_isCompact ⊤ isCompact_univ) M n a

/-- The same holds on a space covered by countably many compact opens. -/
theorem sheaf_cohomology_eq_zero_of_countable_compactOpen_cover
    (K : ℕ → Opens X) (hcompact : ∀ n, IsCompact (K n : Set X))
    (hcover : iSup K = ⊤) (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 := by
  apply sheaf_cohomology_eq_zero_of_projective_top _ M n a
  rw [← hcover]
  exact projective_freeOpen_countable_iSup K hcompact

/-- An arbitrarily indexed disjoint compact-open cover also gives vanishing. -/
theorem sheaf_cohomology_eq_zero_of_disjoint_compactOpen_cover
    {ι : Type u} (K : ι → Opens X) (hcompact : ∀ i, IsCompact (K i : Set X))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hcover : iSup K = ⊤) (M : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H M (n + 1)) : a = 0 := by
  apply sheaf_cohomology_eq_zero_of_projective_top _ M n a
  rw [← hcover]
  exact projective_freeOpen_disjoint_iSup K hcompact hdisj

end Aoki
