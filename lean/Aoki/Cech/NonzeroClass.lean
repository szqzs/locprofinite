import Aoki.Cech.CochainValues
import Aoki.Cech.SheafResolution
import Aoki.Sheaf.CohomologyVanishing
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Nonzero actual sheaf-cohomology classes

The finite projective resolution converts the explicitly nonboundary top
cochain into a nonzero class in Mathlib's ordinary sheaf cohomology.
The identification of this class as a cup power is a further theorem.
-/

noncomputable section

namespace Aoki.Cech

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Geometry

set_option backward.isDefEq.respectTransparency false

variable (A : ℕ → Type) (n : ℕ)
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

local instance : HasExt.{0}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology (U A n)) AddCommGrpCat.{0}) :=
  hasExtAbelianSheaves (TopCat.of (U A n))

/-- The actual finite projective resolution, with the constant integral sheaf
as augmentation target exactly as in the definition of `Sheaf.H`. -/
def quotientIntegralResolution :
    ProjectiveResolution ((constantSheaf (Opens.grothendieckTopology (U A n))
      AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))) := by
  let P := freeOpenProjectiveResolution (X := TopCat.of (U A n)) chartOpen
    iSup_chartOpen (fun k s => by
      rw [faceOpen_chartOpen]
      exact projective_freeOpen_chartIntersection _
        (Finset.Nonempty.image Finset.univ_nonempty s))
  exact
    { complex := P.complex
      projective := P.projective
      π := P.π ≫ (ChainComplex.single₀ _).map (freeOpenTopIso (TopCat.of (U A n))).hom
      quasiIso := by infer_instance }

@[simp] theorem quotientIntegralResolution_complex :
    (quotientIntegralResolution A n).complex =
      orderedComplex chartOpen (freeOpenFunctor (TopCat.of (U A n))) := rfl

/-- The class of the explicit degree-one transition cocycle. -/
def degreeOneClass : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) 1 :=
  (quotientIntegralResolution A n).extMk transitionCochain 2 rfl
    (by simpa using (transitionCochain_cocycle (A := A) (n := n)))

/-- The class of the explicit top-degree product cochain in actual ordinary
sheaf cohomology. -/
def topPowerClass : CategoryTheory.Sheaf.H.{0} (constantF2Sheaf (A := A) (n := n)) n :=
  (quotientIntegralResolution A n).extMk (powerCochain n) (n + 1) rfl
    (by simpa using (powerCochain_top_cocycle (A := A) (n := n)))

/-- Nonvanishing in every positive degree, now in actual sheaf cohomology. -/
theorem aleph_topPowerClass_ne_zero (n : ℕ) : topPowerClass AlephBase (n + 1) ≠ 0 := by
  intro h
  have hb := ((quotientIntegralResolution AlephBase (n + 1)).extMk_eq_zero_iff
    (powerCochain (n + 1)) (n + 2) rfl
    (by simpa using (powerCochain_top_cocycle (A := AlephBase) (n := n + 1))) n rfl).mp h
  exact aleph_powerCochain_not_boundary n (by simpa using hb)

/-- The constructed space has no cohomology beyond the top degree. -/
theorem quotient_sheaf_cohomology_eq_zero_above
    (M : TopCat.Sheaf AddCommGrpCat (TopCat.of (U A n))) (d : ℕ) (hd : n < d)
    (a : CategoryTheory.Sheaf.H.{0} M d) : a = 0 := by
  obtain ⟨f, hf, rfl⟩ := (quotientIntegralResolution A n).extMk_surjective a (d + 1) rfl
  have hz : IsZero ((quotientIntegralResolution A n).complex.X d) :=
    orderedTerm_isZero chartOpen (freeOpenFunctor (TopCat.of (U A n))) hd
  have hfzero : f = 0 := hz.eq_of_src f 0
  subst f
  exact (quotientIntegralResolution A n).extMk_zero _ _

end Aoki.Cech
