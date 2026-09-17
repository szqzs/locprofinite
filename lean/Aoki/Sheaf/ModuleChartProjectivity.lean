import Aoki.Sheaf.ChartProjectivity
import Aoki.Sheaf.ModuleFreeOpen

/-!
# Projectivity for module sheaves on the actual quotient cover

The geometric gauge-cell decomposition works with arbitrary commutative-ring
coefficients. Consequently every term of the ordered module Čech complex is
projective.
-/

noncomputable section

namespace Aoki.Geometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable (R : Type u) [CommRing R]
variable {A : ℕ → Type u} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- Every nonempty chart intersection represents a projective module sheaf. -/
theorem projective_freeOpenModule_chartIntersection
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Projective (freeOpenModule R (X := TopCat.of (U A n)) (chartIntersection I)) := by
  obtain ⟨i, hi⟩ := hI
  rw [chartIntersection_eq_iSup_cells I i hi]
  apply projective_freeOpenModule_disjoint_iSup
  · exact fun v => isCompact_cell v
  · intro v w hvw
    exact Opens.coe_disjoint.mp (cell_pairwiseDisjoint I i hi hvw)

set_option maxHeartbeats 800000 in
/-- The ordered quotient-cover complex with module coefficients has projective terms. -/
theorem quotientModuleCech_projective (k : ℕ) :
    Projective ((Cech.orderedComplex (chartOpen (A := A) (n := n))
      (freeOpenModuleFunctor R (TopCat.of (U A n)))).X k) := by
  let F := freeOpenModuleFunctor R (TopCat.of (U A n))
  have hproj : ∀ s : Cech.Face (n + 1) k,
      Projective (freeOpenModule R (X := TopCat.of (U A n))
        (Cech.faceOpen (chartOpen (A := A) (n := n)) s)) := by
    intro s
    rw [faceOpen_chartOpen]
    exact projective_freeOpenModule_chartIntersection R _
      (Finset.Nonempty.image Finset.univ_nonempty s)
  letI : ∀ s : Cech.Face (n + 1) k,
      Projective (F.obj (Cech.faceOpen (chartOpen (A := A) (n := n)) s)) := hproj
  change Projective (∐ fun s : Cech.Face (n + 1) k => F.obj (Cech.faceOpen chartOpen s))
  constructor
  intro M Q f p hp
  refine ⟨Sigma.desc (fun s => Projective.factorThru
    (Sigma.ι (fun t : Cech.Face (n + 1) k => F.obj (Cech.faceOpen chartOpen t)) s ≫ f) p), ?_⟩
  apply Sigma.hom_ext
  intro s
  simp only [Sigma.ι_desc_assoc, Projective.factorThru_comp]

end Aoki.Geometry
