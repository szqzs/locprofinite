import Aoki.Topology.Intersections
import Aoki.Sheaf.ProjectiveOpen
import Aoki.Cech.Resolution

/-!
# Projective terms for the actual quotient cover

The gauge cells give disjoint compact-open covers of every nonempty finite
intersection. Thus the finite ordered Čech complex has projective terms.
-/

noncomputable section

namespace Aoki.Geometry

open CategoryTheory TopologicalSpace

universe u

variable {A : ℕ → Type u} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

omit [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)] in
theorem mem_finite_iInf_opens {X : Type u} [TopologicalSpace X]
    {ι : Type*} [Finite ι] (V : ι → Opens X) (x : X) :
    x ∈ (⨅ i, V i) ↔ ∀ i, x ∈ V i := by
  constructor
  · exact fun h i => (iInf_le V i) h
  · intro h
    let W : Opens X := ⟨⋂ i, (V i : Set X), isOpen_iInter_of_finite (fun i => (V i).isOpen)⟩
    have hW : W ≤ ⨅ i, V i := le_iInf fun i => Set.iInter_subset _ i
    exact hW (Set.mem_iInter.mpr h)

/-- The quotient chart as a bundled open. -/
def chartOpen (i : Fin (n + 1)) : Opens (U A n) := ⟨chart i, isOpen_chart i⟩

theorem iSup_chartOpen : (⨆ i, chartOpen (A := A) (n := n) i) = ⊤ := by
  apply top_unique
  intro q _
  obtain ⟨i, hi⟩ := charts_cover q
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- A nonempty finite intersection of quotient charts. -/
def chartIntersection (I : Finset (Fin (n + 1))) : Opens (U A n) :=
  ⨅ j : I, chartOpen j.1

theorem mem_chartIntersection (I : Finset (Fin (n + 1))) (q : U A n) :
    q ∈ chartIntersection I ↔ ∀ j ∈ I, q ∈ chart j := by
  change q ∈ (⨅ j : I, chartOpen j.1) ↔ _
  simp [mem_finite_iInf_opens, chartOpen]

/-- The actual gauge-cell decomposition, as an equality of bundled opens. -/
theorem chartIntersection_eq_iSup_cells (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) :
    chartIntersection (A := A) I = ⨆ v : GaugeLabel (A := A) I i hi, cellOpen v := by
  ext q
  change q ∈ chartIntersection I ↔ q ∈ ⨆ v : GaugeLabel (A := A) I i hi, cellOpen v
  rw [mem_chartIntersection]
  rw [Opens.mem_iSup]
  have h := Set.ext_iff.mp (cells_cover_intersection (A := A) I i hi) q
  simpa only [Set.mem_iUnion, Set.mem_setOf_eq, cellOpen, Opens.mem_mk] using h.symm

/-- Every nonempty chart intersection represents a projective abelian sheaf. -/
theorem projective_freeOpen_chartIntersection (I : Finset (Fin (n + 1)))
    (hI : I.Nonempty) :
    Projective (freeOpen (X := TopCat.of (U A n)) (chartIntersection I)) := by
  obtain ⟨i, hi⟩ := hI
  rw [chartIntersection_eq_iSup_cells I i hi]
  apply projective_freeOpen_disjoint_iSup
  · exact fun v => isCompact_cell v
  · intro v w hvw
    exact Opens.coe_disjoint.mp (cell_pairwiseDisjoint I i hi hvw)

/-- The ordered face intersection agrees with the intersection indexed by its image. -/
theorem faceOpen_chartOpen (k : ℕ) (s : Cech.Face (n + 1) k) :
    Cech.faceOpen (chartOpen (A := A)) s =
      chartIntersection (Finset.univ.image s) := by
  ext q
  change q ∈ Cech.faceOpen (chartOpen (A := A)) s ↔
    q ∈ chartIntersection (Finset.univ.image s)
  rw [mem_chartIntersection]
  simp only [Cech.faceOpen, mem_finite_iInf_opens,
    Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
  rfl

/-- Every term of the concrete ordered cover complex is projective. -/
theorem quotientCech_projective (k : ℕ) :
    Projective ((Cech.freeOpenComplex (X := TopCat.of (U A n)) chartOpen).X k) := by
  apply Cech.freeOpenComplex_projective
  intro j s
  rw [faceOpen_chartOpen]
  exact projective_freeOpen_chartIntersection _
    (Finset.Nonempty.image (Finset.univ_nonempty) s)

end Aoki.Geometry
