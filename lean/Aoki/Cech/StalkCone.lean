import Aoki.Cech.AugmentedCone

/-! # Point-supported coefficients give exact ordered Čech complexes -/

noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace Aoki.Cech
universe u v w

variable {X : Type w} [TopologicalSpace X]
variable {N : ℕ} (U : Fin N → Opens X)

/-- At a point of a finite open cover there is a least active cover index. -/
theorem exists_least_cover_index (hcover : iSup U = ⊤) (x : X) :
    ∃ p : Fin N, x ∈ U p ∧ ∀ i, x ∈ U i → p ≤ i := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter fun i => x ∈ U i
  have hmem : x ∈ iSup U := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hmem
  have hS : S.Nonempty := ⟨i, by simp [S, hi]⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2, ?_⟩
  intro j hj
  exact S.min'_le j (by simp [S, hj])

section Coefficients
variable {C : Type u} [Category.{v} C]
variable (F : Opens X ⥤ C) (x : X)
variable (hzero : ∀ W : Opens X, x ∉ W → IsZero (F.obj W))
variable (hiso : ∀ {V W : Opens X} (i : V ⟶ W), x ∈ V → IsIso (F.map i))

include hzero hiso in
/-- Point-supported coefficients satisfy the cone conditions at the least active vertex. -/
theorem hasConeCoefficients_of_support (p : Fin N) (hp : x ∈ U p)
    (hmin : ∀ i, x ∈ U i → p ≤ i) : HasConeCoefficients U F p := by
  constructor
  · intro n s hs
    apply hzero
    intro hx
    have hi : x ∈ U (s 0) := (iInf_le (fun j => U (s j)) 0) hx
    exact (not_le_of_gt hs) (hmin _ hi)
  · intro n s hs
    by_cases hx : x ∈ faceOpen U s
    · apply hiso
      rw [faceOpen_prepend]
      exact ⟨hp, hx⟩
    · exact (hzero _ (fun h => hx (faceOpen_prepend_le U p s hs h))).isIso (hzero _ hx) _

include hiso in
/-- The coefficient at the cone vertex maps isomorphically to the augmentation coefficient. -/
theorem vertexAugmentation_isIso_of_support (p : Fin N) (hp : x ∈ U p) :
    IsIso (F.map (homOfLE (show faceOpen U (vertexFace p) ≤ ⊤ from le_top))) := by
  apply hiso
  change x ∈ ⨅ _ : Fin 1, U p
  simpa using hp

end Coefficients

section Exactness
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (F : Opens X ⥤ C) (x : X)
variable (hzero : ∀ W : Opens X, x ∉ W → IsZero (F.obj W))
variable (hiso : ∀ {V W : Opens X} (i : V ⟶ W), x ∈ V → IsIso (F.map i))

include hzero hiso in
/-- The ordered complex of a cover is exact in positive degrees for point-supported coefficients. -/
theorem orderedComplex_exactAt_succ_of_support (hcover : iSup U = ⊤) (n : ℕ) :
    (orderedComplex U F).ExactAt (n + 1) := by
  obtain ⟨p, hp, hmin⟩ := exists_least_cover_index U hcover x
  exact orderedComplex_exactAt_succ U F p
    (hasConeCoefficients_of_support U F x hzero hiso p hp hmin) n

include hzero hiso in
/-- The augmentation is exact for point-supported coefficients. -/
theorem orderedAugmentation_exact_of_support (hcover : iSup U = ⊤) :
    (ShortComplex.mk (orderedDifferential U F 0) (orderedAugmentation U F)
      (orderedDifferential_comp_augmentation U F)).Exact := by
  obtain ⟨p, hp, hmin⟩ := exists_least_cover_index U hcover x
  letI := vertexAugmentation_isIso_of_support U F x hiso p hp
  exact orderedAugmentation_exact U F p
    (hasConeCoefficients_of_support U F x hzero hiso p hp hmin)

include hiso in
/-- The augmentation is an epimorphism for point-supported coefficients. -/
theorem orderedAugmentation_epi_of_support (hcover : iSup U = ⊤) :
    Epi (orderedAugmentation U F) := by
  obtain ⟨p, hp, _⟩ := exists_least_cover_index U hcover x
  letI := vertexAugmentation_isIso_of_support U F x hiso p hp
  constructor
  intro M f g h
  have hh := congrArg (fun k => coneAugmentationSection U F p ≫ k) h
  simpa only [← Category.assoc, coneAugmentationSection_comp, Category.id_comp] using hh

end Exactness
end Aoki.Cech
