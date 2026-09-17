import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Spectral.Prespectral
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Weight and the number of compact opens

The weight is the least cardinality of a topological basis. A locally compact
Hausdorff totally disconnected space has a basis of compact opens. Its compact
opens are finite unions of members of any basis, which gives the cardinal bound
needed for the weight version of the cohomological lower bound.
-/

noncomputable section

namespace Aoki.Topology

open Set TopologicalSpace Cardinal

universe u

variable (X : Type u) [TopologicalSpace X]

/-- The least cardinality of a basis of the given topology. -/
def weight : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ B : Set (Set X), IsTopologicalBasis B ∧ #B = κ}

theorem exists_basis_card_eq_weight :
    ∃ B : Set (Set X), IsTopologicalBasis B ∧ #B = weight X := by
  change sInf {κ : Cardinal.{u} | ∃ B : Set (Set X), IsTopologicalBasis B ∧ #B = κ} ∈
    {κ : Cardinal.{u} | ∃ B : Set (Set X), IsTopologicalBasis B ∧ #B = κ}
  apply csInf_mem
  exact ⟨_, {U | IsOpen U}, isTopologicalBasis_opens, rfl⟩

theorem weight_le_card_basis {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    weight X ≤ #B :=
  csInf_le' ⟨B, hB, rfl⟩

variable {Y : Type u} [TopologicalSpace Y]

/-- Passing to an induced topology does not increase weight. -/
theorem weight_le_of_isInducing (f : Y → X) (hf : _root_.Topology.IsInducing f) :
    weight Y ≤ weight X := by
  obtain ⟨B, hB, hcard⟩ := exists_basis_card_eq_weight X
  exact (weight_le_card_basis Y (hB.isInducing hf)).trans
    (hcard ▸ Cardinal.mk_image_le)

/-- An open quotient map does not increase weight. -/
theorem weight_le_of_open_quotient (f : X → Y)
    (hf : _root_.Topology.IsQuotientMap f) (ho : IsOpenMap f) :
    weight Y ≤ weight X := by
  obtain ⟨B, hB, hcard⟩ := exists_basis_card_eq_weight X
  exact (weight_le_card_basis Y (hB.isQuotientMap hf ho)).trans
    (hcard ▸ Cardinal.mk_image_le)

/-- A discrete space needs at least one different basic neighborhood per point. -/
theorem mk_le_weight_of_discrete [DiscreteTopology X] : #X ≤ weight X := by
  classical
  obtain ⟨B, hB, hcard⟩ := exists_basis_card_eq_weight X
  have hex : ∀ x : X, ∃ V : B, x ∈ (V : Set X) ∧ (V : Set X) ⊆ {x} := by
    intro x
    obtain ⟨V, hV, hxV, hsub⟩ := hB.exists_subset_of_mem_open (Set.mem_singleton x)
      (isOpen_discrete {x})
    exact ⟨⟨V, hV⟩, hxV, hsub⟩
  choose f hx hf using hex
  have hinj : Function.Injective f := by
    intro x y h
    have : x ∈ (f y : Set X) := h ▸ hx x
    exact hf y this
  exact hcard ▸ Cardinal.mk_le_of_injective hinj

/-- A discrete embedded subspace supplies a lower bound for weight. -/
theorem mk_le_weight_of_discrete_embedding [DiscreteTopology Y] (f : Y → X)
    (hf : _root_.Topology.IsEmbedding f) : #Y ≤ weight X :=
  (mk_le_weight_of_discrete Y).trans (weight_le_of_isInducing X f hf.isInducing)

variable {X}

/-- The compact opens form a basis in a locally profinite Hausdorff space. -/
theorem isTopologicalBasis_compactOpen [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U} := by
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1)
  intro x U hx hU
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVK⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨V, ⟨hV.isOpen, hK.of_isClosed_subset hV.isClosed
    (hVK.trans interior_subset)⟩, hxV, hVK.trans (interior_subset.trans hKU)⟩

/-- An explicit compact-open cover indexed by the points of the space. -/
theorem exists_point_indexed_compactOpen_cover [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    ∃ K : X → Opens X, (∀ x, IsCompact (K x : Set X)) ∧ iSup K = ⊤ := by
  classical
  have hex : ∀ x : X, ∃ K : Opens X, IsCompact (K : Set X) ∧ x ∈ K := by
    intro x
    obtain ⟨V, hV, hxV, _⟩ := isTopologicalBasis_compactOpen.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV.1⟩, hV.2, hxV⟩
  choose K hK hxK using hex
  refine ⟨K, hK, top_unique ?_⟩
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hxK x⟩

/-- Finite subsets of an arbitrary type have cardinality at most its infinite
cardinal envelope. This includes finite and empty bases. -/
theorem mk_finset_le_max (α : Type u) : #(Finset α) ≤ max ℵ₀ #α := by
  classical
  exact (Cardinal.mk_le_of_surjective (List.toFinset_surjective (α := α))).trans
    (Cardinal.mk_list_le_max α)

/-- Every compact open is determined by a finite subset of any topological basis. -/
theorem mk_compactOpens_le_basis {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    #(CompactOpens X) ≤ max ℵ₀ #B := by
  classical
  have hex : ∀ K : CompactOpens X, ∃ s : Finset B, (K : Set X) = (s : Set B).sUnion :=
    fun K => eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open B hB K
      K.isCompact K.isOpen
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro K L h
    apply SetLike.coe_injective
    rw [hf K, hf L, h]
  exact (Cardinal.mk_le_of_injective hinj).trans (mk_finset_le_max B)

theorem mk_compactOpens_le_weight : #(CompactOpens X) ≤ max ℵ₀ (weight X) := by
  obtain ⟨B, hB, hcard⟩ := exists_basis_card_eq_weight X
  simpa [hcard] using mk_compactOpens_le_basis hB

/-- All compact opens cover a locally profinite Hausdorff space. -/
theorem iSup_compactOpens_eq_top [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    (⨆ K : CompactOpens X, K.toOpens) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨V, hV, hxV, _⟩ := isTopologicalBasis_compactOpen.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV.2⟩, hV.1⟩, hxV⟩

end Aoki.Topology
