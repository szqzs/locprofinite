import Aoki.Topology.Axis
import Aoki.Topology.CompactWeight

/-!
# The cardinality and weight of the actual punctured quotient

For the discrete bases of cardinalities `aleph 0, ..., aleph n`, the space
`U AlephBase n` has both cardinality and topological weight `aleph n`.
-/

noncomputable section

namespace Aoki.Geometry

open Cardinal

instance (n : ℕ) : TopologicalSpace (AlephBase n) := ⊥

instance (n : ℕ) : DiscreteTopology (AlephBase n) := ⟨rfl⟩

@[simp] theorem mk_onePoint_alephBase (n : ℕ) :
    #(OnePoint (AlephBase n × Bool)) = aleph (n : Ordinal) := by
  change #(Option (AlephBase n × Bool)) = _
  rw [Cardinal.mk_option, mk_alephBase_bool]
  exact Cardinal.add_eq_left (aleph0_le_aleph _)
    (one_le_aleph0.trans (aleph0_le_aleph _))

theorem mk_compactProduct_le (n : ℕ) :
    #(CompactProduct AlephBase n) ≤ aleph (n : Ordinal) := by
  change #((i : Fin (n + 1)) → OnePoint (AlephBase i × Bool)) ≤ _
  rw [Cardinal.mk_pi]
  calc
    Cardinal.prod (fun i : Fin (n + 1) => #(OnePoint (AlephBase i × Bool)))
        ≤ Cardinal.prod (fun _ : Fin (n + 1) => aleph (n : Ordinal)) := by
          apply Cardinal.prod_le_prod
          intro i
          rw [mk_onePoint_alephBase, aleph_le_aleph]
          exact_mod_cast Nat.le_of_lt_succ i.isLt
    _ = aleph (n : Ordinal) ^ (n + 1) := by
      rw [Cardinal.prod_const', Cardinal.mk_fintype, Fintype.card_fin]
      norm_cast
    _ ≤ aleph (n : Ordinal) := Cardinal.power_nat_le (aleph0_le_aleph _)

theorem mk_compactQuotient_le (n : ℕ) :
    #(CompactQuotient AlephBase n) ≤ aleph (n : Ordinal) :=
  (Cardinal.mk_le_of_surjective (Quotient.mk_surjective)).trans (mk_compactProduct_le n)

theorem mk_U_le (n : ℕ) : #(U AlephBase n) ≤ aleph (n : Ordinal) :=
  (Cardinal.mk_le_of_injective (Subtype.val_injective)).trans (mk_compactQuotient_le n)

/-- The actual quotient space has the claimed sharp cardinality. -/
@[simp] theorem mk_U (n : ℕ) : #(U AlephBase n) = aleph (n : Ordinal) := by
  apply le_antisymm (mk_U_le n)
  simpa using mk_base_le_mk_U (A := AlephBase) (Fin.last n)

theorem weight_compactProduct_le (n : ℕ) :
    Aoki.Topology.weight (CompactProduct AlephBase n) ≤ aleph (n : Ordinal) :=
  (Aoki.Topology.weight_le_max_mk (CompactProduct AlephBase n)).trans
    (max_le (aleph0_le_aleph _) (mk_compactProduct_le n))

theorem weight_compactQuotient_le (n : ℕ) :
    Aoki.Topology.weight (CompactQuotient AlephBase n) ≤ aleph (n : Ordinal) :=
  (Aoki.Topology.weight_le_of_open_quotient (CompactProduct AlephBase n)
    quotientMap isQuotientMap_quotient_mk' isOpenMap_quotientMap).trans
      (weight_compactProduct_le n)

theorem weight_U_le (n : ℕ) :
    Aoki.Topology.weight (U AlephBase n) ≤ aleph (n : Ordinal) :=
  (Aoki.Topology.weight_le_of_isInducing (CompactQuotient AlephBase n)
    Subtype.val _root_.Topology.IsEmbedding.subtypeVal.isInducing).trans
      (weight_compactQuotient_le n)

/-- The actual quotient space has the claimed sharp topological weight. -/
@[simp] theorem weight_U (n : ℕ) :
    Aoki.Topology.weight (U AlephBase n) = aleph (n : Ordinal) := by
  apply le_antisymm (weight_U_le n)
  simpa using Aoki.Topology.mk_le_weight_of_discrete_embedding (U AlephBase n)
    (axis (A := AlephBase) (Fin.last n)) (isEmbedding_axis (Fin.last n))

end Aoki.Geometry
