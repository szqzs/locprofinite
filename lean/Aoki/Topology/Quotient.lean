import Aoki.Functions
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The diagonal involution and its actual topological quotient
-/

namespace Aoki.Geometry

universe u

/-- The compact product before taking the diagonal quotient. -/
abbrev CompactProduct (A : ℕ → Type u) (n : ℕ) :=
  (i : Fin (n + 1)) → OnePoint (A i × Bool)

variable {A : ℕ → Type u} {n : ℕ}

/-- The unique point with every coordinate infinite. -/
def infty : CompactProduct A n := fun _ => OnePoint.infty

/-- Bit flip on a single discrete coordinate. -/
def coordinateFlip (x : A n × Bool) : A n × Bool := (x.1, !x.2)

@[simp] theorem coordinateFlip_coordinateFlip (x : A n × Bool) :
    coordinateFlip (coordinateFlip x) = x := by simp [coordinateFlip]

/-- Bit flip extended to fix the compactification point. -/
def onePointFlip : OnePoint (A n × Bool) → OnePoint (A n × Bool) :=
  OnePoint.map coordinateFlip

@[simp] theorem onePointFlip_infty :
    onePointFlip (A := A) (n := n) OnePoint.infty = OnePoint.infty := rfl

@[simp] theorem onePointFlip_coe (x : A n × Bool) :
    onePointFlip (x : OnePoint (A n × Bool)) = (coordinateFlip x : OnePoint (A n × Bool)) := rfl

@[simp] theorem onePointFlip_onePointFlip (x : OnePoint (A n × Bool)) :
    onePointFlip (onePointFlip x) = x := by
  cases x with
  | infty => rfl
  | coe x => simp

@[simp] theorem onePointFlip_eq_infty_iff (x : OnePoint (A n × Bool)) :
    onePointFlip x = OnePoint.infty ↔ x = OnePoint.infty := by
  cases x with
  | infty => simp
  | coe x => simp

theorem onePointFlip_eq_self_iff (x : OnePoint (A n × Bool)) :
    onePointFlip x = x ↔ x = OnePoint.infty := by
  cases x with
  | infty => simp
  | coe x =>
      rcases x with ⟨a, b⟩
      cases b <;> simp [coordinateFlip]

/-- Flip every finite-coordinate bit simultaneously. -/
def flip (x : CompactProduct A n) : CompactProduct A n :=
  fun i => onePointFlip (x i)

@[simp] theorem flip_flip (x : CompactProduct A n) : flip (flip x) = x := by
  funext i
  exact onePointFlip_onePointFlip (x i)

@[simp] theorem flip_infty : flip (infty : CompactProduct A n) = infty := rfl

theorem flip_eq_self_iff (x : CompactProduct A n) : flip x = x ↔ x = infty := by
  constructor
  · intro h
    funext i
    exact (onePointFlip_eq_self_iff (x i)).mp (congrFun h i)
  · rintro rfl
    exact flip_infty

section Topology

variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- The discrete-coordinate flip as a homeomorphism. -/
def coordinateFlipHomeomorph : (A n × Bool) ≃ₜ (A n × Bool) :=
  Homeomorph.ofDiscrete
    { toFun := coordinateFlip
      invFun := coordinateFlip
      left_inv := coordinateFlip_coordinateFlip
      right_inv := coordinateFlip_coordinateFlip }

/-- The compact product involution is a homeomorphism. -/
def flipHomeomorph : CompactProduct A n ≃ₜ CompactProduct A n :=
  Homeomorph.piCongrRight fun _ => coordinateFlipHomeomorph.onePointCongr

theorem continuous_flip : Continuous (flip : CompactProduct A n → CompactProduct A n) :=
  flipHomeomorph.continuous

instance : TotallySeparatedSpace (CompactProduct A n) := by
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro x y hxy
  have hex : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨C, hC, hxC, hyC⟩ := exists_isClopen_of_totally_separated hi
  exact ⟨(fun x => x i) ⁻¹' C, hC.preimage (continuous_apply i), hxC, hyC⟩

end Topology

/-- The genuine additive action of the two-element group. -/
instance : AddAction (ZMod 2) (CompactProduct A n) where
  vadd g x := if g = 0 then x else flip x
  zero_vadd x := by
    change (if (0 : ZMod 2) = 0 then x else flip x) = x
    simp
  add_vadd g h x := by
    change (if g + h = 0 then x else flip x) =
      (if g = 0 then (if h = 0 then x else flip x)
        else flip (if h = 0 then x else flip x))
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases g with rfl | rfl <;> rcases hcases h with rfl | rfl <;>
      simp [Aoki.self_add, flip_flip]

@[simp] theorem zero_vadd_eq (x : CompactProduct A n) : (0 : ZMod 2) +ᵥ x = x :=
  zero_vadd _ _

@[simp] theorem one_vadd_eq (x : CompactProduct A n) : (1 : ZMod 2) +ᵥ x = flip x := by
  change (if (1 : ZMod 2) = 0 then x else flip x) = flip x
  simp

@[simp] theorem vadd_infty (g : ZMod 2) : g +ᵥ (infty : CompactProduct A n) = infty := by
  change (if g = 0 then infty else flip infty) = infty
  split_ifs <;> rfl

/-- The orbit space, equipped with mathlib's quotient topology. -/
abbrev CompactQuotient (A : ℕ → Type u) (n : ℕ) :=
  Quotient (AddAction.orbitRel (ZMod 2) (CompactProduct A n))

def quotientMap : CompactProduct A n → CompactQuotient A n := Quotient.mk _

/-- Equality in the genuine orbit quotient is equality up to the diagonal flip. -/
theorem quotientMap_eq_iff (x y : CompactProduct A n) :
    quotientMap x = quotientMap y ↔ x = y ∨ x = flip y := by
  change Quotient.mk _ x = Quotient.mk _ y ↔ _
  rw [Quotient.eq, AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases g with rfl | rfl
    · exact Or.inl (by simpa using hg.symm)
    · exact Or.inr (by simpa using hg.symm)
  · rintro (h | h)
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩

@[simp] theorem quotientMap_eq_infty_iff (x : CompactProduct A n) :
    quotientMap x = quotientMap infty ↔ x = infty := by
  rw [quotientMap_eq_iff, flip_infty, or_self]

/-- Delete the image of the all-infinite point from the compact orbit space. -/
def U (A : ℕ → Type u) (n : ℕ) :=
  {q : CompactQuotient A n // q ≠ quotientMap infty}

section QuotientTopology

variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

instance : ContinuousConstVAdd (ZMod 2) (CompactProduct A n) where
  continuous_const_vadd g := by
    change Continuous (fun x : CompactProduct A n => if g = 0 then x else flip x)
    split_ifs
    · exact continuous_id
    · exact continuous_flip

instance : CompactSpace (CompactQuotient A n) := inferInstance

instance : T2Space (CompactQuotient A n) := by
  haveI (i : Fin (n + 1)) : T2Space (OnePoint (A i × Bool)) := inferInstance
  haveI : T2Space (CompactProduct A n) := Pi.t2Space
  haveI : LocallyCompactSpace (CompactProduct A n) := inferInstance
  haveI : ProperlyDiscontinuousVAdd (ZMod 2) (CompactProduct A n) := inferInstance
  exact t2Space_of_properlyDiscontinuousVAdd_of_t2Space

instance : TopologicalSpace (U A n) := inferInstanceAs (TopologicalSpace {q : CompactQuotient A n //
  q ≠ quotientMap infty})

instance : T2Space (U A n) := inferInstanceAs (T2Space {q : CompactQuotient A n //
  q ≠ quotientMap infty})

omit [∀ (i : ℕ), DiscreteTopology (A i)] in
theorem continuous_quotientMap : Continuous (quotientMap : CompactProduct A n → CompactQuotient A n) :=
  continuous_quot_mk

theorem isOpenMap_quotientMap : IsOpenMap (quotientMap : CompactProduct A n → CompactQuotient A n) :=
  isOpenMap_quotient_mk'_add

/-- A finite orbit quotient of this Stone space is again totally separated. -/
instance : TotallySeparatedSpace (CompactQuotient A n) := by
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro q r hqr
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      change quotientMap x ≠ quotientMap y at hqr
      have hxy : x ≠ y := fun h => hqr (congrArg quotientMap h)
      have hxflip : x ≠ flip y := fun h =>
        hqr ((quotientMap_eq_iff x y).mpr (Or.inr h))
      obtain ⟨C, hC, hxC, hyC⟩ := exists_isClopen_of_totally_separated hxy
      obtain ⟨D, hD, hxD, hyD⟩ := exists_isClopen_of_totally_separated hxflip
      refine ⟨quotientMap '' (C ∩ D), ?_, ⟨x, ⟨hxC, hxD⟩, rfl⟩, ?_⟩
      · exact ⟨((hC.inter hD).isClosed.isCompact.image continuous_quotientMap).isClosed,
          isOpenMap_quotientMap _ (hC.inter hD).isOpen⟩
      · rintro ⟨z, hz, hzy⟩
        rcases (quotientMap_eq_iff z y).mp hzy with h | h
        · exact hyC (h ▸ hz.1)
        · exact hyD (h ▸ hz.2)

instance : TotallyDisconnectedSpace (U A n) :=
  inferInstanceAs (TotallyDisconnectedSpace {q : CompactQuotient A n // q ≠ quotientMap infty})

instance : LocallyCompactSpace (U A n) :=
  (isOpen_compl_singleton : IsOpen ({quotientMap (infty : CompactProduct A n)}ᶜ)).locallyCompactSpace

/-- The prequotient chart on which the indicated coordinate is finite. -/
def finiteCoordinate (i : Fin (n + 1)) : Set (CompactProduct A n) :=
  {x | x i ≠ OnePoint.infty}

omit [∀ (i : ℕ), DiscreteTopology (A i)] [∀ (i : ℕ), TopologicalSpace (A i)] in
theorem quotientMap_mem_finiteCoordinate_image_iff (x : CompactProduct A n) (i : Fin (n + 1)) :
    quotientMap x ∈ quotientMap '' finiteCoordinate i ↔ x i ≠ OnePoint.infty := by
  constructor
  · rintro ⟨y, hy, h⟩
    rcases (quotientMap_eq_iff y x).mp h with heq | heq
    · exact heq ▸ hy
    · change y i ≠ OnePoint.infty at hy
      rw [heq] at hy
      simpa only [flip, ne_eq, onePointFlip_eq_infty_iff] using hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem isOpen_finiteCoordinate (i : Fin (n + 1)) : IsOpen (finiteCoordinate (A := A) i) :=
  isOpen_compl_singleton.preimage (continuous_apply i)

/-- The open chart on the punctured orbit space. -/
def chart (i : Fin (n + 1)) : Set (U A n) :=
  {q | q.1 ∈ quotientMap '' finiteCoordinate i}

theorem isOpen_chart (i : Fin (n + 1)) : IsOpen (chart (A := A) i) :=
  (isOpenMap_quotientMap _ (isOpen_finiteCoordinate i)).preimage continuous_subtype_val

omit [∀ (i : ℕ), DiscreteTopology (A i)] [∀ (i : ℕ), TopologicalSpace (A i)] in
theorem charts_cover (q : U A n) : ∃ i : Fin (n + 1), q ∈ chart i := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep q.1
  have hxnot : x ≠ (infty : CompactProduct A n) := by
    intro heq
    apply q.2
    rw [← hx, heq]
    rfl
  have hex : ∃ i, x i ≠ OnePoint.infty := by
    by_contra! h
    exact hxnot (funext h)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, x, hi, hx⟩

end QuotientTopology

end Aoki.Geometry
