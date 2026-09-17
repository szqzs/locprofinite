import Aoki.Sheaf.ModuleFreeOpen
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Stalks

/-!
# Locally constant scalar multiplication on module-sheaf sections

A locally constant scalar acts by gluing its constant scalar actions on the
open fibers. The action is characterized on germs, which proves its algebraic
laws and compatibility with restriction and sheaf morphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Aoki

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf TopCat.Sheaf

universe u

variable {R : Type u} {X : TopCat.{u}}

/-- The fiber of a locally constant function, as an open of the ambient space. -/
def scalarFiber {W : Opens X} (z : LocallyConstant W R) (a : R) : Opens X :=
  ⟨Subtype.val '' {x : W | z x = a},
    W.isOpenEmbedding'.isOpenMap _ (z.isLocallyConstant.isOpen_fiber a)⟩

theorem scalarFiber_le {W : Opens X} (z : LocallyConstant W R) (a : R) :
    scalarFiber z a ≤ W := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem mem_scalarFiber {W : Opens X} (z : LocallyConstant W R) (a : R)
    (x : W) : x.val ∈ scalarFiber z a ↔ z x = a := by
  constructor
  · rintro ⟨y, hy, he⟩
    have h : y = x := Subtype.ext he
    exact h ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem scalarFiber_pairwise_disjoint {W : Opens X} (z : LocallyConstant W R) :
    Pairwise (fun a b => Disjoint (scalarFiber z a) (scalarFiber z b)) := by
  intro a b hab
  apply Opens.coe_disjoint.mp
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  let y : W := ⟨x, scalarFiber_le z a hxa⟩
  exact hab (((mem_scalarFiber z a y).mp hxa).symm.trans
    ((mem_scalarFiber z b y).mp hxb))

theorem scalarFiber_cover {W : Opens X} (z : LocallyConstant W R) :
    W ≤ ⨆ a, scalarFiber z a := by
  intro x hx
  exact Opens.mem_iSup.mpr ⟨z ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl, rfl⟩⟩

variable [CommRing R] (M : TopCat.Sheaf (ModuleCat.{u} R) X) {W : Opens X}

private theorem existsUnique_scalar_section (z : LocallyConstant W R)
    (s : M.obj.obj (op W)) :
    ∃! t : M.obj.obj (op W), ∀ a : R,
      M.obj.map (homOfLE (scalarFiber_le z a)).op t =
        a • M.obj.map (homOfLE (scalarFiber_le z a)).op s := by
  exact M.existsUnique_gluing' (scalarFiber z) W
    (fun a => homOfLE (scalarFiber_le z a)) (scalarFiber_cover z)
    (fun a => a • M.obj.map (homOfLE (scalarFiber_le z a)).op s)
    (module_compatible_of_pairwise_disjoint R M _ (scalarFiber_pairwise_disjoint z) _)

/-- A locally constant scalar acts on sections by its constant actions on fibers. -/
def locallyConstantSMul (z : LocallyConstant W R) (s : M.obj.obj (op W)) :
    M.obj.obj (op W) :=
  (existsUnique_scalar_section M z s).choose

theorem locallyConstantSMul_restrict_fiber (z : LocallyConstant W R)
    (s : M.obj.obj (op W)) (a : R) :
    M.obj.map (homOfLE (scalarFiber_le z a)).op (locallyConstantSMul M z s) =
      a • M.obj.map (homOfLE (scalarFiber_le z a)).op s :=
  (existsUnique_scalar_section M z s).choose_spec.1 a

/-- Germs turn the locally constant action into ordinary scalar multiplication. -/
theorem germ_locallyConstantSMul (z : LocallyConstant W R)
    (s : M.obj.obj (op W)) (x : X) (hx : x ∈ W) :
    TopCat.Presheaf.germ M.obj W x hx (locallyConstantSMul M z s) =
      z ⟨x, hx⟩ • TopCat.Presheaf.germ M.obj W x hx s := by
  let a := z ⟨x, hx⟩
  have hxf : x ∈ scalarFiber z a := (mem_scalarFiber z a ⟨x, hx⟩).mpr rfl
  rw [← TopCat.Presheaf.germ_res_apply M.obj (homOfLE (scalarFiber_le z a)) x hxf,
    locallyConstantSMul_restrict_fiber]
  change (TopCat.Presheaf.germ M.obj (scalarFiber z a) x hxf).hom
    (a • M.obj.map (homOfLE (scalarFiber_le z a)).op s) = _
  rw [map_smul]
  rw [TopCat.Presheaf.germ_res_apply M.obj]

@[simp] theorem locallyConstantSMul_zero (z : LocallyConstant W R) :
    locallyConstantSMul M z (0 : M.obj.obj (op W)) = 0 := by
  apply TopCat.Presheaf.section_ext M W
  intro x hx
  rw [germ_locallyConstantSMul]
  simp

@[simp] theorem locallyConstantSMul_add (z : LocallyConstant W R)
    (s t : M.obj.obj (op W)) :
    locallyConstantSMul M z (s + t) = locallyConstantSMul M z s + locallyConstantSMul M z t := by
  apply TopCat.Presheaf.section_ext M W
  intro x hx
  simp only [map_add, germ_locallyConstantSMul, smul_add]

@[simp] theorem locallyConstantSMul_one (s : M.obj.obj (op W)) :
    locallyConstantSMul M (1 : LocallyConstant W R) s = s := by
  apply TopCat.Presheaf.section_ext M W
  intro x hx
  simp only [germ_locallyConstantSMul, LocallyConstant.one_apply, one_smul]

theorem locallyConstantSMul_mul (z w : LocallyConstant W R) (s : M.obj.obj (op W)) :
    locallyConstantSMul M (z * w) s = locallyConstantSMul M z (locallyConstantSMul M w s) := by
  apply TopCat.Presheaf.section_ext M W
  intro x hx
  simp only [germ_locallyConstantSMul, LocallyConstant.mul_apply, mul_smul]

theorem locallyConstantSMul_add_scalar (z w : LocallyConstant W R) (s : M.obj.obj (op W)) :
    locallyConstantSMul M (z + w) s = locallyConstantSMul M z s + locallyConstantSMul M w s := by
  apply TopCat.Presheaf.section_ext M W
  intro x hx
  simp only [germ_locallyConstantSMul, map_add, LocallyConstant.add_apply, add_smul]

@[simp] theorem locallyConstantSMul_zero_scalar (s : M.obj.obj (op W)) :
    locallyConstantSMul M (0 : LocallyConstant W R) s = 0 := by
  apply TopCat.Presheaf.section_ext M W
  intro x hx
  simp only [germ_locallyConstantSMul, LocallyConstant.zero_apply, zero_smul, map_zero]

/-- Restrict a locally constant scalar to a smaller open. -/
def restrictScalar {V W : Opens X} (i : V ⟶ W) (z : LocallyConstant W R) :
    LocallyConstant V R :=
  LocallyConstant.comap ⟨Set.inclusion (leOfHom i), (Opens.isOpenEmbedding_of_le i.le).continuous⟩ z

theorem locallyConstantSMul_restrict {V W : Opens X} (i : V ⟶ W)
    (z : LocallyConstant W R) (s : M.obj.obj (op W)) :
    M.obj.map i.op (locallyConstantSMul M z s) =
      locallyConstantSMul M (restrictScalar i z) (M.obj.map i.op s) := by
  apply TopCat.Presheaf.section_ext M V
  intro x hx
  rw [TopCat.Presheaf.germ_res_apply M.obj, germ_locallyConstantSMul, germ_locallyConstantSMul,
    TopCat.Presheaf.germ_res_apply M.obj]
  rfl

theorem locallyConstantSMul_naturality {N : TopCat.Sheaf (ModuleCat.{u} R) X}
    (f : M ⟶ N) (z : LocallyConstant W R) (s : M.obj.obj (op W)) :
    f.hom.app (op W) (locallyConstantSMul M z s) =
      locallyConstantSMul N z (f.hom.app (op W) s) := by
  apply TopCat.Presheaf.section_ext N W
  intro x hx
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, germ_locallyConstantSMul,
    germ_locallyConstantSMul]
  change ((TopCat.Presheaf.stalkFunctor (ModuleCat R) x).map f.hom).hom
    (z ⟨x, hx⟩ • TopCat.Presheaf.germ M.obj W x hx s) = _
  rw [map_smul, TopCat.Presheaf.stalkFunctor_map_germ_apply]

variable {M}

/-- Multiply a map represented on an open by a locally constant scalar there. -/
def locallyWeightedHom (z : LocallyConstant W R) (f : freeOpenModule R W ⟶ M) :
    freeOpenModule R W ⟶ M :=
  (freeOpenModuleHomEquiv R W M).symm
    (locallyConstantSMul M z (freeOpenModuleHomEquiv R W M f))

@[simp] theorem locallyWeightedHom_section (z : LocallyConstant W R)
    (f : freeOpenModule R W ⟶ M) :
    freeOpenModuleHomEquiv R W M (locallyWeightedHom z f) =
      locallyConstantSMul M z (freeOpenModuleHomEquiv R W M f) :=
  (freeOpenModuleHomEquiv R W M).apply_symm_apply _

@[simp] theorem locallyWeightedHom_one (f : freeOpenModule R W ⟶ M) :
    locallyWeightedHom (1 : LocallyConstant W R) f = f := by
  apply (freeOpenModuleHomEquiv R W M).injective
  simp

@[simp] theorem locallyWeightedHom_zero_scalar (f : freeOpenModule R W ⟶ M) :
    locallyWeightedHom (0 : LocallyConstant W R) f = 0 := by
  apply (freeOpenModuleHomAddEquiv R W M).injective
  change freeOpenModuleHomEquiv R W M (locallyWeightedHom 0 f) = _
  rw [locallyWeightedHom_section, locallyConstantSMul_zero_scalar]
  exact (map_zero (freeOpenModuleHomAddEquiv R W M)).symm

theorem locallyWeightedHom_mul (z w : LocallyConstant W R)
    (f : freeOpenModule R W ⟶ M) :
    locallyWeightedHom (z * w) f = locallyWeightedHom z (locallyWeightedHom w f) := by
  apply (freeOpenModuleHomEquiv R W M).injective
  simp only [locallyWeightedHom_section, locallyConstantSMul_mul]

theorem locallyWeightedHom_add_scalar (z w : LocallyConstant W R)
    (f : freeOpenModule R W ⟶ M) :
    locallyWeightedHom (z + w) f = locallyWeightedHom z f + locallyWeightedHom w f := by
  apply (freeOpenModuleHomAddEquiv R W M).injective
  rw [map_add]
  change freeOpenModuleHomEquiv R W M (locallyWeightedHom (z + w) f) =
    freeOpenModuleHomEquiv R W M (locallyWeightedHom z f) +
      freeOpenModuleHomEquiv R W M (locallyWeightedHom w f)
  simp only [locallyWeightedHom_section, locallyConstantSMul_add_scalar]

@[simp] theorem locallyWeightedHom_zero (z : LocallyConstant W R) :
    locallyWeightedHom z (0 : freeOpenModule R W ⟶ M) = 0 := by
  apply (freeOpenModuleHomAddEquiv R W M).injective
  change freeOpenModuleHomEquiv R W M (locallyWeightedHom z 0) = _
  rw [locallyWeightedHom_section]
  change locallyConstantSMul M z ((freeOpenModuleHomAddEquiv R W M) 0) = _
  simp

theorem locallyWeightedHom_add (z : LocallyConstant W R)
    (f g : freeOpenModule R W ⟶ M) :
    locallyWeightedHom z (f + g) = locallyWeightedHom z f + locallyWeightedHom z g := by
  apply (freeOpenModuleHomAddEquiv R W M).injective
  rw [map_add]
  change freeOpenModuleHomEquiv R W M (locallyWeightedHom z (f + g)) = _
  rw [locallyWeightedHom_section]
  change locallyConstantSMul M z ((freeOpenModuleHomAddEquiv R W M) (f + g)) = _
  rw [map_add, locallyConstantSMul_add]
  simp only [freeOpenModuleHomAddEquiv, AddEquiv.coe_mk, locallyWeightedHom_section]

theorem locallyWeightedHom_sum {ι : Type*} (z : LocallyConstant W R)
    (S : Finset ι) (f : ι → (freeOpenModule R W ⟶ M)) :
    locallyWeightedHom z (∑ i ∈ S, f i) = ∑ i ∈ S, locallyWeightedHom z (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp only [Finset.sum_insert ha, locallyWeightedHom_add, ih]

theorem locallyWeightedHom_postcomp {N : TopCat.Sheaf (ModuleCat.{u} R) X}
    (z : LocallyConstant W R) (f : freeOpenModule R W ⟶ M) (g : M ⟶ N) :
    locallyWeightedHom z f ≫ g = locallyWeightedHom z (f ≫ g) := by
  apply (freeOpenModuleHomEquiv R W N).injective
  rw [freeOpenModuleHomEquiv_naturality, locallyWeightedHom_section,
    locallyWeightedHom_section, freeOpenModuleHomEquiv_naturality]
  exact locallyConstantSMul_naturality M g z _

theorem locallyWeightedHom_precomp {V W : Opens X} (i : V ⟶ W)
    (z : LocallyConstant W R) (f : freeOpenModule R W ⟶ M) :
    freeOpenModuleMap R i ≫ locallyWeightedHom z f =
      locallyWeightedHom (restrictScalar i z) (freeOpenModuleMap R i ≫ f) := by
  apply (freeOpenModuleHomEquiv R V M).injective
  rw [freeOpenModuleHomEquiv_restrict, locallyWeightedHom_section,
    locallyWeightedHom_section, freeOpenModuleHomEquiv_restrict]
  exact locallyConstantSMul_restrict M i z _

/-- Composition of locally weighted inclusions multiplies the scalar functions. -/
theorem locallyWeightedHom_comp {V W : Opens X} (i : V ⟶ W)
    (z : LocallyConstant V R) (w : LocallyConstant W R) (f : freeOpenModule R W ⟶ M) :
    locallyWeightedHom z (freeOpenModuleMap R i) ≫ locallyWeightedHom w f =
      locallyWeightedHom (z * restrictScalar i w) (freeOpenModuleMap R i ≫ f) := by
  rw [locallyWeightedHom_postcomp, locallyWeightedHom_precomp, ← locallyWeightedHom_mul]

end Aoki
