import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Projective dimension and transfinite extensions

The argument uses injective presentations and the stability of the left lifting
property under transfinite composition. No exactness of arbitrary filtered
colimits is assumed: the input filtration is continuous at limit stages.
-/

noncomputable section

namespace Aoki

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The degree-one connecting homomorphism identifies vanishing of `Ext¹`
with lifting all maps through an injective presentation. -/
theorem extOne_vanish_iff_surjective_comp (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] :
    (∀ e : Ext X S.X₁ 1, e = 0) ↔
      Function.Surjective (fun f : X ⟶ S.X₂ => f ≫ S.g) := by
  constructor
  · intro h g
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ X hS (Ext.mk₀ g)
      (zero_add 1) (h _)
    obtain ⟨a, rfl⟩ := Ext.homEquiv₀.symm.surjective a
    exact ⟨a, Ext.homEquiv₀.symm.injective (by simpa using ha)⟩
  · intro h e
    obtain ⟨a, rfl⟩ := Ext.covariant_sequence_exact₁ X hS e
      (Ext.eq_zero_of_injective _) (zero_add 1)
    obtain ⟨a, rfl⟩ := Ext.homEquiv₀.symm.surjective a
    obtain ⟨b, rfl⟩ := h a
    simp only [Ext.homEquiv₀_symm_apply, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
      Ext.comp_zero]

omit [HasExt C] in
/-- A monomorphism has the lifting property against a map out of an injective
object if maps from its cokernel lift against that map. -/
theorem hasLiftingProperty_of_surjective_cokernel
    {A B I Q : C} (i : A ⟶ B) [Mono i] (p : I ⟶ Q) [Injective I]
    (h : Function.Surjective (fun f : cokernel i ⟶ I => f ≫ p)) :
    HasLiftingProperty i p where
  sq_hasLift {f g} sq := by
    let a := Injective.factorThru f i
    have ha : i ≫ a = f := Injective.comp_factorThru f i
    have hz : i ≫ (g - a ≫ p) = 0 := by
      simp only [Preadditive.comp_sub, ← Category.assoc, ha, sq.w, sub_self]
    let d := cokernel.desc i (g - a ≫ p) hz
    obtain ⟨b, hb⟩ := h d
    change b ≫ p = d at hb
    refine ⟨⟨{
      l := a + cokernel.π i ≫ b
      fac_left := by simp [Preadditive.comp_add, ← Category.assoc, ha]
      fac_right := by
        rw [Preadditive.add_comp, Category.assoc, hb, cokernel.π_desc]
        abel }⟩⟩

/-- Degree-one Ext vanishing for the cokernel gives the lifting property
against an injective presentation. -/
theorem hasLiftingProperty_of_extOne_vanish
    {A B : C} (i : A ⟶ B) [Mono i] {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂]
    (h : ∀ e : Ext (cokernel i) S.X₁ 1, e = 0) :
    HasLiftingProperty i S.g :=
  hasLiftingProperty_of_surjective_cokernel i S.g
    ((extOne_vanish_iff_surjective_comp (cokernel i) hS).mp h)

section Transfinite

variable {J : Type t} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {F : J ⥤ C} [F.IsWellOrderContinuous] (c : Cocone F) (hc : IsColimit c)
  (hbot : IsZero (F.obj ⊥))
  (hmono : ∀ (j : J), ¬IsMax j → Mono (F.map (homOfLE (Order.le_succ j))))

include hc hbot hmono

/-- Eklof's extension lemma, in degree one, for a continuous well-ordered
filtration starting from zero. -/
theorem extOne_vanish_of_transfinite [EnoughInjectives C] (Y : C)
    (h : ∀ (j : J), ¬IsMax j →
      ∀ e : Ext (cokernel (F.map (homOfLE (Order.le_succ j)))) Y 1, e = 0) :
    ∀ e : Ext c.pt Y 1, e = 0 := by
  let ⟨p⟩ := EnoughInjectives.presentation Y
  let S := ShortComplex.mk p.f (cokernel.π p.f) (cokernel.condition p.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel p.f }
  apply (extOne_vanish_iff_surjective_comp c.pt hS).mpr
  haveI : HasLiftingProperty (c.ι.app ⊥) S.g :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot hc
      (fun j hj => by
        letI := hmono j hj
        exact hasLiftingProperty_of_extOne_vanish _ hS (h j hj))
  intro g
  have sq : CommSq (0 : F.obj ⊥ ⟶ S.X₂) (c.ι.app ⊥) S.g g :=
    ⟨hbot.eq_of_src _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- Vanishing of any fixed positive Ext degree is closed under continuous
transfinite extensions. This follows from degree one by dimension shifting
in the coefficient variable. -/
theorem ext_succ_vanish_of_transfinite [EnoughInjectives C] (n : ℕ) (Y : C)
    (h : ∀ (j : J), ¬IsMax j →
      ∀ e : Ext (cokernel (F.map (homOfLE (Order.le_succ j)))) Y (n + 1), e = 0) :
    ∀ e : Ext c.pt Y (n + 1), e = 0 := by
  induction n generalizing Y with
  | zero => exact extOne_vanish_of_transfinite c hc hbot hmono Y h
  | succ n ih =>
    let ⟨p⟩ := EnoughInjectives.presentation Y
    let S := ShortComplex.mk p.f (cokernel.π p.f) (cokernel.condition p.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel p.f }
    have h' : ∀ (j : J), ¬IsMax j →
        ∀ e : Ext (cokernel (F.map (homOfLE (Order.le_succ j)))) S.X₃ (n + 1),
          e = 0 := by
      intro j hj e
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ _ hS e rfl (h j hj _)
      rw [Ext.eq_zero_of_injective b, Ext.zero_comp] at hb
      exact hb.symm
    have hcolim := ih S.X₃ h'
    intro e
    obtain ⟨a, rfl⟩ := Ext.covariant_sequence_exact₁ c.pt hS e
      (Ext.eq_zero_of_injective _) rfl
    rw [hcolim a, Ext.zero_comp]

omit [HasExt C] in
/-- A uniform projective-dimension bound is preserved by a continuous
well-ordered filtration with zero initial object and monomorphic successor
maps, provided that every successive quotient satisfies that bound. -/
theorem hasProjectiveDimensionLE_of_transfinite [EnoughInjectives C] (n : ℕ)
    (h : ∀ (j : J), ¬IsMax j →
      HasProjectiveDimensionLE (cokernel (F.map (homOfLE (Order.le_succ j)))) n) :
    HasProjectiveDimensionLE c.pt n := by
  letI := HasExt.standard C
  apply hasProjectiveDimensionLT_of_enoughInjectives c.pt (n + 1)
  intro Y
  apply subsingleton_of_forall_eq 0
  apply ext_succ_vanish_of_transfinite c hc hbot hmono n Y
  intro j hj e
  letI := h j hj
  exact e.eq_zero_of_hasProjectiveDimensionLT (n + 1) le_rfl

end Transfinite

end Aoki
