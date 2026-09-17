import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Comparing Ext through paired projective resolutions

This conditional helper requires actual projective resolutions and additive
bijections of their Hom groups commuting with the differentials. It constructs
the induced Ext equivalence in every positive degree, with an explicit formula
on cocycle representatives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Abelian

namespace Aoki.Cech

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable {Z Y : C} {Z' Y' : D}

/-- Cocycles represented on one degree of a projective resolution. -/
def resolutionCycles (P : ProjectiveResolution Z) (Y : C) (n : ℕ) :
    AddSubgroup (P.complex.X n ⟶ Y) where
  carrier := {f | P.complex.d (n + 1) n ≫ f = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg; simp_all
  neg_mem' := by intro f hf; simp_all

/-- The surjective map from cocycles to the Ext group they represent. -/
def resolutionExtHom (P : ProjectiveResolution Z) (Y : C) (n : ℕ) :
    resolutionCycles P Y n →+ Ext Z Y n where
  toFun f := P.extMk f.1 (n + 1) rfl f.2
  map_zero' := P.extMk_zero _ _
  map_add' f g := (P.add_extMk f.1 g.1 (n + 1) rfl f.2 g.2).symm

theorem resolutionExtHom_surjective (P : ProjectiveResolution Z) (Y : C) (n : ℕ) :
    Function.Surjective (resolutionExtHom P Y n) := by
  intro a
  obtain ⟨f, hf, ha⟩ := P.extMk_surjective a (n + 1) rfl
  exact ⟨⟨f, hf⟩, ha⟩

variable (P : ProjectiveResolution Z) (Q : ProjectiveResolution Z')
variable (e : ∀ n, (P.complex.X n ⟶ Y) ≃+ (Q.complex.X n ⟶ Y'))
variable (he : ∀ n (f : P.complex.X n ⟶ Y),
  e (n + 1) (P.complex.d (n + 1) n ≫ f) = Q.complex.d (n + 1) n ≫ e n f)

/-- A comparison commuting with the differential induces a bijection on cycles. -/
def resolutionCyclesEquiv (n : ℕ) : resolutionCycles P Y n ≃+ resolutionCycles Q Y' n where
  toFun f := ⟨e n f.1, by
    change Q.complex.d (n + 1) n ≫ e n f.1 = 0
    rw [← he, f.2, map_zero]⟩
  invFun f := ⟨(e n).symm f.1, by
    apply (e (n + 1)).injective
    rw [he, AddEquiv.apply_symm_apply, f.2, map_zero]⟩
  left_inv f := by ext; exact (e n).symm_apply_apply f.1
  right_inv f := by ext; exact (e n).apply_symm_apply f.1
  map_add' f g := by ext; exact (e n).map_add f.1 g.1

private theorem resolutionExtHom_ker_eq (n : ℕ) :
    (resolutionExtHom P Y (n + 1)).ker =
      ((resolutionExtHom Q Y' (n + 1)).comp
        (resolutionCyclesEquiv P Q e he (n + 1)).toAddMonoidHom).ker := by
  ext f
  change P.extMk f.1 (n + 2) rfl f.2 = 0 ↔
    Q.extMk (e (n + 1) f.1) (n + 2) rfl (by rw [← he, f.2, map_zero]) = 0
  rw [P.extMk_eq_zero_iff _ _ _ _ n rfl, Q.extMk_eq_zero_iff _ _ _ _ n rfl]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨e n g, (he n g).symm.trans (congrArg (e (n + 1)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨(e n).symm g, (e (n + 1)).injective ?_⟩
    rw [he, AddEquiv.apply_symm_apply, hg]

/-- The Ext equivalence induced by paired Hom complexes, in positive degree. -/
def resolutionExtAddEquiv (n : ℕ) : Ext Z Y (n + 1) ≃+ Ext Z' Y' (n + 1) :=
  (QuotientAddGroup.quotientKerEquivOfSurjective
    (resolutionExtHom P Y (n + 1)) (resolutionExtHom_surjective P Y (n + 1))).symm.trans
    (QuotientAddGroup.liftEquiv (resolutionExtHom P Y (n + 1)).ker
      ((resolutionExtHom_surjective Q Y' (n + 1)).comp
        (resolutionCyclesEquiv P Q e he (n + 1)).surjective)
      (resolutionExtHom_ker_eq P Q e he n))

/-- This equivalence sends a cocycle to its image under the specified Hom comparison. -/
theorem resolutionExtAddEquiv_extMk (n : ℕ) (f : P.complex.X (n + 1) ⟶ Y)
    (hf : P.complex.d (n + 2) (n + 1) ≫ f = 0) :
    resolutionExtAddEquiv P Q e he n (P.extMk f (n + 2) rfl hf) =
      Q.extMk (e (n + 1) f) (n + 2) rfl (by rw [← he, hf, map_zero]) := by
  let c : resolutionCycles P Y (n + 1) := ⟨f, hf⟩
  change resolutionExtAddEquiv P Q e he n (resolutionExtHom P Y (n + 1) c) = _
  dsimp only [resolutionExtAddEquiv, AddEquiv.trans_apply]
  have hc : (QuotientAddGroup.quotientKerEquivOfSurjective
      (resolutionExtHom P Y (n + 1)) (resolutionExtHom_surjective P Y (n + 1))).symm
        (resolutionExtHom P Y (n + 1) c) = (c : _ ⧸ (resolutionExtHom P Y (n + 1)).ker) := by
    apply (QuotientAddGroup.quotientKerEquivOfSurjective
      (resolutionExtHom P Y (n + 1)) (resolutionExtHom_surjective P Y (n + 1))).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [hc, QuotientAddGroup.liftEquiv_mk]
  rfl

end Aoki.Cech
