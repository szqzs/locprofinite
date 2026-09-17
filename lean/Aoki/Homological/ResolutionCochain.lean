import Aoki.Homological.ExtComposition

/-! # Degree-one cochain lifts on projective resolutions -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace Aoki.Homological
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C} (R : ProjectiveResolution X) (S : ProjectiveResolution Y)

/-- Extend a degree-one family on the nonnegative resolution to its integer-indexed cochain complex. -/
def resolutionCochainOne (L : ∀ k, R.complex.X (k + 1) ⟶ S.complex.X k) :
    Cochain R.cochainComplex S.cochainComplex 1 :=
  Cochain.mk fun p q hpq => if hq : q ≤ 0 then
    (R.cochainComplexXIso p ((-q).toNat + 1) (by omega)).hom ≫ L (-q).toNat ≫
      (S.cochainComplexXIso q (-q).toNat (by omega)).inv
  else 0

@[simp] theorem resolutionCochainOne_v (L : ∀ k, R.complex.X (k + 1) ⟶ S.complex.X k)
    (k : ℕ) :
    (resolutionCochainOne R S L).v (-((k + 1 : ℕ) : ℤ)) (-k) (by omega) =
      (R.cochainComplexXIso (-((k + 1 : ℕ) : ℤ)) (k + 1) (by omega)).hom ≫ L k ≫
        (S.cochainComplexXIso (-k) k rfl).inv := by
  dsimp only [resolutionCochainOne, Cochain.mk_v]
  split_ifs with hk
  · have H : ∀ j (hj : j = k) (hp : -((j + 1 : ℕ) : ℤ) = -((k + 1 : ℕ) : ℤ))
        (hq : -(j : ℤ) = -(k : ℤ)),
        (R.cochainComplexXIso (-((k + 1 : ℕ) : ℤ)) (j + 1) hp).hom ≫ L j ≫
          (S.cochainComplexXIso (-k) j hq).inv =
        (R.cochainComplexXIso (-((k + 1 : ℕ) : ℤ)) (k + 1) (by omega)).hom ≫ L k ≫
          (S.cochainComplexXIso (-k) k rfl).inv := by
      intro j hj hp hq
      subst j
      rfl
    exact H _ (by simp) _ _
  · omega

theorem resolutionCochainOne_v' (L : ∀ k, R.complex.X (k + 1) ⟶ S.complex.X k)
    (p q : ℤ) (k : ℕ) (hp : -((k + 1 : ℕ) : ℤ) = p) (hq : -(k : ℤ) = q) :
    (resolutionCochainOne R S L).v p q (by omega) =
      (R.cochainComplexXIso p (k + 1) hp).hom ≫ L k ≫
        (S.cochainComplexXIso q k hq).inv := by
  subst p q
  exact resolutionCochainOne_v R S L k

/-- The signed chain-lift identity is exactly the cocycle condition. -/
theorem resolutionCochainOne_closed (L : ∀ k, R.complex.X (k + 1) ⟶ S.complex.X k)
    (hL : ∀ k, L (k + 1) ≫ S.complex.d (k + 1) k +
      R.complex.d (k + 2) (k + 1) ≫ L k = 0) :
    δ 1 2 (resolutionCochainOne R S L) = 0 := by
  ext p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hq
    have hp : p = -(k + 2) := by omega
    subst p
    rw [δ_v 1 2 rfl _ _ _ hpq (-(k + 1)) (-(k + 1)) (by omega) (by omega)]
    rw [resolutionCochainOne_v' R S L _ _ (k + 1) (by omega) (by omega),
      resolutionCochainOne_v' R S L _ _ k (by omega) rfl]
    rw [R.cochainComplex_d _ _ (k + 2) (k + 1) (by omega) (by omega),
      S.cochainComplex_d _ _ (k + 1) k (by omega) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, show (2 : ℤ).negOnePow = 1 from rfl, one_smul,
      Cochain.zero_v]
    have hh := congrArg (fun f =>
      (R.cochainComplexXIso (-(k + 2)) (k + 2) (by omega)).hom ≫ f ≫
        (S.cochainComplexXIso (-k) k rfl).inv) (hL k)
    simpa only [comp_add, add_comp, Category.assoc, zero_comp, comp_zero] using hh
  · exact (CochainComplex.isZero_of_isStrictlyLE S.cochainComplex 0 q (by omega)).eq_of_tgt _ _

/-- An anticommuting degree-one family defines an actual degree-one cocycle. -/
def resolutionCocycleOne (L : ∀ k, R.complex.X (k + 1) ⟶ S.complex.X k)
    (hL : ∀ k, L (k + 1) ≫ S.complex.d (k + 1) k +
      R.complex.d (k + 2) (k + 1) ≫ L k = 0) :
    Cocycle R.cochainComplex S.cochainComplex 1 :=
  Cocycle.mk (resolutionCochainOne R S L) 2 rfl (resolutionCochainOne_closed R S L hL)

/-- The corresponding shifted cochain morphism. -/
def resolutionLiftOne (L : ∀ k, R.complex.X (k + 1) ⟶ S.complex.X k)
    (hL : ∀ k, L (k + 1) ≫ S.complex.d (k + 1) k +
      R.complex.d (k + 2) (k + 1) ≫ L k = 0) :
    ShiftedHom R.cochainComplex S.cochainComplex (1 : ℤ) :=
  Cocycle.equivHomShift.symm (resolutionCocycleOne R S L hL)

end Aoki.Homological
