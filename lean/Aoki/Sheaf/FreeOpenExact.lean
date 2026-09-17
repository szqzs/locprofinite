import Aoki.Sheaf.FreeOpen
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Mayer--Vietoris for free sheaves on opens

The sheaf gluing property gives the short exact sequence from the intersection,
through the direct sum, to the union. This uses mathlib's general
Mayer--Vietoris-square construction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Aoki

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}

/-- The square of two opens, their intersection, and their union. -/
def opensIntersectionUnionSquare (V W : Opens X) : Square (Opens X) where
  X₁ := V ⊓ W
  X₂ := V
  X₃ := W
  X₄ := V ⊔ W
  f₁₂ := homOfLE inf_le_left
  f₁₃ := homOfLE inf_le_right
  f₂₄ := homOfLE le_sup_left
  f₃₄ := homOfLE le_sup_right
  fac := Subsingleton.elim _ _

/-- The binary open cover is a Mayer--Vietoris square for the usual topology. -/
def opensMayerVietorisSquare (V W : Opens X) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  .mk' (opensIntersectionUnionSquare V W) (fun M =>
    Square.IsPullback.mk _ (TopCat.Sheaf.isLimitPullbackCone M V W))

/-- The free sheaves on two opens form a pushout over their intersection. -/
theorem freeOpen_union_isPushout (V W : Opens X) :
    ((opensIntersectionUnionSquare V W).map (freeOpenFunctor X)).IsPushout :=
  (opensMayerVietorisSquare V W).isPushoutAddCommGrpFreeSheaf

/-- The integral free-open Mayer--Vietoris short complex. -/
def freeOpenMayerVietoris (V W : Opens X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (opensMayerVietorisSquare V W).shortComplex

@[simp] theorem freeOpenMayerVietoris_X₁ (V W : Opens X) :
    (freeOpenMayerVietoris V W).X₁ = freeOpen (V ⊓ W) := rfl

@[simp] theorem freeOpenMayerVietoris_X₂ (V W : Opens X) :
    (freeOpenMayerVietoris V W).X₂ = (freeOpen V ⊞ freeOpen W) := rfl

@[simp] theorem freeOpenMayerVietoris_X₃ (V W : Opens X) :
    (freeOpenMayerVietoris V W).X₃ = freeOpen (V ⊔ W) := rfl

/-- Exactness, including monicity on the left and epicity on the right. -/
theorem freeOpenMayerVietoris_shortExact (V W : Opens X) :
    (freeOpenMayerVietoris V W).ShortExact :=
  (opensMayerVietorisSquare V W).shortComplex_shortExact

/-- Adding an open `W` to `V` changes the free sheaf by the quotient of
`freeOpen W` by the free sheaf of the intersection. -/
def freeOpenUnionQuotientIso (V W : Opens X) :
    cokernel (freeOpenMap (homOfLE (inf_le_right : V ⊓ W ≤ W))) ≅
      cokernel (freeOpenMap (homOfLE (le_sup_left : V ≤ V ⊔ W))) := by
  let sq := (freeOpen_union_isPushout V W).flip
  let f := cokernel.map _ _ _ _ sq.w
  letI := isIso_cokernel_map_of_isPushout sq
  let e := asIso f
  exact e

end Aoki
