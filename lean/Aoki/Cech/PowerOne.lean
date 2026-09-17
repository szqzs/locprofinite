import Aoki.Cech.Cocycle

noncomputable section

namespace Aoki.Cech

open CategoryTheory CategoryTheory.Limits Geometry

set_option backward.isDefEq.respectTransparency false

variable {A : ℕ → Type} {n : ℕ}
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]

/-- In degree one the adjacent-product cochain is the transition cocycle. -/
theorem powerCochain_one :
    powerCochain (A := A) (n := n) 1 = transitionCochain := by
  apply Sigma.hom_ext
  intro s
  simp only [powerCochain, transitionCochain, Sigma.ι_desc]
  simp only [powerTransitionHom, edgeTransitionHom, transitionHom, transitionSection]
  congr 2
  simp [powerTransition]

end Aoki.Cech
