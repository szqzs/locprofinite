# Aoki Question 2.14 in Lean

This project formalizes the punctured involution quotient construction and the
sharp cardinality and weight bounds using finite projective resolutions of
sheaves. The [main research exposition](../README.md) states Aoki’s question,
the sharp theorem, and the complete proof, with links to the Lean declarations
formalizing each step. This page is the build and source guide.

## Verified theorem

For every positive integer $r$, the project constructs an actual locally
profinite Hausdorff space $U_r$ and an ordinary sheaf-cohomology class
$\eta\in H^1(U_r;\mathbf F_2)$ satisfying

$$
|U_r|=w(U_r)=\aleph_r,\qquad \eta^r\ne0,\qquad \eta^{r+1}=0.
$$

For every locally profinite Hausdorff space, nonzero degree-$r$ cohomology
with any abelian coefficient sheaf forces both cardinality and weight to be
at least $\aleph_r$. All abelian sheaf cohomology on the constructed example
vanishes in degrees greater than $r$.

The assembled declarations in [Main.lean](Aoki/Main.lean) are:

- `Aoki.aoki_question_2_14`: the explicit space, all three topological
  properties, both exact sizes, and a degree-one class with the asserted powers.
- `Aoki.aoki_question_2_14_minimality`: the universal lower bounds, with
  arbitrary abelian coefficient sheaves.
- `Aoki.aoki_example_cohomology_above`: the all-coefficient upper vanishing bound.

These statements use Mathlib's `CategoryTheory.Sheaf.H`, defined as Ext from
the constant integral sheaf. The earlier `ObstructionSpace` is only an auxiliary
algebraic quotient, not a substitute definition of cohomology.

The cup product is defined in [CupCohomology.lean](Aoki/Cech/CupCohomology.lean)
by the standard Yoneda algebra of the constant rank-one module, transported
through the proved section-complex comparison with ordinary sheaf cohomology.
The multiplication formula is proved using an explicit Alexander–Whitney lift.
This supplies the cup-product operation needed here; it is not a comparison
against a separate pre-existing Mathlib cup-product definition.
`cupPower_degreeOneClass_top` in
[CupNonvanishing.lean](Aoki/Cech/CupNonvanishing.lean) is the final identity
connecting that product to the explicit nonboundary cochain.

The class is defined by the transition cocycle. The additional interpretation
as a torsor-classification equivalence in the handwritten explanation is not
needed by the formal theorem and has not been formalized here.

## Proof organization

1. **Combinatorial obstruction.** `Cardinals`, `Thinning`, `Functions`,
   `AlmostConstant`, and `Nonvanishing` prove the alternating function cannot
   be a sum of the permitted coordinatewise almost-constant invariant functions.
   `OnePoint` connects almost-constancy with continuous extension.
2. **Actual topology.** `Topology/Quotient`, `Charts`, `Intersections`, `Axis`,
   and `GeometrySize` construct the finite involution quotient and its puncture,
   compact-open gauge cells, and exact cardinality and topological weight.
3. **Sheaves and projectivity.** `Sheaf/FreeOpen`, `EpiSections`, and
   `ProjectiveOpen` show that represented free sheaves on compact opens and
   disjoint unions of compact opens are projective. `LocallyConstant` identifies
   constant-sheaf sections with locally constant functions.
4. **Finite resolution.** `Cech/OrderedComplex`, `OrderedCone`, `StalkCone`, and
   `SheafResolution` construct the finite ordered Cech projective resolution.
   Exactness is proved on stalks by a least-active-vertex contraction.
5. **Nonvanishing.** `Cech/BoundaryObstruction`, `CochainValues`, and
   `NonzeroClass` prove the explicit top cochain is not a boundary and therefore
   defines a nonzero class in actual ordinary sheaf cohomology.
6. **Products.** `Sheaf/LocallyConstantScalar` constructs local scalar action
   by gluing. `Cech/CupProduct` proves the explicit Alexander-Whitney lift and
   its iterates. The module and integral resolutions are compared through their
   section-valued Hom complexes in `ModuleComparison`. Actual Yoneda composition
   is handled in `Homological/ExtComposition` and its companion modules.
7. **Sharp lower bounds.** `Sheaf/CardinalDimension` proves the constant
   integral sheaf has projective dimension at most n for a compact-open cover
   of cardinality at most aleph n. It uses countable disjointification,
   Mayer-Vietoris, and `Homological/TransfiniteDimension`. This directly proves
   the needed bound without a general Boolean-ring/Osofsky formalization.

## Build

Pinned versions:

- Lean `v4.31.0`.
- Mathlib `v4.31.0`, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- Transitive dependency commits in `lake-manifest.json`.

With `elan` installed, run from this directory:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The pinned manifest uses portable upstream dependency URLs. Lake downloads
the dependencies and Mathlib cache when the commands above are run.

The aggregate build imports the complete development. The principal results'
axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`; there
are no proof placeholders or added mathematical axioms. The recorded commands
and audit output are in [verification.txt](verification.txt).

The repository workflow builds this project and runs an axiom allowlist audit
on pushes and pull requests. The allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`.
