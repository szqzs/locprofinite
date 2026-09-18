# Sharp cardinal bounds for cup products on locally profinite spaces

*An AI-assisted proof of the sharp form of Aoki’s Question 2.14, with a Lean formalization.*

## 1. Aoki’s question

In *On cohomology of locally profinite sets*, Aoki proves that, for every $`n\geq 0`$, there is a locally profinite space of cardinality $`\aleph_{2n+1}`$ carrying classes $`\eta_0,\ldots,\eta_n\in H^1(U;\mathbf F_2)`$ with nonzero product. He then asks:

> **Question 2.14.** Is Theorem C optimal in terms of the weight (or cardinality) of $`U`$?

The statement and numbering here refer to [Aoki, arXiv:2411.05995v1, Theorem C on p. 1 and Question 2.14 on p. 4](https://arxiv.org/pdf/2411.05995v1#page=4).

We show that the sharp bound for a product of $`n+1`$ degree-one classes is $`\aleph_{n+1}`$, for both cardinality and weight. Thus the bound in Theorem C can be lowered for every $`n\geq 1`$. Moreover, all the factors in our nonzero product can be the same class.

Throughout, a *locally profinite Hausdorff space* means a locally compact, Hausdorff, totally disconnected space. Our examples are obtained by removing one point from a profinite space, so they also satisfy Aoki’s punctured-profinite convention. The *weight* $`w(X)`$ is the least cardinality of a basis for the topology. Cohomology means ordinary sheaf cohomology; $`\mathbf F_2`$ denotes the constant sheaf when used as a coefficient.

**Formalization convention.** A paragraph labeled **Lean** identifies the checked declarations supporting the preceding result. These links point to the actual definitions and proofs, not to axioms recording the desired conclusions. Mathematical notation is kept independent of implementation details; Section 8 explains the few relevant differences in presentation.

## 2. The theorem

**Theorem 2.1 — Sharp cup-power examples and size bounds.** For every integer $`r\geq 1`$, there exist a locally profinite Hausdorff space $`U_r`$ and a class $`\eta_r\in H^1(U_r;\mathbf F_2)`$ such that

```math
|U_r|=w(U_r)=\aleph_r,
\qquad
\eta_r^r\neq 0,
\qquad
\eta_r^{r+1}=0.
```

For every abelian sheaf $`\mathcal M`$ on $`U_r`$,

```math
H^q(U_r;\mathcal M)=0
\qquad(q\gt r).
```

Conversely, if $`V`$ is any locally profinite Hausdorff space and $`\mathcal M`$ is any abelian sheaf on $`V`$, then

```math
H^r(V;\mathcal M)\neq 0
\quad\Longrightarrow\quad
|V|\geq\aleph_r
\quad\text{and}\quad
w(V)\geq\aleph_r.
```

In particular, the least possible cardinality, and separately the least possible weight, of a locally profinite Hausdorff space supporting a nonzero product of $`r`$ degree-one constant-$`\mathbf F_2`$ classes is exactly $`\aleph_r`$.

The last assertion follows because such a product is a nonzero degree-$`r`$ class, whereas the examples attain both bounds. The all-coefficient vanishing and the nonzero degree-$`r`$ class also show that $`U_r`$ has cohomological dimension exactly $`r`$.

**Lean.** The three parts of the theorem are assembled as [Aoki.aoki_question_2_14](lean/Aoki/Main.lean#L31), [Aoki.aoki_question_2_14_minimality](lean/Aoki/Main.lean#L47), and [Aoki.aoki_example_cohomology_above](lean/Aoki/Main.lean#L56). The first theorem includes the topological properties, both cardinal equalities, and the two cup-power assertions.

### Proof strategy

We construct $`U_r`$ and a cover by $`r+1`$ opens whose nonempty intersections are disjoint unions of compact opens. The represented free sheaves on those intersections give a finite projective resolution. Transition functions for the diagonal involution define a degree-one class. An explicit chain lift shows that its $`r`$-th power is represented by a product of adjacent bit differences. Every top-degree boundary would give a decomposition of that function into invariant functions, each almost constant in one coordinate. A finite-difference induction rules out such a decomposition. Finally, a separate cardinal induction bounds the projective dimension of the constant integral sheaf on every smaller space.

## 3. The space, its charts, and its size

### 3.1. The diagonal involution quotient

Choose discrete sets $`A_i`$ with $`|A_i|=\aleph_i`$, for $`0\leq i\leq r`$, and put

```math
D_i=A_i\times\mathbf F_2,
\qquad
K_i=D_i\sqcup\{\infty_i\},
\qquad
K=\prod_{i=0}^{r}K_i.
```

Give $`K_i`$ the one-point compactification topology. Thus every point of $`D_i`$ is isolated, and a neighborhood of $`\infty_i`$ contains all but finitely many points of $`D_i`$. Each $`K_i`$ is profinite, and so is $`K`$.

Let $`\tau`$ act on every finite coordinate by

```math
\tau(a,s)=(a,s+1),
\qquad
\tau(\infty_i)=\infty_i.
```

The diagonal action is continuous. Its only fixed point is

```math
p=(\infty_0,\ldots,\infty_r).
```

Indeed, any finite coordinate changes its bit. Let $`q:K\to\overline K=K/\langle\tau\rangle`$ be the orbit map, and define

```math
U_r=\overline K\setminus\{q(p)\}.
```

The quotient $`\overline K`$ is compact Hausdorff: the finite orbit relation is closed. It is also zero-dimensional. If an orbit lies in an invariant open set, choose a clopen neighborhood of one representative inside that open set and take the union with its translate. The resulting invariant clopen set descends to a clopen neighborhood of the orbit. Hence $`\overline K`$ is profinite, and $`U_r`$ is locally compact, Hausdorff, and totally disconnected.

**Lean.** The objects are [CompactProduct](lean/Aoki/Topology/Quotient.lean#L19), [CompactQuotient](lean/Aoki/Topology/Quotient.lean#L138), and [U](lean/Aoki/Topology/Quotient.lean#L163). The fixed-point calculation is [flip_eq_self_iff](lean/Aoki/Topology/Quotient.lean#L73). The compactness and separation properties are registered instances in [Quotient.lean](lean/Aoki/Topology/Quotient.lean), and the orbit map is proved open in [isOpenMap_quotientMap](lean/Aoki/Topology/Quotient.lean#L196).

### 3.2. Gauge charts and compact-open cells

For $`0\leq i\leq r`$, let $`W_i\subseteq U_r`$ be the open subset on which coordinate $`i`$ is finite. This condition is invariant under $`\tau`$, and the $`W_i`$ cover $`U_r`$, since only the all-infinite orbit was removed.

On $`W_i`$, each orbit has a unique representative whose $`i`$-th bit is zero. This choice is continuous: the bit-zero slice is open, and the quotient map restricts to an open embedding from that slice onto $`W_i`$.

**Lean.** The cover is [iSup_chartOpen](lean/Aoki/Sheaf/ChartProjectivity.lean#L37). The continuous choice of representative is [sliceHomeomorph](lean/Aoki/Topology/Charts.lean#L86); a product description of each single chart is [chartProductHomeomorph](lean/Aoki/Topology/Charts.lean#L126).

**Lemma 3.1.** For every nonempty $`I\subseteq\{0,\ldots,r\}`$, the intersection

```math
W_I=\bigcap_{i\in I}W_i
```

is a disjoint union of compact-open subsets of $`U_r`$.

*Proof.* Choose any index $`k\in I`$; this is possible because $`I`$ is nonempty. Every orbit in $`W_I`$ has a finite $`k`$-th coordinate, so it has a unique representative whose $`k`$-th bit is zero. This representative varies continuously, by the chart description above.

In this representative, coordinate $`k`$ has the form $`(a_k,0)`$ and is specified by $`a_k\in A_k`$. Each other coordinate $`i\in I\setminus\{k\}`$ is an arbitrary finite pair $`(a_i,s_i)\in A_i\times\{0,1\}`$, while every coordinate $`j\notin I`$ can be any point of $`K_j`$, including infinity. Reading off these coordinates gives a homeomorphism

```math
W_I\cong
\underbrace{
A_k\times\prod_{i\in I\setminus\{k\}}(A_i\times\{0,1\})
}_{\text{discrete set of labels}}
\times
\underbrace{
\prod_{j\notin I}K_j
}_{\text{compact space}}.
```

The inverse inserts the zero bit in coordinate $`k`$ and takes the orbit. The label space is discrete because it is a finite product of discrete spaces, and the remaining product is compact. Fixing one label therefore gives a compact-open subset of $`W_I`$, homeomorphic to $`\prod_{j\notin I}K_j`$. Since $`W_I`$ is open in $`U_r`$, each such piece is also open in $`U_r`$ and remains compact there. Different labels give disjoint pieces, and every point has exactly one label, so the pieces cover $`W_I`$. $`\square`$

**Lean.** The labels and cells are [GaugeLabel](lean/Aoki/Topology/Intersections.lean#L14) and [cellOpen](lean/Aoki/Topology/Intersections.lean#L151). Their properties are [cell_pairwiseDisjoint](lean/Aoki/Topology/Intersections.lean#L84), [cells_cover_intersection](lean/Aoki/Topology/Intersections.lean#L92), [isClopen_cell](lean/Aoki/Topology/Intersections.lean#L126), and [isCompact_cell](lean/Aoki/Topology/Intersections.lean#L130). The formal proof constructs these labeled compact-open pieces directly.

### 3.3. Cardinality and weight

The finite product $`K`$ has cardinality $`\aleph_r`$, since the largest factor has that cardinality. Taking a quotient and then a subspace gives

```math
|U_r|\leq\aleph_r.
```

For weight, we use the elementary bound

```math
w(T)\leq\max(\aleph_0,|T|)
```

for a compact Hausdorff space $`T`$. To see it for infinite $`T`$, choose disjoint neighborhoods for every pair of distinct points. At a fixed point $`x`$, finite intersections of the chosen neighborhoods of $`x`$ refine every neighborhood of $`x`$: the complementary compact set is covered by finitely many of the corresponding neighborhoods of the other points. These finite intersections, for all $`x`$, form a basis of cardinality at most $`|T|`$.

An open quotient map does not increase weight, because images of basis elements form a basis. Passing to a subspace also does not increase weight. Consequently,

```math
w(U_r)\leq w(\overline K)\leq w(K)\leq\aleph_r.
```

For the reverse inequalities, consider the axis where all coordinates except coordinate $`r`$ are infinite. Each orbit on this axis has a unique representative with finite coordinate $`(a,0)`$, so the axis is an embedded discrete copy of $`A_r`$. It supplies $`\aleph_r`$ distinct points. It also forces weight at least $`\aleph_r`$, since a basis must distinguish the points of a discrete subspace by distinct basic neighborhoods. Therefore

```math
|U_r|=w(U_r)=\aleph_r.
```

**Lean.** The compact-space estimate is [weight_le_max_mk](lean/Aoki/Topology/CompactWeight.lean#L18). The discrete axis is [isEmbedding_axis](lean/Aoki/Topology/Axis.lean#L37). The final equalities are [mk_U](lean/Aoki/Topology/GeometrySize.lean#L52) and [weight_U](lean/Aoki/Topology/GeometrySize.lean#L74). Weight itself is defined in [weight](lean/Aoki/Topology/Weight.lean#L26) as the least basis cardinality.

## 4. A finite projective resolution

### 4.1. Free sheaves on opens

Let $`X`$ be a space and $`j:W\hookrightarrow X`$ the inclusion of an open subset. Write $`P(W)=j_!\underline{\mathbb Z}_W`$ for the constant integer sheaf on $`W`$, extended by zero to $`X`$. Its defining property is the natural isomorphism

```math
\mathrm{Hom}(P(W),\mathcal M)\cong\Gamma(W,\mathcal M).
```

Thus a morphism from $`P(W)`$ to $`\mathcal M`$ is exactly a section of $`\mathcal M`$ over $`W`$. Inclusions of opens induce maps between these representing sheaves, and $`P(X)\cong\underline{\mathbb Z}_X`$. Similarly, for a commutative ring $`R`$, write $`P_R(W)=j_!\underline R_W`$ for the constant rank-one $`R`$-module sheaf on $`W`$, extended by zero to $`X`$.

**Lean.** The implementation constructs $`P(W)`$ by sheafifying the free abelian presheaf on the representable presheaf of $`W`$, and proves the same representing property. The integral representation and the identification at the whole space are [freeOpenHomEquiv](lean/Aoki/Sheaf/FreeOpen.lean#L33) and [freeOpenTopIso](lean/Aoki/Sheaf/FreeOpen.lean#L97). Their module counterparts are [freeOpenModuleHomEquiv](lean/Aoki/Sheaf/ModuleFreeOpen.lean#L31) and [freeOpenModuleTopIso](lean/Aoki/Sheaf/ModuleFreeOpen.lean#L97).

**Lemma 4.1.** If $`X`$ is Hausdorff and totally disconnected and $`W`$ is a disjoint union of compact-open subsets, then $`P(W)`$ is projective. The same is true of $`P_R(W)`$.

*Proof.* Projectivity means that, given an epimorphism of sheaves $`\varphi:\mathcal F\twoheadrightarrow\mathcal G`$, every morphism $`P(W)\to\mathcal G`$ lifts to a morphism $`P(W)\to\mathcal F`$. By the representing property above, this is equivalent to the following concrete claim: every section $`s\in\Gamma(W,\mathcal G)`$ has a lift $`t\in\Gamma(W,\mathcal F)`$ with $`\varphi(t)=s`$. We prove this claim.

First suppose that $`W=K`$ is compact and open. An epimorphism of sheaves is surjective on stalks. Hence, for each $`x\in K`$, there is an open neighborhood $`V_x\subseteq K`$ on which $`s`$ has a lift $`t_x`$. Indeed, lift the germ of $`s`$ at $`x`$, represent the lifted germ by a local section, and shrink its neighborhood until its image agrees with $`s`$.

The space $`K`$ is compact, Hausdorff, and totally disconnected, so it has a basis of clopen subsets. We may therefore choose a clopen neighborhood $`C_x`$ of $`x`$ contained in $`V_x`$. Compactness gives finitely many of these neighborhoods, say $`C_1,\ldots,C_m`$, covering $`K`$. Each $`C_j`$ carries a chosen lift of $`s`$.

These lifts need not agree where the $`C_j`$ overlap. To remove the overlaps, set

```math
D_1=C_1,
\qquad
D_j=C_j\setminus\bigcup_{i=1}^{j-1}C_i
\quad(2\leq j\leq m).
```

The sets $`D_j`$ are clopen, pairwise disjoint, and still cover $`K`$; moreover, $`D_j\subseteq C_j`$. Restrict the chosen lift on $`C_j`$ to $`D_j`$. There are now no overlaps on which compatibility must be checked, so the sheaf gluing axiom combines these sections into a section $`t\in\Gamma(K,\mathcal F)`$. Its image is $`s`$, since this equality holds on every $`D_j`$.

For general $`W`$, write $`W=\coprod_{\lambda}K_\lambda`$ with each $`K_\lambda`$ compact and open. Apply the compact case to $`s|_{K_\lambda}`$ to obtain a lift on every $`K_\lambda`$. These sets are again disjoint and open, so the lifts glue to the required section on all of $`W`$. This proves projectivity of $`P(W)`$. The same argument applies to sheaves of $`R`$-modules and proves projectivity of $`P_R(W)`$. $`\square`$

**Lean.** See [exists_compactOpen_disjoint_refinement](lean/Aoki/Topology/CompactOpenCovers.lean#L79), [surjective_sections_of_disjoint_refinements](lean/Aoki/Sheaf/EpiSections.lean#L70), [projective_freeOpen_disjoint_iSup](lean/Aoki/Sheaf/ProjectiveOpen.lean#L41), and [projective_freeOpenModule_disjoint_iSup](lean/Aoki/Sheaf/ModuleFreeOpen.lean#L184). Applied to the cells of Lemma 3.1, this gives [projective_freeOpen_chartIntersection](lean/Aoki/Sheaf/ChartProjectivity.lean#L64) and [projective_freeOpenModule_chartIntersection](lean/Aoki/Sheaf/ModuleChartProjectivity.lean#L25).

### 4.2. The ordered Čech resolution

For the cover $`W_0,\ldots,W_r`$, define

```math
P_k=\bigoplus_{0\leq i_0\lt \cdots\lt i_k\leq r}
P(W_{i_0}\cap\cdots\cap W_{i_k}).
```

The differential is the alternating sum of the maps induced by deleting one index. The augmentation $`P_0\to P(U_r)`$ is induced by the inclusions $`W_i\subseteq U_r`$. Face-deletion identities imply $`d^2=0`$ and compatibility with augmentation.

**Proposition 4.2.** The augmented complex

```math
0\longrightarrow P_r\longrightarrow\cdots\longrightarrow P_1
\longrightarrow P_0\longrightarrow\underline{\mathbb Z}_{U_r}
\longrightarrow 0
```

is a projective resolution. The analogous complex $`P_\bullet^R`$ resolves the constant rank-one $`R`$-module sheaf.

*Proof.* Projectivity follows from Lemma 4.1. For exactness, work at a point $`x`$. The stalk of $`P(W)`$ vanishes when $`x\notin W`$; if $`x\in V\subseteq W`$, the inclusion induces an isomorphism between the corresponding stalks. These stalk facts follow from the representing property and the stalk–skyscraper adjunction. Choose the least index $`a`$ with $`x\in W_a`$.

Cone an increasing face to $`a`$: prepend $`a`$ when its first index is larger than $`a`$, using the inverse of the associated stalk inclusion, and put the contraction equal to zero otherwise. Faces with first index below $`a`$ have zero coefficient stalk. For the other faces, the usual alternating cancellations give $`dh+hd=1`$, with the augmentation section included in degree zero. This contracts the augmented stalk complex. Exactness of sheaves can be checked on stalks, so the augmented complex is exact. The module argument is identical. $`\square`$

**Lean.** The complex and its boundedness are [orderedComplex](lean/Aoki/Cech/OrderedComplex.lean#L161) and [orderedTerm_isZero](lean/Aoki/Cech/OrderedComplex.lean#L178). The contraction identities are [orderedContraction_identity](lean/Aoki/Cech/OrderedCone.lean#L194) and [orderedContraction_augmentation_identity](lean/Aoki/Cech/AugmentedCone.lean#L70). Their applicability at stalks is established in [StalkCone.lean](lean/Aoki/Cech/StalkCone.lean). The resulting actual projective-resolution objects are [freeOpenProjectiveResolution](lean/Aoki/Cech/SheafResolution.lean#L49) and [freeOpenModuleProjectiveResolution](lean/Aoki/Cech/ModuleSheafResolution.lean#L81).

Applying $`\mathrm{Hom}(-,\mathcal M)`$ computes ordinary sheaf cohomology, since

```math
H^q(U_r;\mathcal M)
=
\mathrm{Ext}^q_{\mathrm{Sh}(U_r;\mathbf{Ab})}
(\underline{\mathbb Z},\mathcal M).
```

There are no increasing faces of degree greater than $`r`$, hence

```math
H^q(U_r;\mathcal M)=0\qquad(q\gt r)
```

for every abelian sheaf $`\mathcal M`$. With constant $`\mathbf F_2`$ coefficients, the degree-$`k`$ cochains are the locally constant functions on the $`W_I`$ with $`|I|=k+1`$.

**Lean.** Ordinary cohomology is Mathlib’s actual sheaf-cohomology type. Its precise integral resolution is [quotientIntegralResolution](lean/Aoki/Cech/NonzeroClass.lean#L32); the all-coefficient vanishing is [quotient_sheaf_cohomology_eq_zero_above](lean/Aoki/Cech/NonzeroClass.lean#L70). Constant-sheaf sections are identified with locally constant functions by [constantSheafSectionAddEquiv](lean/Aoki/Sheaf/LocallyConstant.lean#L112).

## 5. The degree-one class and its cup powers

### 5.1. The transition cocycle

We construct a degree-one cohomology class by comparing the local choices of representative from Section 3.2. Recall that a point $`u\in U_r`$ is an orbit $`\{x,\tau x\}`$. The two representatives are distinct because we removed the only fixed point $`p`$. Write

```math
E=K\setminus\{p\},
\qquad
\pi:E\longrightarrow U_r
```

for the quotient map, whose fibers consist of these pairs.

On $`W_i`$, the $`i`$-th coordinate is finite. For a representative $`x`$, write this coordinate as $`x_i=(a_i,s_i)`$, where $`a_i\in A_i`$ and $`s_i\in\mathbf F_2=\{0,1\}`$. Thus $`s_i`$ is simply the bit in that coordinate. It belongs to the chosen representative: replacing $`x`$ by $`\tau x`$ changes $`s_i`$ to $`s_i+1`$.

Exactly one representative has $`i`$-th bit zero. Denote this choice by

```math
\ell_i:W_i\longrightarrow E,
\qquad
\pi(\ell_i(u))=u.
```

Section 3.2 shows that $`\ell_i`$ is continuous. The two choices $`\ell_i`$ and $`\tau\circ\ell_i`$ identify the preimage of $`W_i`$ with two disjoint copies of $`W_i`$. This is the local description of the double cover $`\pi`$.

On an overlap $`W_i\cap W_j`$, we have two rules for choosing a representative: make bit $`i`$ zero, or make bit $`j`$ zero. The transition function records whether these rules choose the same representative or opposite ones:

```math
z_{ij}(u)=
\begin{cases}
0,&\ell_j(u)=\ell_i(u),\\
1,&\ell_j(u)=\tau(\ell_i(u)).
\end{cases}
```

To compute this function, take either representative $`x`$ of $`u`$ and read its two bits $`s_i,s_j`$. Obtaining $`\ell_i(u)`$ requires a flip precisely when $`s_i=1`$, and similarly for $`\ell_j(u)`$. The two choices therefore agree exactly when the bits agree. In arithmetic modulo two, this gives the formula

```math
z_{ij}(u)=s_i+s_j\in\mathbf F_2.
```

The formula is independent of the representative, since $`(s_i+1)+(s_j+1)=s_i+s_j`$ in $`\mathbf F_2`$. It is also locally constant: on each compact-open piece of $`W_i\cap W_j`$ from Lemma 3.1, the representative with $`i`$-th bit zero has a fixed $`j`$-th bit, so $`z_{ij}`$ is constant there. Thus $`z_{ij}`$ is a section of the constant sheaf $`\mathbf F_2`$ on the overlap.

On a triple overlap $`W_i\cap W_j\cap W_k`$, changing from the $`i`$-choice to the $`j`$-choice and then to the $`k`$-choice has the same effect as changing directly from the $`i`$-choice to the $`k`$-choice. Algebraically,

```math
z_{ij}+z_{jk}
=(s_i+s_j)+(s_j+s_k)
=s_i+s_k
=z_{ik}.
```

A degree-one cochain in the ordered Čech complex is a family of sections on the pairwise overlaps, indexed by $`i\lt j`$. The functions $`z_{ij}`$ give such a cochain $`z`$, and the identity on triple overlaps is exactly the cocycle condition $`dz=0`$. Since Section 4.2 identifies the cohomology of this complex with ordinary sheaf cohomology, we obtain a class

```math
\eta_r=[z]\in H^1(U_r;\mathbf F_2).
```

This constructs the class; Section 6 will prove that its $`r`$-th power is nonzero.

**Lean.** The functions and cocycle are [transitionOnOpen](lean/Aoki/Cech/Cocycle.lean#L70), [transitionCochain](lean/Aoki/Cech/Cocycle.lean#L155), and [transitionCochain_cocycle](lean/Aoki/Cech/Cocycle.lean#L167). The ordinary cohomology class is [degreeOneClass](lean/Aoki/Cech/NonzeroClass.lean#L51).

### 5.2. Computing multiplication by a chain lift

We want explicit cocycles for the powers of $`\eta_r=[z]`$. The square has degree two, so it must be represented by functions on triple overlaps. The formula is

```math
(z\smile z)_{ijk}=z_{ij}z_{jk}
\qquad\text{on }W_i\cap W_j\cap W_k.
```

Both functions are restricted to this common intersection before multiplication. More generally, multiplying a degree-$`k`$ cochain $`c`$ by $`z`$ uses the rule

```math
(Tc)_{i_0\ldots i_{k+1}}
=z_{i_0i_1}\,c_{i_1\ldots i_{k+1}}.
```

Use the first two indices for the transition function and the remaining list for $`c`$, with the index $`i_1`$ shared by both. We will justify that this operation represents multiplication by $`\eta_r`$ in ordinary sheaf cohomology.

Put $`R=\mathbf F_2`$. By Section 4, a degree-$`k`$ cochain is equivalently a map $`c:P_k^R\to\underline R`$ from the module resolution. Define $`L_k`$ on the summand indexed by $`[i_0,\ldots,i_{k+1}]`$ by multiplying by $`z_{i_0i_1}`$ and deleting the first index. The deletion uses the inclusion of the full intersection into the intersection with that index omitted. Multiplication is well-defined because $`z_{i_0i_1}`$ is locally constant. Following $`L_k`$ by $`c`$ gives exactly our rule:

```math
P_{k+1}^R\xrightarrow{L_k}P_k^R\xrightarrow{c}\underline R,
\qquad Tc=c\circ L_k.
```

Let $`\varepsilon:P_0^R\to\underline R`$ be the augmentation, corresponding to the constant degree-zero cochain $`1`$. Then $`\varepsilon\circ L_0=z`$. Moreover, writing $`d_k:P_{k+1}^R\to P_k^R`$, we have

```math
L_k\circ d_{k+1}=d_k\circ L_{k+1}.
```

Indeed, expand the differential as a sum of index deletions. Terms deleting an index after the first two match; the first two terms combine using $`z_{i_1i_2}+z_{i_0i_2}=z_{i_0i_1}`$. Signs disappear over $`\mathbf F_2`$. These identities say that $`L`$ is a **chain lift** of $`z`$.

The differential identity ensures that $`T`$ sends cocycles to cocycles. The standard projective-resolution rule for the cup product then says that $`c\circ L_k`$ represents $`\eta_r\smile[c]`$. This is the Yoneda description of multiplication: lift one cocycle, then compose with the other.

Starting with $`c_1=z`$ and applying $`T`$ repeatedly therefore gives

```math
(c_k)_{i_0\ldots i_k}
=z_{i_0i_1}\cdots z_{i_{k-1}i_k},
\qquad [c_k]=\eta_r^k.
```

In degree $`r`$, the only increasing list is $`[0,\ldots,r]`$, corresponding to $`W_0\cap\cdots\cap W_r`$. All coordinates are finite here. Write $`F_r`$ for the function on tuples $`((a_i,s_i))_{i=0}^r`$ obtained by substituting $`z_{ij}=s_i+s_j`$:

```math
F_r((a_i,s_i)_{i=0}^{r})
=\prod_{j=0}^{r-1}(s_j+s_{j+1})\in\mathbf F_2.
```

The function $`F_r`$ depends only on the bits $`s_i`$ and is unchanged by flipping them all. It therefore defines a cocycle on the quotient intersection representing $`\eta_r^r`$. Section 6 proves that this cocycle is not a boundary.

**Lean.** The lift, differential identity, and product formula are [cupLift](lean/Aoki/Cech/CupProduct.lean#L45), [cupLift_chain_signed](lean/Aoki/Cech/CupProduct.lean#L197), and [ι_cupIterate](lean/Aoki/Cech/CupProduct.lean#L231). The Yoneda multiplication rule is [extMk_comp_of_lift](lean/Aoki/Homological/ExtMkComposition.lean#L116), applied in [yonedaPower_cupExtClass](lean/Aoki/Cech/CupExt.lean#L62). The comparison with ordinary cohomology is [cupCohomologyAddEquiv](lean/Aoki/Cech/CupCohomology.lean#L86); [cupProduct](lean/Aoki/Cech/CupCohomology.lean#L118) transports the Yoneda product through it. The final identity is [cupPower_degreeOneClass_top](lean/Aoki/Cech/CupNonvanishing.lean#L49).

## 6. The nonvanishing argument

### 6.1. A necessary condition for being a boundary

To prove $`\eta_r^r\neq0`$, we must show that its representing cocycle is not a boundary. A boundary in degree $`r`$ is the differential of a degree-$`(r-1)`$ cochain. Such a cochain assigns one locally constant function to each intersection obtained by omitting one of the opens:

```math
W_{\widehat i}=\bigcap_{j\neq i}W_j
\qquad(0\leq i\leq r).
```

Its differential restricts these functions to $`W_0\cap\cdots\cap W_r`$ and adds them; signs disappear over $`\mathbf F_2`$.

Evaluate these functions on the orbits of finite-coordinate tuples in

```math
C_r=\prod_{i=0}^{r}D_i
=\prod_{i=0}^{r}(A_i\times\mathbf F_2),
```

and call the resulting functions $`f_i:C_r\to\mathbf F_2`$. Thus, if our cocycle were a boundary, we would have

```math
F_r=\sum_{i=0}^{r}f_i.
```

Each summand would satisfy two properties:

1. **Flip invariance.** Write $`\sigma_r`$ for the simultaneous flip of all bits. Then $`f_i(\sigma_r x)=f_i(x)`$, since the two tuples represent the same orbit.

2. **Almost constancy.** With all other coordinates fixed, $`f_i`$ is constant outside a finite subset of $`D_i`$. We call this *almost constant* in coordinate $`i`$ and prove it below.

**Proposition (almost constancy).** Assume $`r\geq1`$ and fix $`0\leq i\leq r`$. Let $`b_i:W_{\widehat i}\to\mathbf F_2`$ be locally constant, and let $`f_i:C_r\to\mathbf F_2`$ be its pullback to finite-coordinate tuples. After fixing all coordinates except $`i`$, there exist a finite set $`E\subseteq D_i`$ and a value $`c\in\mathbf F_2`$ such that $`f_i=c`$ whenever the $`i`$-th coordinate lies outside $`E`$. Both $`E`$ and $`c`$ may depend on the fixed coordinates.

*Proof.* Fix $`x_j\in D_j`$ for each $`j\neq i`$. Allow coordinate $`i`$ to vary over $`D_i^+=D_i\cup\{\infty\}`$, and send $`t\in D_i^+`$ to the orbit of the tuple with $`i`$-th coordinate $`t`$ and other coordinates $`x_j`$. This gives a continuous map

```math
\iota:D_i^+\longrightarrow W_{\widehat i}.
```

Indeed, all other coordinates remain finite, as required by $`W_{\widehat i}`$, and $`r\geq1`$ ensures that the tuple never becomes the removed all-infinite point. Continuity follows from the coordinate inclusion and the quotient map.

The composite $`g=b_i\circ\iota:D_i^+\to\mathbf F_2`$ is continuous and agrees with the chosen slice of $`f_i`$ on $`D_i`$. Since $`\mathbf F_2`$ is discrete, $`g^{-1}(\{g(\infty)\})`$ is an open neighborhood of infinity. Such a neighborhood contains all but finitely many points of $`D_i`$. Taking those exceptional points as $`E`$ and $`c=g(\infty)`$ proves the claim. $`\square`$

Section 6.3 will rule out any decomposition of $`F_r`$ with these two properties, proving nonvanishing.

**Lean.** The differential is the sum of the omitted-intersection restrictions by [cochainValue_differential](lean/Aoki/Cech/CochainValues.lean#L68). Flip invariance and almost constancy are [invariant_deleted_section](lean/Aoki/Cech/BoundaryObstruction.lean#L142) and [along_deleted_section](lean/Aoki/Cech/BoundaryObstruction.lean#L152), using continuity at infinity via [almostConstant_of_continuous_onePoint](lean/Aoki/OnePoint.lean#L64).

### 6.2. Uniform thinning

**Lemma 6.1.** Let $`P`$ be infinite, let $`|P|\lt |A|`$, and let $`N_y\subseteq A\times\mathbf F_2`$ be finite for every $`y\in P`$. There exists $`a\in A`$ such that both $`(a,0)`$ and $`(a,1)`$ avoid every $`N_y`$.

*Proof.* The union of the first-coordinate projections of the $`N_y`$ has cardinality at most $`|P|\cdot\aleph_0=|P|\lt |A|`$. Choose $`a`$ outside this union. $`\square`$

This is a uniform choice over all $`y`$, rather than a separate choice for each configuration.

**Lean.** The cardinal estimate and the fresh pair are [mk_exceptional_first_coordinates_le](lean/Aoki/Thinning.lean#L18) and [exists_fresh_pair](lean/Aoki/Thinning.lean#L57). For our coordinates, [mk_config](lean/Aoki/Cardinals.lean#L45) and [config_lt_next](lean/Aoki/Cardinals.lean#L62) verify the strict cardinal growth used below.

### 6.3. The invariant nondecomposition lemma

**Lemma 6.2.** For $`r\geq1`$, $`F_r`$ cannot be written as a sum $`\sum_{i=0}^{r}f_i`$ in which every $`f_i`$ is invariant under $`\sigma_r`$ and almost constant in coordinate $`i`$.

*Proof.* We induct on $`r`$, starting at $`r=1`$. Given a putative decomposition, apply Lemma 6.1 to the finite exceptional sets of the last summand $`f_r`$, indexed by $`C_{r-1}`$. This is possible because

```math
|C_{r-1}|=\aleph_{r-1}\lt \aleph_r=|A_r|.
```

Choose $`a\in A_r`$ as in that lemma and define

```math
(\Delta_a f)(y)=f(y,(a,0))+f(y,(a,1)),
\qquad y\in C_{r-1}.
```

The same eventual value occurs at both chosen points for every $`y`$, so $`\Delta_a f_r=0`$. Direct calculation gives

```math
\Delta_a F_r=F_{r-1},
\qquad
F_0=1.
```

For $`i\lt r`$, almost constancy in coordinate $`i`$ survives $`\Delta_a`$, by taking the union of the two finite exceptional sets. Invariance survives as well:

```math
\begin{aligned}
(\Delta_a f_i)(\sigma_{r-1}y)
&=f_i(\sigma_{r-1}y,(a,0))
  +f_i(\sigma_{r-1}y,(a,1))\\
&=f_i(y,(a,1))+f_i(y,(a,0))\\
&=(\Delta_a f_i)(y).
\end{aligned}
```

The use of two points with the same base coordinate is what makes the flip exchange the two summands. Therefore, when $`r\geq2`$, applying $`\Delta_a`$ produces a prohibited decomposition

```math
F_{r-1}=\sum_{i=0}^{r-1}\Delta_a f_i,
```

contradicting the induction hypothesis.

For the base case $`r=1`$, retain the slice

```math
g(x)=f_0(x,(a,0)),
\qquad x\in D_0.
```

It is almost constant. Invariance of $`f_0`$ gives $`g(\sigma_0x)=f_0(x,(a,1))`$, so the assumed decomposition implies

```math
g(x)+g(\sigma_0x)=1
\qquad\text{for every }x\in D_0.
```

Choose an entire two-element orbit outside a finite exceptional set for $`g`$. Both values there equal the same constant $`c`$, making the left side $`c+c=0`$, a contradiction. Notice that $`g`$ itself need not be invariant; only the displayed relation is used. This completes the induction. $`\square`$

Starting at $`r=1`$ is necessary: for $`r=0`$, the function $`F_0=1`$ already is a single invariant, almost-constant summand, so there is no analogous nondecomposition assertion.

**Lean.** The difference identities are [delta_alternating](lean/Aoki/Functions.lean#L67) and [invariant_delta](lean/Aoki/Functions.lean#L73). The base-case contradiction is [not_flip_sum_one](lean/Aoki/AlmostConstant.lean#L78), used in [alternating_one_not_boundary](lean/Aoki/Nonvanishing.lean#L73). The induction step is [boundary_delta](lean/Aoki/Nonvanishing.lean#L51), and the final aleph specialization is [aleph_nondecomposition](lean/Aoki/Nonvanishing.lean#L120).

### 6.4. Conclusion of nonvanishing

By Section 6.1, a top-degree boundary would give exactly a decomposition excluded by Lemma 6.2. Hence the cochain representing $`\eta_r^r`$ is not a boundary, and

```math
\eta_r^r\neq0.
```

The resolution of Section 4 gives $`H^{r+1}(U_r;\mathbf F_2)=0`$, so $`\eta_r^{r+1}=0`$. Together with Section 3.3, this proves the existence and upper-vanishing assertions of Theorem 2.1.

**Lean.** The cochain is proved not to be a boundary in [aleph_powerCochain_not_boundary](lean/Aoki/Cech/CochainValues.lean#L140), giving nonzero ordinary cohomology in [aleph_topPowerClass_ne_zero](lean/Aoki/Cech/NonzeroClass.lean#L62). The actual cup-power conclusions are [aleph_cupPower_ne_zero](lean/Aoki/Cech/CupNonvanishing.lean#L58) and [cupPower_next_eq_zero](lean/Aoki/Cech/CupNonvanishing.lean#L66).

## 7. The universal lower bound

We now prove the all-coefficient bound used for optimality. This argument is independent of the special quotient construction.

### 7.1. Transfinite extensions preserve a projective-dimension bound

We use projective dimension in its Ext-vanishing sense: $`\mathrm{pd}(P)\leq n`$ means that $`\mathrm{Ext}^d(P,M)=0`$ for every $`M`$ and every $`d\gt n`$.

**Lemma 7.1.** In an abelian category with enough injectives, let a continuous well-ordered filtration start at zero, have monomorphic successor maps, and have colimit $`P`$. If every successive quotient has projective dimension at most $`n`$, then $`\mathrm{pd}(P)\leq n`$.

*Proof.* First fix an object $`Y`$ and an injective presentation

```math
0\longrightarrow Y\longrightarrow I\xrightarrow{p}C\longrightarrow0.
```

For an object $`Q`$, the condition $`\mathrm{Ext}^1(Q,Y)=0`$ is equivalent to every map $`Q\to C`$ lifting to $`I`$. Suppose it holds for each successive quotient, and consider a map $`P\to C`$. Construct compatible lifts along the filtration.

At a successor stage, extend the preceding lift using injectivity of $`I`$. Its discrepancy from the desired map to $`C`$ vanishes on the preceding stage, so it factors through the successive quotient. Lift that discrepancy to $`I`$, and use it to correct the extension. At a limit stage, continuity of the filtration gives a unique map from the compatible earlier lifts. The colimit therefore admits a lift, proving $`\mathrm{Ext}^1(P,Y)=0`$.

For higher positive degrees, dimension-shift in the coefficient variable using injective presentations. Vanishing of a fixed degree on all successive quotients becomes the degree-one vanishing condition just treated, and hence holds for $`P`$. Apply this in every degree $`d\gt n`$ for every coefficient object. $`\square`$

This proof uses the continuity of the given filtration; it does not require Ext to commute with arbitrary filtered colimits.

**Lean.** The lifting criterion is [extOne_vanish_iff_surjective_comp](lean/Aoki/Homological/TransfiniteDimension.lean#L24). The transfinite degree-one argument, dimension shifting, and final bound are [extOne_vanish_of_transfinite](lean/Aoki/Homological/TransfiniteDimension.lean#L86), [ext_succ_vanish_of_transfinite](lean/Aoki/Homological/TransfiniteDimension.lean#L107), and [hasProjectiveDimensionLE_of_transfinite](lean/Aoki/Homological/TransfiniteDimension.lean#L134).

### 7.2. The compact-open cover bound

**Proposition 7.2.** Let $`X`$ be Hausdorff and totally disconnected, and let $`W\subseteq X`$ be the union of at most $`\aleph_n`$ compact-open subsets of $`X`$. Then

```math
\mathrm{pd}(P(W))\leq n.
```

*Proof.* For $`n=0`$, enumerate the compact opens as $`K_0,K_1,\ldots`$, padding with empty sets if necessary. Set

```math
L_j=K_j\setminus\bigcup_{i\lt j}K_i.
```

Every $`L_j`$ is compact open: it is open, and it is a closed subset of the compact set $`K_j`$. The $`L_j`$ are disjoint and cover $`W`$. Lemma 4.1 makes $`P(W)`$ projective.

Suppose the assertion is known for $`n`$. Index a cover of size at most $`\aleph_{n+1}`$ by the initial ordinal $`\omega_{n+1}`$, again allowing empty terms, and write

```math
W=\bigcup_{\alpha\lt \omega_{n+1}}K_\alpha,
\qquad
W_\alpha=\bigcup_{\beta\lt \alpha}K_\beta.
```

The sheaves $`P(W_\alpha)`$ form a continuous filtration starting at zero with colimit $`P(W)`$. Here inclusions of opens give monomorphisms, and the free-open sheaf of a directed union is the colimit of the corresponding free-open sheaves. The latter assertion follows also from the representing property: compatible sections on an increasing open cover glue to a unique section on its union.

The binary Mayer–Vietoris sequence identifies the successive quotient $`Q_\alpha=P(W_{\alpha+1})/P(W_\alpha)`$ through the exact sequence

```math
0\longrightarrow P(W_\alpha\cap K_\alpha)
\longrightarrow P(K_\alpha)
\longrightarrow Q_\alpha
\longrightarrow0.
```

For completeness, this sequence comes from the exact sequence of free-open sheaves for two opens: on each stalk, the intersection maps into the sum of the two opens by the signed diagonal $`u\mapsto(u,-u)`$, and the next map adds the two inclusions into the union. Quotienting by the first open gives the displayed sequence.

Since $`\alpha\lt \omega_{n+1}`$, the cardinality of $`\alpha`$ is at most $`\aleph_n`$. Thus

```math
W_\alpha\cap K_\alpha
=
\bigcup_{\beta\lt \alpha}(K_\beta\cap K_\alpha)
```

is a union of at most $`\aleph_n`$ compact opens. The induction hypothesis gives projective dimension at most $`n`$ for its free-open sheaf, and $`P(K_\alpha)`$ is projective. The long exact Ext sequence therefore gives $`\mathrm{pd}(Q_\alpha)\leq n+1`$. Lemma 7.1 now gives $`\mathrm{pd}(P(W))\leq n+1`$, completing the induction. $`\square`$

**Lean.** The countable base is [projective_freeOpen_countable_iSup](lean/Aoki/Sheaf/ProjectiveOpen.lean#L52). Union colimits and continuous filtrations are [freeOpenUnionCoconeIsColimit](lean/Aoki/Sheaf/FreeOpenColimit.lean#L57) and [initialFreeOpenFiltration_continuous](lean/Aoki/Sheaf/FreeOpenFiltration.lean#L74). The binary exact sequence and quotient identification are [freeOpenMayerVietoris_shortExact](lean/Aoki/Sheaf/FreeOpenExact.lean#L64) and [freeOpenUnionQuotientIso](lean/Aoki/Sheaf/FreeOpenExact.lean#L70). Proposition 7.2 is [freeOpen_iSup_projectiveDimensionLE](lean/Aoki/Sheaf/CardinalDimension.lean#L54).

Taking $`W=X`$ and using $`P(X)\cong\underline{\mathbb Z}`$, we obtain

```math
H^d(X;\mathcal M)=0\qquad(d\gt n)
```

for every abelian sheaf $`\mathcal M`$, whenever $`X`$ has a compact-open cover of cardinality at most $`\aleph_n`$.

**Lean.** This is [sheaf_cohomology_eq_zero_of_compactOpen_cover_cardinal](lean/Aoki/Sheaf/CardinalDimension.lean#L111).

### 7.3. From covers to cardinality and weight

Let $`V`$ be locally compact, Hausdorff, and totally disconnected. It has a basis of compact opens. Choosing one compact-open neighborhood of each point gives a compact-open cover with at most $`|V|`$ members.

For the weight bound, take a basis $`\mathcal B`$ of cardinality $`w(V)`$. Every compact open is a finite union of members of $`\mathcal B`$: choose basis neighborhoods inside it and use compactness. Consequently,

```math
|\mathrm{CompactOpens}(V)|
\leq \max(\aleph_0,w(V)).
```

The family of all compact opens covers $`V`$. Proposition 7.2 therefore implies that either of the inequalities $`|V|\leq\aleph_n`$ or $`w(V)\leq\aleph_n`$ forces vanishing of all abelian sheaf cohomology above degree $`n`$.

Now let $`r\geq1`$. A cardinal strictly below $`\aleph_r`$ is at most $`\aleph_{r-1}`$. Hence

```math
|V|\lt \aleph_r\ \text{or}\ w(V)\lt \aleph_r
\quad\Longrightarrow\quad
H^r(V;\mathcal M)=0
```

for every abelian sheaf $`\mathcal M`$. This proves the universal lower bound and completes the proof of Theorem 2.1. $`\square`$

**Lean.** The required covers and count of compact opens are [exists_point_indexed_compactOpen_cover](lean/Aoki/Topology/Weight.lean#L93) and [mk_compactOpens_le_weight](lean/Aoki/Topology/Weight.lean#L128). The strict bounds are [sheaf_cohomology_eq_zero_of_cardinal_lt_aleph](lean/Aoki/Sheaf/CardinalDimension.lean#L149) and [sheaf_cohomology_eq_zero_of_weight_lt_aleph](lean/Aoki/Sheaf/CardinalDimension.lean#L161). Their contrapositive is assembled in [Aoki.aoki_question_2_14_minimality](lean/Aoki/Main.lean#L47).

## 8. Formalization and verification

### 8.1. Mathematical objects and Lean definitions

| Mathematical object or assertion | Lean declaration |
| --- | --- |
| The explicit punctured quotient | [U](lean/Aoki/Topology/Quotient.lean#L163) |
| Least cardinality of a topological basis | [weight](lean/Aoki/Topology/Weight.lean#L26) |
| The constant coefficient sheaf | [constantF2Sheaf](lean/Aoki/Cech/Cocycle.lean#L119) |
| The ordinary degree-one class | [degreeOneClass](lean/Aoki/Cech/NonzeroClass.lean#L51) |
| The ordinary cup-product operation | [cupProduct](lean/Aoki/Cech/CupCohomology.lean#L118) |
| Repeated degree-one cup powers | [cupPower](lean/Aoki/Cech/CupCohomology.lean#L127) |
| Equality of the cup power with the explicit top class | [cupPower_degreeOneClass_top](lean/Aoki/Cech/CupNonvanishing.lean#L49) |
| The complete existence theorem | [Aoki.aoki_question_2_14](lean/Aoki/Main.lean#L31) |
| Universal size minimality | [Aoki.aoki_question_2_14_minimality](lean/Aoki/Main.lean#L47) |

The code uses Boolean bits and the field with two elements. Its recursive configuration type with index $`r`$ has $`r+1`$ coordinates; its alternating function with index $`r`$ is exactly $`F_r`$ above. Some inductive helper theorems use an index one less than the positive degree. The final theorem uses the same $`r`$ as Theorem 2.1.

The free integral sheaf on the whole space is identified with exactly the constant integral object used in Mathlib’s definition of ordinary sheaf cohomology. The module resolution and the integral resolution are both proved projective and exact. Their comparison is constructed from the identical section-valued Hom complexes; no assertion that forgetting module structure preserves projectives or injectives is needed.

The cup operation is defined by transporting the standard constant-module Yoneda product through this proved comparison. The proof checks the explicit lift and its product formula. It does not invoke an independently defined Mathlib sheaf cup-product operation.

The gauge sections also suggest the familiar interpretation of $`\eta_r`$ as the class of a double cover. A torsor-classification equivalence is not formalized here and is not needed by the theorem. Likewise, the proof of nonvanishing uses the necessary boundary condition of Section 6.1; it does not need an additional converse characterization of all boundaries.

### 8.2. Reproducing the verification

The project pins Lean v4.31.0 and Mathlib v4.31.0, with Mathlib commit

~~~text
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f
~~~

From the directory containing this README, run:

~~~sh
cd lean
lake exe cache get
lake build
lake env lean AxiomAudit.lean
~~~

The aggregate [Aoki.lean](lean/Aoki.lean) imports the complete local development: 64 modules under the Aoki directory, or 65 modules including the aggregate itself. The complete development builds, and [AxiomAudit.lean](lean/AxiomAudit.lean) reports only Lean’s standard axioms—propositional extensionality, classical choice, and quotient soundness—for the main statements and their principal bridges. There are no proof placeholders or added mathematical axioms. The commands and audit output are recorded in [verification.txt](lean/verification.txt).

This repository includes the exposition, Lean sources, and pinned dependency manifest. Build caches are excluded. The [Lean project guide](lean/README.md) gives the source organization and build instructions. [GitHub Actions](.github/workflows/lean.yml) is configured to build the development and audit its axioms.

## References

1. Ko Aoki, *On cohomology of locally profinite sets*, [arXiv:2411.05995v1](https://arxiv.org/abs/2411.05995v1), 2024. The theorem and question numbers used here refer to this version.
2. The mathlib community, *Mathlib*, [source at the pinned commit](https://github.com/leanprover-community/mathlib4/tree/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f). The development uses its topology, sheaves, projective resolutions, derived-category Ext, and transfinite lifting infrastructure.

This README follows the economical proof implemented in the Lean development.
