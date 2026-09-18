# A small mathematical baseline

Start with connected mathematical topics rather than unrelated famous theorems.
The following arguments are candidate tasks for the
[formalization pilot](formalization-experiments.md), not an accepted corpus or a
list of results absent from mathlib. The sumset lower bound and a triple-sumset
application have local Lean proofs; the remaining tasks below are proposals.
Ordinary checked mathlib infrastructure can be reused without rebuilding a separate
foundation library or obtaining per-lemma exceptions.

The current [corpus](../corpus/README.md) has two sumset notes and a short
Erdős–Szekeres note reserved for a measured attempt. The latter remains entirely
`not_started`. For standard-corpus construction, bind existing declarations when
appropriate. For proof-translation experiments, the plans below specify which
human argument to preserve; these are different evaluation tasks.

## Algebra: inverses of products

**Definitions.** A group, identity, inverse, and multiplication. Do not assume
commutativity.

**Supporting lemma.** If `xg = 1` and `gy = 1`, then

\[
x=x(gy)=(xg)y=y.
\]

This proves that any left inverse and right inverse of the same element agree.
It uses only associativity and the identity laws.

**Statement.** For elements \(a,b\) of a group,

\[
(ab)^{-1}=b^{-1}a^{-1}.
\]

**Human proof.** The order reverses because undoing the product starts with its
last factor:

\[
(ab)(b^{-1}a^{-1})=a(bb^{-1})a^{-1}=aa^{-1}=1.
\]

The element \((ab)^{-1}\) is a left inverse of \(ab\), and the calculation shows
that \(b^{-1}a^{-1}\) is a right inverse. Apply the supporting lemma.

**Proof-translation experiment.** Use mathlib's group definition, prove the supporting lemma
internally, and express the displayed calculation using the reviewed group laws.
Do not close the goal by calling the upstream inverse-of-product theorem. Inspect
inferred group instances as well as the explicit rewrite lemmas. The
[group library documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Basic.html)
provides existing definitions and theorem names for comparison.

**Why this seed matters.** It tests quantified structure assumptions, a helper
lemma shared by proofs, and a concise explanation of an algebraic mechanism.

## Additive combinatorics: cardinality of a sumset

**Definition.** For subsets \(A,B\) of an additive abelian group \(G\),

\[
A+B=\{a+b:a\in A,\ b\in B\}.
\]

Define finite sets, cardinality, and translations before using them. The basic
sumset construction makes sense under weaker assumptions, but one consistent
abelian-group setting is sufficient for the first reader-facing collection.

**Statement.** If \(A\) and \(B\) are finite and nonempty, then

\[
\max(|A|,|B|)\leq |A+B|\leq |A|\,|B|.
\]

**Human proof, lower bound.** Fix \(b_0\in B\). The map \(a\mapsto a+b_0\)
injects \(A\) into \(A+B\), since translation is cancellative. Thus
\(|A|\leq |A+B|\). Fixing \(a_0\in A\) gives the other inequality by the
same argument. Together they give the maximum.

**Human proof, upper bound.** The map \(A\times B\to A+B\) given by
\((a,b)\mapsto a+b\) is onto. Each sum therefore has at least one representing
pair, and there are \(|A|\,|B|\) pairs. Consequently \(|A+B|\leq |A|\,|B|\).

The upper bound holds when one set is empty too. The lower bound as stated needs
both sets nonempty: if \(A=\varnothing\) and \(B\neq\varnothing\), the sumset
is empty. Preserve these distinctions in the formal statements.

**Proof-translation experiment.** Model finite subsets using `Finset` or explicit
finite subtypes consistently. Formalize the translation injection and the
addition surjection, using existing finite-cardinality and product-counting lemmas
whose hypotheses match. Record these prerequisites in the experiment's allowed
context. mathlib's
[pointwise set operations](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Pointwise/Set/Basic.html)
help locate the formal objects. Reusing the target cardinality theorem would be
valid corpus curation, but would not translate this injection/surjection argument.

**Why this seed matters.** It checks finiteness/nonemptiness, finite versus infinite
sets, an image-based proof, and a statement useful for further additive combinatorics.
The upper bound could become another block in the existing sumset note.

## Enumerative combinatorics: Pascal's identity

**Definition.** \(\binom{n}{k}\) counts the \(k\)-element subsets of an
\(n\)-element set, and is zero when \(k>n\).

**Statement.** For natural numbers \(n,k\),

\[
\binom{n+1}{k+1}=\binom{n}{k}+\binom{n}{k+1}.
\]

**Human proof.** Distinguish one element \(x\) of an \((n+1)\)-element set.
Partition its \((k+1)\)-element subsets according to whether they contain \(x\).
Removing \(x\) from the first class gives a bijection with the \(k\)-element
subsets of the remaining \(n\) elements. The second class already consists of
the \((k+1)\)-element subsets of those remaining elements. The classes are
disjoint and exhaustive, so their cardinalities add.

**Proof-translation experiment.** Define the two classes and both bijections, and prove the
cardinality-of-disjoint-union step. If using `Nat.choose`, first link it to the
subset-counting interpretation. A proof by its recursive equation alone would
verify the identity but would not formalize this submitted counting argument.
The [binomial coefficient documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Basic.html)
is a reference for the existing formal object.

**Why this seed matters.** It distinguishes a faithful formalization from a short
proof of the same proposition by a different method. It also supplies a good test
for an explanatory diagram and a second, algebraic proof later.

## Graph theory: the handshaking lemma

**Definitions.** A finite undirected simple graph \(G=(V,E)\), with each edge a
two-element subset of \(V\). The degree \(\deg(v)\) counts edges containing \(v\).

**Statement.**

\[
\sum_{v\in V}\deg(v)=2|E|.
\]

**Human proof.** Count incidences \(I=\{(v,e)\in V\times E:v\in e\}\) in two
ways. Counting first by vertices gives \(|I|=\sum_v\deg(v)\). Counting first
by edges gives \(|I|=\sum_e 2=2|E|\), because every edge has exactly two endpoints.

**Proof-translation experiment.** Formalize the incidence set and the two finite
fiber sums, reusing suitable checked counting lemmas as recorded prerequisites.
Do not introduce loops without changing the degree convention. A picture of a
triangle with its six incidences is an appropriate rendering fixture, not a proof
of the general theorem.

**Why this seed matters.** It covers double counting, finite sums, and images whose
mathematical role must remain clear to both readers and agents.

## Baseline acceptance checks

For a measured proof-translation task, check the following. These combine local
commands with manual review; they are not all automated gates in the current app:

- Definitions and hypotheses on the page match the elaborated Lean types.
- Human proof steps have corresponding formal steps and declared prerequisites.
- Complete proofs have no direct or transitive `sorryAx` or disallowed axioms.
  Pending helpers are reported separately and do not make a partial block complete.
- The reviewed statement has the intended hypotheses, including boundary cases;
  compilation alone is not enough. Check for target-theorem shortcuts separately.
- A changed human proof receives fresh review even if the Lean statement is
  unchanged. There is no automatic review-invalidation service yet.
- Desktop, mobile, and print output show inline/display math, long equations,
  images, captions, and alternate proofs correctly.
- Logs preserve the exact input, environment, all attempts, model spending, and
  human correction time. An API or immutable release service is not required.

After these examples work, expand toward Lagrange's theorem, Vandermonde's identity,
and more substantial sumset inequalities. The dependency graph will reveal which
supporting material is missing. mathlib's
[coverage overview](https://leanprover-community.github.io/mathlib-overview)
can guide later areas, without treating upstream coverage as already-present
human exposition in this project.
