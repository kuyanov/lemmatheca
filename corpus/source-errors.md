# Source errors

Last checked: **2026-10-12**. Scope: the publications cited by the current **54
entries**, using their `based_on` locations and the named results those citations
identify, together with explicitly scoped supporting, adjacent, entry-planning, and
mathematical-logic area-planning passages.
The [coverage](#coverage) includes the directly cited publications, checked
supporting material, and separately scoped planning publications and
source versions. Some planning rows cover only metadata, contents, or statements;
their outcomes distinguish those readings from mathematical proof checks.
Duplicate URLs and
chapter extracts of the same edition are grouped.

The main register contains confirmed false statements, missing necessary
hypotheses, invalid constructions, and deductions that fail as written. Each
finding includes mathematical evidence and a checked repair. Missing explanation,
valid compression, differences of convention, and uncertainty are not errors.
[Local mathematical slips](#local-mathematical-slips) are separate and lower
priority. Neither category certifies that the rest of a publication is error-free.

An error recorded here remains present in the inspected source version unless
an upstream correction is explicitly recorded. **Already handled in the corpus**
means our entry uses a correct version; it does not mean the source was corrected.
Errors in adjacent inspected material are explicitly distinguished from arguments
actually used by an entry. Page numbers are printed pages unless marked otherwise.

## Serious mathematical defects

### KAMENSKY-01

**Finite agreement on common domains is not an equivalence relation.**
[Kamensky, *Set Theory*](https://mkamensky.github.io/teaching/2012f/set-theory/notes.pdf),
p. 6, §1.3.8 and the proof of Theorem 1.3.9; course URL `2012f`, embedded
revision dated 2011-12-07. Type: invalid construction.

The proof treats finite disagreement on the common domain as an equivalence
relation on injections of different lengths. Let `s(n)=n` and `u(n)=2n` on
`ω`, and let `t` be the empty function. Then `s∼t` and `t∼u`, but `s≁u`.
Consequently the claimed equivalence classes across the whole tree are not defined.

**Repair and corpus disposition:** use finite-error equivalence only on a fixed
domain. Construct coherent injections `s_α`, then define level `α` by the injections
`t:α→ω` with `t=*s_α`; prove restriction closure using coherence.
Already handled in [finite-change classes](entries/infinite-trees/entry.html#finite-change-classes)
and [the Aronszajn tree](entries/infinite-trees/entry.html#aronszajn-existence).
The source's request to verify finite-collision repair is valid compression and
is not a separate error.

### WEISS-01

**The decimal almost-disjoint construction has an infinite common intersection.**
[Weiss, *An Introduction to Set Theory*](https://www.math.toronto.edu/~weiss/Set_Theory.pdf),
2014-11-21, p. 82, the almost-disjoint paragraph after Exercise 27.
Type: false claim and invalid witness.

The formula for `a_f` fixes decimal positions below `n` and zeros those above
`n`, leaving position `n` unrestricted. Taking `n=0` puts every integer, represented
by its integer coordinate and zero tail, in every `a_f`. Thus `a_f∩a_g` is infinite
even for distinct `f,g`.

**Repair and corpus disposition:** use length-tagged finite prefixes of binary
sequences on the countable set of finite binary words. Distinct sequences have
only finitely many common prefixes. This defective paragraph is adjacent material
in the pages cited by [dense linear orders](entries/dense-linear-orders/entry.html#cantor-back-and-forth),
whose back-and-forth argument is unaffected. It was not adopted by the corpus's
[binary-prefix construction](entries/almost-disjoint-families/entry.html#binary-prefix-family),
which uses other cited sources and already supplies the correct witness.

### CAICEDO-01

**The proposed finite Ramsey recurrence yields a false bound.**
[Caicedo, *580 — III. Partition calculus*](https://andrescaicedo.wordpress.com/2009/03/21/580-iii-partition-calculus/),
2009-03-21, §2, proof of Theorem 4. Type: invalid deduction.

The recurrence starts at `r₁=1` and uses `r_{j+1}=r(k−1,m,r_j)`.
For `k=2,m=2,n=3`, the singleton Ramsey number is always `r(1,2,1)=1`,
so every term stays at 1. The claimed bound would give `r(2,2,3)≤1`, although
one point cannot contain three points (and the actual value is 6).

**Repair and corpus disposition:** include the selected pivot when setting the
reservoir size: using constant-color homogeneity, with empty restrictions
homogeneous vacuously, for positive parameters use `r_{j+1}=1+r(k−1,m,r_j)` and
`M=m(n−1)+1`. Each induction step leaves a tail large enough for the previous
stage. Alternatively use the corpus's checked
[finite Ramsey proof via König's lemma](entries/partition-relations/entry.html#finite-ramsey).
The defective finite-bound argument is adjacent to the cited Theorem 3 and was
not adopted. The entry's [infinite Ramsey proof](entries/partition-relations/entry.html#infinite-ramsey)
uses Theorem 3's valid nested-tail argument.

### CAICEDO-02

**Negating the large-neighborhood alternative gives the wrong cardinal bound.**
[Caicedo, *580 — Partition calculus (5)*](https://caicedoteaching.wordpress.com/2009/04/21/580-partition-calculus-5/),
2009-04-21, §1, singular-cardinal proof of Theorem 1, immediately after the
infinite homogeneous-set recursion. Type: false deduction.

With `κ=cf(λ)`, the source concludes that some `S∈[λ]^λ` has
`|B_α∩S|<κ` for every `α∈S`. The negated alternative yields only `<λ`.
For a counterexample, take `λ=aleph_ω`, partition its ordinal carrier into
cells `A_n` of sizes `aleph_n`, and color pairs 1 within each cell and 0
between cells. Every forward 1-neighborhood has size less than `λ`.
If all these neighborhoods in a full-size `S` were finite (`<cf(λ)`),
the least point of each nonempty `S∩A_n` would see all its other points,
making each intersection finite. Their countable union could not have size `λ`.

**Repair and corpus disposition:** replace this bound by `<λ`.
This corrects the negation step; the rest of the singular proof was not
certified in this review. The current [regular-cardinal dichotomy](entries/uncountable-pair-colourings/entry.html#large-neighbourhood-dichotomy)
already uses the correct ambient-cardinal bound. The singular theorem is
excluded from the entry, so this adjacent defect does not affect its result.

### PHILIP-01

**The countable-choice proof asks for nonexistent bijections.**
[Philip, *Axiomatic Set Theory*](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf#page=167),
revision 2025-12-30, p. 167, Theorem C.10, implication (i) ⇒ (iii).
Type: invalid witness.

The choice family consists of bijections `n→A` with `A` infinite. Every such
set of maps is empty, so countable choice cannot be applied.

**Repair and corpus disposition:** select injections `e_n:n→A`. Their ranges
have an infinite union `B`, since it contains an `n`-element subset for every `n`.
The supplied injections explicitly enumerate `B` using pairs of naturals; taking
first occurrences enumerates it without repetition. No further choice is needed.
Already handled in [countable choice and infinity](entries/weaker-forms-of-choice/entry.html#countable-choice-and-infinity).

### PHILIP-02

**The layer-enumeration minimum can be taken over an empty set.**
[Philip](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf#page=167),
revision 2025-12-30, p. 167, the alternative construction in Theorem C.10.
Type: invalid construction, independently of PHILIP-01.

After repairing the maps to injections, put `e₁(0)=0` and `e₂=(0,1)`.
The new layer `C₁={1}` has size 1. The printed search for its first member
examines only indices below `|C₁|`, hence only `e₂(0)=0`; its candidate set
is empty.

**Repair and corpus disposition:** search the whole domain `n+1` of `e_{n+1}`,
removing values already selected. Every remaining layer member has a preimage,
so the minimum exists. The corpus instead uses the direct pair enumeration in
[countable choice and infinity](entries/weaker-forms-of-choice/entry.html#countable-choice-and-infinity),
which avoids the defective layers.

### PHILIP-03

**Uniqueness of minimal elements does not imply trichotomy for arbitrary relations.**
[Philip](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf#page=59),
revision 2025-12-30, p. 59, Proposition 4.21(a), with minimality as defined on
p. 58. Type: false statement; missing irreflexivity hypothesis.

On `{0,1}`, let `R={(0,0),(1,1)}`. No nonempty subset has a minimal point:
each candidate is its own predecessor. Thus every subset has at most one minimal
point, vacuously, while 0 and 1 are incomparable.

**Repair and corpus disposition:** assume `R` irreflexive for the reverse
implication. Two incomparable distinct points would then both be minimal in
their two-point subset. This is adjacent material: [relation closures](entries/equivalence-relations/entry.html#relation-closures)
uses the valid Proposition 4.21(b), not part (a).

### PHILIP-04

**Injection–surjection equivalence fails for an empty target.**
[Philip](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf#page=99),
revision 2025-12-30, Corollary 5.13(d), statement p. 99 and proof p. 100.
Type: false statement; missing necessary hypothesis.

Take `B=∅` and `κ=1`. There is an injection `B→κ` but no function `κ→B`,
let alone a surjection.

**Repair and corpus disposition:** require `B≠∅`, or state that `B` injects
into `κ` iff `B=∅` or `κ` surjects onto `B`. For a nonempty image, pad the
inverse of the injection with its least image point; conversely choose each
surjection fiber's least ordinal. The proof overlaps a cited page, but the
entry uses the unaffected [Hartogs theorem](entries/axiom-of-choice/entry.html#hartogs-bound)
and first-uncountable-ordinal definition, not this corollary.

### HALBEISEN-01

**The proposed bound does not strictly dominate its input functions.**
[Halbeisen, *Combinatorial Set Theory*](https://user.math.uzh.ch/halbeisen/publications/pdf/cst.pdf#page=208),
2011-11-17, pp. 191–192, Theorem 8.3 and its strict eventual-order convention.
Type: invalid witness.

The witness takes a maximum of initial function values without incrementing it.
If all input functions are constantly 0, the proposed bound is also constantly 0,
which does not strictly dominate any of them.

**Repair and corpus disposition:** take
`h(k)=1+max({g_i(k):i<k}∪{0})`. For each fixed `i`, every `k≥i+1` then
satisfies `g_i(k)<h(k)`. Already handled in the
[countable eventual bound](entries/finite-errors-and-countable-diagonalization/entry.html#countable-eventual-bound),
reused by [the bounding-number inequalities](entries/bounding-and-dominating-families/entry.html#basic-inequalities).
The entry also explicitly distinguishes strict and nonstrict conventions.

### SWITZER-01

**The bounded-family definition quantifies over the entire function space.**
[Switzer, *Lecture Notes on Iterated Forcing*](https://coreyswitzer.wordpress.com/wp-content/uploads/2021/12/complete-lecture-notes.pdf#page=18),
Vienna winter term 2021, p. 18, paragraph before Definition 4.17.
Type: false definition.

The bound must dominate all of `ω^ω` instead of the members of `B`. For every
proposed `g`, the function `g+1` defeats it. Literally even the empty family is
therefore unbounded, making the subsequent minimum 0 instead of an uncountable
cardinal. The earlier definition on p. 1 has the correct quantifier.

**Repair and corpus disposition:** boundedness is
`∃g∈ω^ω ∀f∈B (f≤*g)`. Already handled, including the empty family, in
[bounded and dominating families](entries/bounding-and-dominating-families/entry.html#bounded-and-dominating).

### SWITZER-02

**Cofinal indices are applied to the wrong sequence in the regularity proof.**
[Switzer](https://coreyswitzer.wordpress.com/wp-content/uploads/2021/12/complete-lecture-notes.pdf#page=18),
winter term 2021, p. 18, proof of Lemma 4.18.
Type: invalid deduction.

The primed sequence is made increasing, but the selected cofinal-index family
uses the unprimed terms. The needed implication is false even with distinct
original functions: let `f_{2n}` be 1 at coordinate `n` and 0 elsewhere,
and let `f_{2n+1}` be constantly `n+1`. Set `f′₀=f₀` and let `f′_m` be
constantly `m+2` for `m≥1`. The primed terms increase eventually and bound
the preceding and corresponding original terms. The even indices are cofinal,
yet all their unprimed terms are eventually zero and are not cofinal in the
primed sequence. This tests the inference, not the proof's contradictory
singularity assumption.

**Repair and corpus disposition:** select the **primed** terms at cofinal
indices. Their increasingness makes this subfamily cofinal and hence unbounded,
giving the required smaller unbounded family. The corpus instead uses the
checked cofinal-cover and small-union argument in
[regularity of the bounding number](entries/bounding-and-dominating-families/entry.html#bounding-number-regular).

### UNGER-01

**The MAD definition permits counterexamples to the claimed lower bound.**
[Unger, *Forcing Summer School Lecture Notes*](https://math.huji.ac.il/~sunger/ucla/LogicSummerSchool/ForcingNotes.pdf#page=6),
2013-07-15, pp. 5–6, Definitions 2.3/2.6, Lemma 2.5 and Theorems 2.7–2.8.
Type: false statements; missing necessary hypotheses.

Definition 2.3 permits finite members and finite families. Under its
infinite-intersection criterion `{ω}` is MAD, so the invariant later minimized
over all MAD families equals 1. Even reading “countable” as countably infinite
does not rescue Lemma 2.5: `Fin∪{ω}` is a countably infinite pairwise almost
disjoint family, maximal among arbitrary subsets of `ω`. Every finite subset
is already present and any additional infinite set meets `ω` infinitely.

**Repair and corpus disposition:** take members in `[ω]^ω`, state the extension
lemma for **countably infinite** families, and minimize `a` over **infinite** MAD
families. Finite MAD families remain legitimate examples. Already handled in the
corpus's [almost-disjoint definition](entries/almost-disjoint-families/entry.html#almost-disjoint),
[finite maximal-family question](entries/almost-disjoint-families/entry.html#finite-maximal-family-question),
and [countable-family extension](entries/almost-disjoint-families/entry.html#countable-family-extension).
The [small-family minima](entries/small-families-of-subsets/entry.html#three-minima)
now define the almost-disjointness number using infinite MAD families. The
[uncountability bound](entries/small-families-of-subsets/entry.html#uncountable-minima)
and [bounding-number comparison](entries/small-families-of-subsets/entry.html#bounding-below-almost-disjointness)
retain these hypotheses.

### UNGER-02

**The cutoff for a set's intersection with itself does not exist.**
[Unger](https://math.huji.ac.il/~sunger/ucla/LogicSummerSchool/ForcingNotes.pdf#page=6),
2013-07-15, p. 6, Theorem 2.8. Type: invalid construction,
even after the MAD hypotheses in UNGER-01 are repaired.

The proposed `f_α(n)` is above every element of `A_n∩A_α` for all `α<κ`.
At `α=n` this intersection is the infinite set `A_n`, which is unbounded in `ω`.
No such natural-number cutoff exists.

**Repair and corpus disposition:** disjointify the first `ω` sets by removing
their finitely many intersections with predecessors. Define cutoff functions only
for `α≥ω`, bound them strictly, and select sufficiently late elements of those
first sets. The selected set meets each first set once and each remaining member
only finitely. This repairs the intended inequality `b≤a`. It is adjacent
material on a cited page. The
[bounding-number comparison](entries/small-families-of-subsets/entry.html#bounding-below-almost-disjointness)
now supplies the repaired disjointification and cutoff argument. The
[almost-disjoint entry](entries/almost-disjoint-families/entry.html#maximal-almost-disjoint)
only uses maximal-family extension and does not require this inequality.

### MARKS-01

**The right-inverse formulation of Choice omits surjectivity.**
[Marks, *Set Theory*](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=12),
revision 2026-01-31, §2, p. 12. Type: false statement.
The function `{0}→{0,1}` taking 0 to 0 has no right inverse: the section identity
at 1 would say `0=1`. Require every **surjection**, rather than every function,
to have a section. Already correct in
[sections of surjections](entries/axiom-of-choice/entry.html#sections-of-surjections).

### MARKS-02

**Dependent choice is false on an empty carrier.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=38),
revision 2026-01-31, §8.1, pp. 37–38. Type: missing necessary hypothesis.
The empty relation on `X=∅` satisfies the displayed seriality condition
vacuously, but no sequence `ω→X` exists. Require `X≠∅`, or supply a starting
point in `X`. Already handled in
[dependent choice](entries/weaker-forms-of-choice/entry.html#dependent-choice)
and [its starting-point version](entries/weaker-forms-of-choice/entry.html#starting-point-version).

### MARKS-03

**Strict ordinal multiplication needs a positive left factor.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=25),
revision 2026-01-31, Exercise 5.10(2), p. 25. Type: false statement.
Taking `α=0, γ=0, β=1` in `γ<β ⇒ α·γ<α·β` gives `0<0`.
Add `α>0`; nonstrict monotonicity needs no such restriction. Already correct in
[multiplication comparison](entries/ordinal-arithmetic/entry.html#multiplication-comparison).

### MARKS-04

**Cantor normal form cannot be unique if zero coefficients are allowed.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=26),
revision 2026-01-31, Exercise 5.14, p. 26. Type: false uniqueness statement.
Both `ω⁰·1` and `ω¹·0+ω⁰·1` represent 1 with natural coefficients and
decreasing exponents. Require positive coefficients and represent zero by the
empty expression. Already correct in
[Cantor normal form](entries/ordinal-powers/entry.html#cantor-normal-form).

### MARKS-05

**Cardinal powers are not exponent-monotone at the empty-base boundary.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=40),
revision 2026-01-31, Exercise 9.10(2), p. 40. Type: false statement.
Take the base and smaller domain empty and the larger domain a singleton.
Then `0⁰=1` and `0¹=0`, contradicting the asserted inequality.
A nonempty base supplies a fixed value for extending functions and repairs the
claim. Already handled in [monotone cardinal powers](entries/infinite-sums-and-products/entry.html#monotone-cardinal-powers)
and [empty function cases](entries/infinite-cardinal-arithmetic/entry.html#empty-function-cases).

### MARKS-06

**Aleph continuity conflicts with the source's zero-as-limit convention.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=39),
revision 2026-01-31, Exercise 9.5, p. 39, and the cofinality example on p. 45;
compare Definition 4.17, p. 20. Type: false boundary statements.
Zero is a limit under the source's convention. At zero,
`ω_α=sup_{β<α}ω_β` would say `ω=0`, and `cf(ω_α)=cf(α)` would say
`ω=0` again. Require a **nonzero** limit index. The limit convention itself is
legitimate. Already handled in
[aleph and beth sequences](entries/continuum-function/entry.html#aleph-and-beth-sequences).

### MARKS-07

**The cofinality of a limit need not be infinite if zero counts as a limit.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=44),
revision 2026-01-31, Exercise 10.3, p. 44. Type: missing necessary hypothesis.
The empty map is cofinal in zero under Definitions 10.1–10.2, so `cf(0)=0`.
The exercise's conclusion `cf(α)≥ω` therefore needs a **nonzero** limit ordinal.
Already correct in [limit cofinality](entries/cofinality/entry.html#limit-cofinality).

### MARKS-08

**The club-closure definition forces zero into every club and breaks stationarity.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=61),
revision 2026-01-31, Definition 14.1 and Exercise 14.2, p. 61;
consequences in Exercises 14.3, 14.7 and 14.11(2), pp. 61–63.
Type: inconsistent definition and false consequences.

The source tests all limit ordinals, including zero, and allows an empty
sequence in the equivalent criterion. The empty set is cofinal in zero and
its supremum is zero, so every closed set must contain zero. Consequently `{0}`
is stationary in `ω₁`, contradicting the stated unboundedness of stationary sets;
two disjoint clubs are impossible, contrary to another exercise.

**Repair and corpus disposition:** test only nonzero limit points, or use
nonempty increasing sequences in the supremum criterion. Already handled in
[closed unbounded sets](entries/clubs-and-stationary-sets/entry.html#closed-unbounded),
[the boundary question](entries/clubs-and-stationary-sets/entry.html#cofinality-boundary-question),
and [stationary properties](entries/clubs-and-stationary-sets/entry.html#stationary-properties).

### MARKS-09

**A club filter and club diagonal intersections require uncountability.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=63),
revision 2026-01-31, Definition 14.8, p. 62, and Theorem 14.14, p. 63.
Type: missing necessary hypothesis.

At the regular cardinal `κ=ω`, even retaining the source's zero-containing
closure convention, `{0}∪evens` and `{0}∪odds` are clubs but their intersection
contains no club. Moreover `C_n={0}∪{m:m≥n+2}` are clubs whose diagonal
intersection is `{0}`: for `m>0`, index `m−1<m` excludes `m`.

**Repair and corpus disposition:** require `κ` regular **uncountable**, as the
countable-supremum argument needs. Already handled in
[the club filter](entries/clubs-and-stationary-sets/entry.html#club-filter)
and [diagonal intersection](entries/clubs-and-stationary-sets/entry.html#diagonal-intersection).

### MARKS-10

**The Δ-system root bins omit their possible maximum.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=65),
revision 2026-01-31, Lemma 15.2, p. 65. Type: failed partition construction.
The proof bins roots into finite subsets of `γ` after bounding their supremum
by `γ`. Take `X₀=∅` and `X_α={0,α}` for `α>0`. On every positive index
the root is `{0}` with supremum `γ=0`, yet `{0}` is not a subset of `γ`.
Use finite subsets of `γ+1`. Already corrected in
[the Δ-system lemma](entries/pressing-down-and-delta-systems/entry.html#delta-system-lemma).

### MARKS-11

**The claimed closure-point witness does not give the Δ-system proof's club.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=65),
revision 2026-01-31, Lemma 15.2, p. 65. Type: invalid witness identification.
The proof identifies `C={α:∀β<α, X_β⊆α}` with closure points of
`f(δ)=sup⋃_{β<δ}X_β`. For `X_β={β+1}`, one has `f(0)=0` and `f(δ)=δ`
for positive `δ`. Thus 1 is a closure point but is not in `C`, since
`X₀={1}` is not a subset of ordinal 1.

**Repair and corpus disposition:** use `h(β)=sup{x+1:x∈X_β}` and its
closure-point club restricted to nonzero limits. It is contained in `C`, which
suffices for thinning; an exact identification is unnecessary.
Already handled in [the Δ-system proof](entries/pressing-down-and-delta-systems/entry.html#delta-system-lemma).

### MARKS-12

**The full function tree's height assertion fails for an empty alphabet.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=68),
revision 2026-01-31, §16, p. 68, example before Lemma 16.1.
Type: missing necessary hypothesis.
For `X=∅, κ=ω`, the only function node is the empty root and the tree has
height 1, rather than `κ`. Require `X≠∅`; constant functions then populate
every prescribed level. Already correct in
[sequence trees](entries/infinite-trees/entry.html#sequence-trees).

### MARKS-13

**The Aronszajn construction can repeatedly reserve the same value.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=69),
revision 2026-01-31, Theorem 16.3, p. 69. Type: failed limit construction.

At the limit `α=ω`, take `α_n=n` and the permitted coherent finite injections
`s_n(i)=i+1`. The extension maps can remain `s_n`. The reserve update always
chooses the least number outside the current range, namely 0. All nonempty
reserves therefore equal `{0}`, rather than having size `n`; the union's range
is `ω\{0}`, which is not coinfinite. The required limit invariant fails.

**Repair and corpus disposition:** choose the next reserve outside both the
current range **and the old reserve**. The coinfinite extension leaves enough
fresh values; reserves then grow by one at every step. Already handled in
[coherent injections](entries/infinite-trees/entry.html#coherent-injections).
The finite-collision completion itself is valid compression, not another error.

### MARKS-14

**The indecomposability characterization needs a positive ordinal.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=27),
revision 2026-01-31, Exercise 5.17, p. 27. Type: false boundary equivalence.
Zero has no decomposition into two smaller ordinals and satisfies the displayed
partition condition vacuously, but is not `ω^ξ` for any `ξ`. Restrict to positive
ordinals. This is unused exercise material in the pages cited by
[normal functions](entries/normal-functions/entry.html#hereditary-ordinal-forms),
not a claim that entry imports.

### MARKS-15

**The all-set formulation of GCH also quantifies over finite counterexamples.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=41),
revision 2026-01-31, Exercise 9.16, p. 41. Type: false formulation.
Set sizes 2 and 3 satisfy `2≤3≤2²`, but 3 equals neither endpoint. Thus the
literal condition for every set cannot express GCH. Restrict the starting set to
infinite sets. This ZF exercise is unused; the corpus's
[GCH definition](entries/continuum-function/entry.html#gch) already uses infinite cardinals.

### MARKS-16

**The cofinal-power bound is false for finite cardinals.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=49),
revision 2026-01-31, Exercise 11.10, p. 49. Type: missing necessary hypothesis.
At `κ=1`, `2^{<κ}=1` and `cf(κ)=1`, so
`2^κ≤(2^{<κ})^{cf(κ)}` says `2≤1`. Require infinite `κ`.
The exercise is adjacent to the cited [continuum-function material](entries/continuum-function/entry.html#continuum-restrictions)
and is not asserted by a current entry.

### MARKS-17

**The filter characterization makes its regressive-function condition vacuous.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=64),
revision 2026-01-31, Exercise 14.16, p. 64. Type: false equivalence.
There is no `f:κ→κ` with `f(α)<α` also at zero, so the printed Fodor condition
holds for every filter. Yet the cofinite filter on `ω₁` is not normal: diagonal
intersection of `ω₁\{ξ+1}` omits every positive successor and is not cofinite.
State the regressive condition on the positive set being thinned. This abstract
filter exercise is not imported; the corpus's
[regressive functions](entries/pressing-down-and-delta-systems/entry.html#regressive-functions)
and [Fodor lemma](entries/pressing-down-and-delta-systems/entry.html#fodors-lemma)
already have the correct domain.

### MARKS-18

**The Wetzel proof uses a discrete interpolation set and reverses its indices.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=50),
revision 2026-01-31, Theorem 11.12, pp. 50–51. Type: failed construction.

`Z+iZ` is discrete, so it cannot supply the claimed arbitrarily close
interpolation values. Moreover the written condition controls later points of
each earlier entire function, while the recursion controls earlier points of
each later function. The written condition forces each function's whole range
to be countable and hence each entire function to be constant, defeating the
uncountable-family construction. The opposite-direction bounded-set proof also
uses circles of integer radius as a cover of the plane; they do not cover it.

**Repair and corpus disposition:** use the countable dense set `Q+iQ` and,
for `α<β`, require both `f_β(z_α)∈D` and `f_β(z_α)≠f_α(z_α)`.
Thus both pair conditions concern the earlier point for each later function.
At a stage with infinitely many predecessors, enumerate their distinct points
as `w_n`. Choose the Newton correction
`ε_n∏_{j<n}(z−w_j)` to put the value at `w_n` in `D`, avoiding the one
forbidden predecessor value, and to have supremum at most `2^{-n}` on
`|z|≤n+1`. The interpolation map has nonzero slope at `w_n`; density of
`D` with one value removed permits an arbitrarily small correction. These
bounds give uniform convergence on every compact disk to an entire function;
later terms vanish at already treated points. Finite predecessor lists use a
finite polynomial.
Use closed disks in the bounded-set argument, considering distinct function pairs.
The theorem itself is not refuted. This is unused analytic material in pages
cited by [the continuum-function entry](entries/continuum-function/entry.html#strong-limits-and-sch);
no current entry develops Wetzel's problem.

### BUTTON-01

**An injection with empty domain need not have a left inverse.**
[Button / Open Logic, *Set Theory: An Open Introduction*](https://st.openlogicproject.org/settheory-screen.pdf#page=60),
July 2026 revision, Proposition 4.16, p. 47 (PDF p. 60).
Type: missing necessary hypothesis.
The empty function `∅→{0}` is injective but a left inverse would map `{0}`
into `∅`. Require a nonempty domain, or allow the empty self-map as the other
case. The corpus's [inverse maps](entries/sets-and-maps/entry.html#inverse-maps)
and [empty-map question](entries/sets-and-maps/entry.html#empty-maps-question)
do not import the false converse.

### BUTTON-02

**The untagged word representation identifies words of different lengths.**
[Button / Open Logic](https://st.openlogicproject.org/settheory-screen.pdf#page=37),
July 2026 revision, Example 2.28, p. 24 (PDF p. 37), using the tuple coding on
pp. 22–23. Type: invalid representation.
One-letter words are represented by their letters, the empty word by `∅`, and
all lengths are combined by ordinary union. With alphabet `{∅}`, the empty word
equals the represented one-letter word. Length is therefore not well-defined.
Use functions `n→A`, or a disjoint union of tuples tagged by `n`.
This construction is in a cited range but is not adopted by the corpus's
[pairs and relations](entries/sets-and-maps/entry.html#pairs-and-relations)
or [finite products](entries/finite-and-countable-sets/entry.html#finite-products).

### BUTTON-03

**Signed cut multiplication leaves negative-times-zero undefined.**
[Button / Open Logic](https://st.openlogicproject.org/settheory-screen.pdf#page=94),
July 2026 revision, §6.4, p. 81 (PDF p. 94). Type: incomplete operation definition.
The nonnegative clause requires both factors nonnegative; the mixed-sign clauses
require the positive factor strictly positive. For the cuts of `−1` and `0`,
none applies. The reversed product is likewise undefined.
Specify zero whenever either factor is zero before applying the nonzero sign
rules. Already handled in [cut multiplication](entries/constructing-number-systems/entry.html#cut-multiplication).

### BUTTON-05

**The general closure lemma applies a partial-domain map outside its domain.**
[Button / Open Logic](https://st.openlogicproject.org/settheory-screen.pdf#page=109),
July 2026 revision, Definition 7.2 and Lemma 7.3, pp. 96–97 (PDF pp. 109–110).
Type: missing necessary typing hypothesis.
For `f:{0}→{1}` and starting point 0, closure first requires 1, where `f`
has no value. The proposed witness `ran(f)∪{0}` is not closed under a function
defined on all its members. Require an endomap `f:A→A` and take closure inside
`A`; then `A` is an initial closed witness.
Already correctly typed in [the natural-number system](entries/natural-numbers-as-sets/entry.html#unique-natural-number-system).

### BUTTON-06

**Successor injectivity on an arbitrary inductive witness uses an unavailable assumption.**
[Button / Open Logic](https://st.openlogicproject.org/settheory-screen.pdf#page=139),
July 2026 revision, p. 126 (PDF p. 139), paragraph before Definition 9.7;
the announced `Z−` system on p. 128 omits Foundation.
Type: false assertion in the stated axiom setting.

Without Foundation, a two-cycle `a={b}, b={a}` with distinct `a,b` can occur.
Then both successors equal `{a,b}`. An inductive set containing this cycle,
the empty set and their successor closures is an Infinity witness on which
successor is not injective. This does not refute the Dedekind-infinity of an
Infinity witness: after extracting `ω`, shift its natural-number elements and
fix the other elements. It refutes the particular proposed map `S|I`.

The cycle exists in a relative countermodel, rather than merely being
postulated. In any model `M` of ZF, let `a=0ᴹ`, `b=1ᴹ`, `c={b}ᴹ`, and
let `π` swap `a,c`, fixing everything else. Define `x E y` by
`x∈ᴹπ(y)`. The new empty set is `c`, and under `E` the extensions of `a,b`
are `{b},{a}`. Extensionality transfers through the bijection `π`. Pairing,
Union, Powerset, and Separation transfer by applying `π` to the corresponding
old set witnesses, translating formulas into the definable relation `E`.
For Infinity, old recursion and Replacement collect the orbits of `a,b,c`
under the new successor `F(x)=π(π(x)∪{x})` into an old set `W`.
Then `π(W)` is `E`-inductive and contains the cycle, while
`F(a)=F(b)=π({a,b})`. Thus the advertised injection fails in a model of the
announced axioms without Foundation.

**Repair and corpus disposition:** extract the least inductive set `ω` first
and establish successor injectivity on its ordinal elements. The corpus does
this in [Peano properties](entries/natural-numbers-as-sets/entry.html#peano-properties),
with the [least inductive set](entries/natural-numbers-as-sets/entry.html#least-inductive-set).
Alternatively introduce Foundation earlier, making the stronger assumptions explicit.

### BUTTON-07

**The recursion-defining term has no empty-history case.**
[Button / Open Logic](https://st.openlogicproject.org/settheory-screen.pdf#page=165),
July 2026 revision, Theorem 11.5, p. 152 (PDF p. 165).
Type: incomplete defining construction.
The fallback handles objects that are not ordinal-domain functions; other cases
handle successor and limit domains. The empty function has ordinal domain zero,
which is neither a successor nor a limit under Definition 10.29. No clause
assigns `ξ(∅)`, despite the subsequent assertion `ξ(∅)=A` and invocation of
a total-term recursion theorem.
Explicitly set the value on empty histories to `A`.
Already handled in [set-valued ordinal recursion](entries/cumulative-hierarchy/entry.html#set-valued-ordinal-recursion)
and [the hierarchy definition](entries/cumulative-hierarchy/entry.html#hierarchy-definition).

### PILA-01

**The order-sum successor witness loses the first summand.**
[Pila, *B1.2 Set Theory*](https://www.maths.ox.ac.uk/system/files/attachments/SetTheoryHT18.pdf#page=37),
HT2018, Proposition 14.7, p. 37. Type: invalid isomorphism witness.
After mapping `X∪Z` onto `α+δ`, the extension is given codomain `δ+1` and
last value `δ`. For `α=1, δ=0`, it sends both points to 0.
The codomain must be `(α+δ)+1` and the new value `α+δ`; at limits use
compatible maps onto `α+δ` and take their union.
Already correct in [ordered sums](entries/ordinal-arithmetic/entry.html#ordered-sums)
and [addition recursion](entries/ordinal-arithmetic/entry.html#addition-recursion).

### BAYS-01

**The finite-subset surjection is not a function into its stated codomain.**
[Bays, *B1.2 Set Theory*](https://people.maths.ox.ac.uk/bays/teaching/b1set/B1.2.pdf#page=43),
HT26, p. 43, proof of Theorem 10.2(ii). Type: invalid witness.
`B(n)` denotes exactly `n`-element subsets, but the proposed map on all `B^n`
takes `(b,b)` to a singleton when `n=2`. Restrict its domain to tuples with
distinct coordinates; handle `n=0` separately by `B(0)={∅}`.
The corpus's [finite-subset family](entries/finite-and-countable-sets/entry.html#finite-subset-family)
uses a correct injective binary code instead.

### BAYS-02

**The independence and span formulas quantify over the wrong set.**
[Bays](https://people.maths.ox.ac.uk/bays/teaching/b1set/B1.2.pdf#page=43),
HT26, Definition 10.1, pp. 42–43. Type: false definitions.
The displayed formulas use `b_i∈V` rather than `b_i∈B`, so the independence
condition fails even for empty `B` (choose `b₁=0, a₁=1`), while the displayed
span equals `V` even for empty `B`. Independence also needs distinct `b_i`:
repeating a vector with coefficients 1 and −1 creates a spurious dependence.
Use distinct vectors of `B` for independence and vectors of `B` for span,
including the empty combination.
This is adjacent algebraic material on the cited
[finite-subset proof's page](entries/finite-and-countable-sets/entry.html#finite-subset-family);
no current entry imports these algebraic definitions.

### TEREK-01

**The congruence-quotient class count needs a positive modulus.**
[Terek, *Equivalence Relations, Quotients, and Examples*](https://math-terek.github.io/texts/quotients.pdf#page=2),
undated PDF, Example 5, p. 2. Type: false boundary statement.
The modulus is allowed to be any integer, but the class count is stated as `m`.
For `m=0`, congruence is equality and the quotient is infinite; for `m=−2`,
it has two classes. Require `m>0`, or use `|m|` when nonzero and separate zero.
Already correctly restricted in the corpus's
[class-arithmetic question](entries/equivalence-relations/entry.html#adding-classes).

### TEREK-02

**All codomain fibers do not form a partition when some outputs are missed.**
[Terek](https://math-terek.github.io/texts/quotients.pdf#page=3),
undated PDF, p. 3, paragraph after Proposition 2. Type: missing necessary restriction.
For `f:{a}→{0,1}` taking `a` to 0, codomain fibers include both `{a}` and
`∅`; a partition's blocks must be nonempty. Index by `f(X)`, discard empty
fibers, or assume surjectivity. Already handled in
[the fiber question](entries/equivalence-relations/entry.html#finite-fibers-question)
and [quotient as image](entries/equivalence-relations/entry.html#quotient-is-image).

### MAKKAI-02

**The increasing-union proof applies infinite cardinal absorption to finite sets.**
[Makkai, *Inaccessible cardinals*, §13](https://www.math.mcgill.ca/makkai/SetTheory/SETSEC13.pdf),
pp. 133–136, Lemma (2), especially the successor step on p. 135.
Type: false intermediate claim and invalid deduction.

The lemma permits finite sets with strictly increasing sizes. For `α=ω` and
`B_n={0,…,n}`, its `C_β=⋃_{γ<β}B_γ` gives `|C₂|=2` and `|C₃|=3`.
The claimed `|C₃\C₂|=λ₃=3` is false: the difference has one element.
The proof uses infinite absorption without an infinitude hypothesis. Also,
`B₀=∅` gives `C₀=C₁`, contrary to its universal strict-growth assertion.

**Repair and corpus disposition:** for finite sizes `n<m`, both the ordinal
and set differences have size `m−n`; choose the required bijection directly.
Retain the absorption argument when the larger cardinal is infinite, and allow
the initial empty equality. The union-cardinality conclusion remains true.
This supporting planning passage is unused by current entries; the proposed
inaccessible-cardinal scope needs only the corrected union fact.

### LIETZ-01

**A tree representing an entire perfect real set need not permit unique binary representations.**
[Lietz, *Set Theory — Lecture Notes*](https://andreas-lietz.github.io/resources/PDFs/Lecture_Notes.pdf),
version 2025-02-27, pp. 6–7, proof of Lemma 1.12. Type: false intermediate claim.

The proof requires a perfect binary tree representing all of `P` whose distinct
branches evaluate to distinct reals. Take `P=[0,1]`. Every finite binary word
is a prefix of the unique expansion of some nondyadic real. A tree representing all
these reals therefore contains every finite word. Its branches `1000…` and
`0111…` both evaluate to `1/2`, contradicting injectivity.

**Repair and corpus disposition:** construct a thinner perfect subtree with
injective evaluation; its real image may be a proper subset of `P`. Alternatively,
prove the branch-cardinality result directly in sequence space. Lemma 1.12's
cardinality conclusion remains true. This is planning-only material, unused by
current entries; [Perfect subtrees](entries/perfect-subtrees/entry.html#binary-splitting) uses the sequence-space proof.

### AVIGAD-LC-01

**Upward Löwenheim–Skolem omits the infinite starting-model hypothesis.**
[Avigad, *Logic and Computation*](https://www.andrew.cmu.edu/user/avigad/Teaching/landc_notes.pdf),
January 2002, §7.4, Theorem 7.4.2, p. 91 (PDF p. 97).
Type: missing necessary hypothesis.

A one-element structure satisfies `∀x∀y x=y`, so every elementary extension
also has one element. It cannot have an elementary extension of any infinite
cardinality, although the displayed size bounds allow one.

**Repair and corpus disposition:** require the starting structure to be infinite,
with the stated language/model lower size bounds. Use its elementary diagram,
compactness, and downward Löwenheim–Skolem to obtain the desired cardinality.
Planning only; the affected proposed entry is `models-and-independence` in the
[logic roadmap](reference-planning.md#mathematical-logic-sources-and-development-plan).
This is not a finding about Avigad's different 2022 book.

### AVIGAD-LC-02

**The preservation proof uses a positive diagram where an embedding needs negated atoms.**
[Avigad, *Logic and Computation*](https://www.andrew.cmu.edu/user/avigad/Teaching/landc_notes.pdf),
January 2002, §7.6, proof of Theorem 7.6.1, p. 96 (PDF p. 102).
Type: invalid model-construction step.

The diagram is redefined using only positive atomic facts, then its consistency
with a theory is treated as sufficient for a substructure embedding. In a
language with a unary predicate `P`, take a singleton structure where `P` is
false and a theory requiring `∀x P(x)`. The positive diagram is consistent with
that theory, but the singleton cannot embed as a substructure of a model of it:
an embedding must reflect `P`, too. This counterexample identifies the failed
diagram-to-embedding step; it does not refute the preservation theorem.

**Repair and corpus disposition:** include all true atomic and negated atomic
sentences with names for the structure's elements, as the notes correctly do
in §7.4, p. 92. That signed atomic diagram gives an embedding. A merely positive
diagram does not. Planning only; preservation is a later model-theory extension,
not a theorem currently used by an entry.

### DOETS-01

**The Łoś–Vaught test allows finite models that defeat completeness.**
[Doets, *Basic Model Theory*](https://web.stanford.edu/group/cslipublications/cslipublications/Online/doets-basic-model-theory.pdf),
CSLI / FoLLI, 1996, §3.44, p. 44 (PDF p. 52).
Type: missing necessary hypothesis.

The stated assumptions require an infinite model and categoricity in an
infinite cardinal, rather than excluding finite models. The empty theory in
the equality-only language has one isomorphism type at every infinite cardinal,
but its one-element and two-element models disagree on `∀x∀y x=y`.
It is therefore incomplete.

**Repair and corpus disposition:** require no finite models. Downward and upward
Löwenheim–Skolem then bring any two disagreeing models to the categorical
cardinality, a contradiction. This is adjacent planning material, not currently
adopted. The selected witness-closure and countable back-and-forth arguments
are different passages.

### SCHLICHT-01

**Dense-order quantifier elimination discards conditions on the parameters.**
[Schlicht, *Lecture Notes: Introduction to Mathematical Logic*](https://philippschlicht.github.io/teaching/files/mathematicallogic2021.pdf),
Bonn summer 2021, PDF dated 2022-02-01, §5.1, proof of Lemma 5.1.6,
pp. 65–66 (same PDF pages). Type: false elimination formulas.

After splitting a conjunction into a parameter-only part `φ₀` and constraints
on the eliminated variable, the proof returns truth for one-sided bounds.
But `∃y (x₁<x₂ ∧ x₃<y)` is equivalent to `x₁<x₂`, rather than truth.
The two-sided conclusion also needs to retain every comparison between a
lower-bound and an upper-bound parameter; choosing one compatible ordering
does not eliminate these conditions for other assignments.

**Repair and corpus disposition:** retain `φ₀`; for two-sided bounds conjoin it
with all lower/upper comparisons. Finite maxima/minima, density, and no endpoints
prove the resulting equivalence. Handle equalities separately as in the usual
substitution case. The quantifier-elimination theorem is correct after this
repair. Planning only; this is a possible later logic branch, not an adopted
corpus proof.

### AVIGAD-CI-01

**The minimization formula checks the parameter instead of the proposed least witness.**
[Avigad, *Computability and Incompleteness*](https://www.andrew.cmu.edu/user/avigad/Teaching/candi_notes.pdf),
version 2007-01-09, §4.3, p. 98 (PDF p. 102), immediately before Lemma 4.3.9.
Type: invalid representability formula.

The least-zero condition bounds the earlier candidates by `w<z`, where `z`
is a side parameter, instead of `w<y`, where `y` is the proposed output.
Take `g(0,z)=1` and `g(x,z)=0` for `x>0`. Its least zero is 1, but with
`z=0` the displayed condition also accepts `y=2`: the earlier-candidate test
is empty. The claimed unique output is lost.

**Repair and corpus disposition:** replace that bound by `w<y` and retain the
convergence checks for earlier computations. Zach's *Incompleteness and
Computability*, §4.7, pp. 92–96, supplies the corrected construction and numeral
order reasoning in Q. Planning only; apply the repair in the proposed
`arithmetic-representability` entry, which has no drafted blocks yet.

### AVIGAD-CI-02

**The undecidability corollary omits consistency of the extension.**
[Avigad, *Computability and Incompleteness*](https://www.andrew.cmu.edu/user/avigad/Teaching/candi_notes.pdf),
version 2007-01-09, Corollary 4.4.14, p. 107 (PDF p. 111).
Type: missing necessary hypothesis.

It prohibits every decidable extension of ZFC. An inconsistent extension proves
every sentence, so its deductive closure is decidable. The notes explicitly allow
inconsistent theories nearby; the qualifier cannot be inferred as a general
convention.

**Repair and corpus disposition:** prohibit **consistent** decidable extensions
of ZFC. The following Corollary 4.4.15 includes this qualification. Planning only;
the first-incompleteness/undecidability development must state consistency and
effective-axiom hypotheses explicitly.

### MARKER-01

**The compactness construction's single-generator family need not be a filter.**
[Marker, *Model Theory for Algebra and Algebraic Geometry*, Orsay sections 1–3](https://homepages.math.uic.edu/~marker/orsay/orsay1.pdf),
Spring 2010, §3, alternate compactness proof, p. 23 (same PDF page).
Type: invalid ultrafilter-extension prerequisite.

For a theory `Γ`, the proof uses finite subsets as indices and defines its
family by supersets of individual sets `X_φ={Δ: Δ⊨φ}`, for `φ∈Γ`.
With `Γ={P(c),Q(c)}`, both `X_P` and `X_Q` belong to the family, while their
intersection contains neither generator. The family is not closed under
intersection. The proof silently treats `P(c)∧Q(c)` as another member of `Γ`.
For empty `Γ`, the displayed family is empty as well.

**Repair and corpus disposition:** generate a filter using all finite
intersections, including the empty intersection, or use the upward cones of
finite subsets of `Γ`. Finite satisfiability gives properness, after which
ultrafilter extension and Łoś apply. Marks §13, pp. 57–58, uses the finite-cone
route. Planning only; apply the repair in the proposed `ultraproducts` entry.

### MARKS-21

**The hereditary-size model claim includes a structure that fails Infinity.**
[Marks, *Set Theory*](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=80),
revision 2026-01-31, Exercise 18.17, p. 80 (same PDF page).
Type: missing necessary hypothesis.

The exercise claims that `H_κ` satisfies ZFC minus Power Set for every regular
cardinal `κ`. The regular cardinal `ω` gives `H_ω`, the hereditarily finite sets.
No member is inductive: an inductive set contains every finite ordinal and is
infinite. Thus this structure fails Infinity.

**Repair and corpus disposition:** require `κ` regular **uncountable**;
alternatively omit Infinity as well for `κ=ω`. The uncountable case still needs
the normal per-axiom proof review when drafted. This is adjacent planning
material; the current hereditary-size entry makes no model-of-ZFC assertion.

### MARKS-22

**The forcing-filter definition reverses closure and omits internal directedness.**
[Marks, *Set Theory*](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=98),
revision 2026-01-31, Definition 24.5, p. 98, compared with Lemma 24.6 on p. 99
(same PDF pages). Type: invalid definition for the subsequent construction.

The order makes smaller conditions stronger, but the definition closes a filter
under every stronger extension. A subset containing the top empty binary word
would then contain the incompatible words `0` and `1`. The generic construction
on p. 99 instead takes weaker conditions above a descending sequence.
Changing the closure direction alone also leaves pairwise compatibility too
weak: in the poset `c≤a,b≤1`, the upward-closed subset `{1,a,b}` is pairwise
compatible but contains no common stronger condition for `a,b`.

**Repair and corpus disposition:** require a nonempty subset closed toward
weaker conditions and directed toward common stronger conditions **inside the
subset**. The descending-sequence construction satisfies this corrected
definition. This is adjacent forcing-planning material; the forcing theorem
and preservation arguments have not been audited or adopted.

### TRESSL-PRED-01

**Bound-variable renaming omits the new variable's freshness condition.**
[Tressl, *Predicate Logic*](https://personalpages.manchester.ac.uk/staff/Marcus.Tressl/teaching/Goedel/PredicateLogic.pdf),
2018-02-17, Lemma 6.3, p. 56 (PDF p. 57); Definition 1.6.6, p. 17.
Type: missing necessary hypothesis.

The lemma assumes only that substitution is capture-free when asserting
`∀x φ ↔ ∀y φ(x/y)` and its existential analogue. Take distinct variables and
`φ=(x=y)`. Substitution is capture-free, but in a two-element domain the original
universal formula is false and `∀y(y=y)` is true. The new binder captures the
original free occurrence of `y`.

**Repair and corpus disposition:** additionally require `y∉FV(φ)` for a genuine
renaming, along with substitutability. The renamed binder then cannot capture an
old free parameter. Planning only; no current entry adopts this rule. The [normal-form entry](entries/first-order-normal-forms/entry.html#fresh-renaming)
uses Rossegger's correctly qualified rule. The prenex theorem
itself is true; expanding routine mixed-prefix cases is not a separate source bug.

### SCHLICHT-02

**The upward-extension proof uses a theory where an elementary diagram is needed.**
[Schlicht, *Lecture Notes: An Introduction to Model Theory*](https://philippschlicht.github.io/teaching/files/modeltheory2017.pdf),
Bonn 2017 course, PDF dated 2021-07-13, Theorem 1.2.8(2), p. 6;
compare the theory/elementary-diagram definitions and Lemma 1.1.15 on p. 4.
Type: invalid construction step.

The enlarged-language theory uses `Th(M)` and inequalities between new constants.
`Th(M)` contains original-language sentences; it does not require the constants
naming all elements of `M` to realize its elementary diagram. A resulting model
need only be elementarily equivalent to `M`.

For a concrete failed step, use rational orders with original constants `d_n`.
Interpret them as `1−1/(n+2)` in `M` and as `n` in `N`. Every finite increasing
list of named points matches under an order isomorphism, so the structures have
the same theory. `N` can interpret countably many distinct new constants, but it
cannot contain an embedding of `M`: the image of `1` would have to exceed every
natural-number value `d_n` in `N`.

**Repair and corpus disposition:** replace `Th(M)` by `Th(M*)`, the elementary
diagram with names for every element, as in Lemma 1.1.15. Retain infinitude and the
cardinality hypotheses. The upward theorem is valid; this particular construction
fails to ensure its embedding. Planning only; no current consumer. Doets' corrected
scope and Kruckman's diagram argument support the planned extension entries.

### BONEY-02

**The formula for excluding an induced subgraph omits distinctness and nonedges.**
[Boney, *MATH 144: Course Notes*](https://people.math.harvard.edu/~wboney/spring16/144-modeltheory-notes_02_05_2016.pdf),
PDF dated 2016-02-02, Lemma 5.7, pp. 8–9 (same PDF pages).
Type: false characterization.

The proposed universal disjunction negates only the edge requirements of the
finite graph. Even after correcting its indexing, for the three-vertex path it
fails in the two-vertex complete graph: the tuple `(0,1,0)` realizes all required
edges, although there is no three-vertex induced subgraph. A triangle also realizes
the path's edges while failing its nonedge requirement.

**Repair and corpus disposition:** negate the existential assertion that there
is a pairwise distinct tuple realizing the entire adjacency matrix, including
nonedges. That sentence excludes exactly induced copies. Theorem 5.9's later forbidden-subgraph axiomatization also needs this repair. Planning/adjacent material
only; no current graph or definability entry adopts the defective formula. The
selected parameter-definition and automorphism propositions are unaffected.

## Local mathematical slips

These are lower priority: a displayed formula or index is wrong, but a local
correction preserves the underlying argument. They are not missing explanations.

### MAKKAI-01

**Power-set infimum and supremum are interchanged in one display.**
[Makkai, *The Boole/Stone algebra of sets*](https://www.math.mcgill.ca/makkai/SetTheory/SETSEC14.pdf),
§14.1, p. 148, paragraph beginning the power-set comparison. Edition/date not
specified in the extract. The display identifies supremum with intersection and
infimum with union, contradicting the definitions immediately surrounding it.
For the family `{{0},{1}}`, those operations give `{0,1}` and `∅`, respectively.
Swap them: infimum is intersection, supremum is union.
Already correct in [Boolean operations](entries/boolean-algebras/entry.html#boolean-operations).
The subsequent prime-filter and Stone-representation arguments are unaffected.

### MONK-01

**The currying witness evaluates a function outside its domain.**
[Monk, *Lectures on Set Theory*](https://euclid.colorado.edu/~monkd/setth.pdf),
2019-03-11, p. 135, proof of Proposition 12.43(viii).
Type: invalid witness; the exponentiation identity itself is correct.

The proposed map takes `x:μ→(λ→κ)` to a function on `λ×μ`, but assigns
the pair `(α,β)` the value `x(α)(β)` for `α∈λ, β∈μ`. With `λ=2, μ=1`,
evaluation at `(1,0)` requests `x(1)`, outside the outer domain. The proposed
inverse likewise has the factors reversed.

**Repair and corpus disposition:** assign `(α,β)↦x(β)(α)` and define the
inverse by `x(β)(α)=z(α,β)`. The two inverse identities then hold pointwise.
This is adjacent material on a cited page; the entry uses Monk's valid
cardinal-exponentiation reduction and cofinal coding, not this witness.
The corpus's [power laws](entries/infinite-cardinal-arithmetic/entry.html#power-laws)
use the correct correspondence.

### HALBEISEN-02

**The pseudointersection proof removes one too few initial choices.**
[Halbeisen](https://user.math.uzh.ch/halbeisen/publications/pdf/cst.pdf#page=207),
2011-11-17, Theorem 8.1, p. 191 (PDF p. 207). The `n`th chosen point is
only required to meet the sets with indices below `n`, but the containment
claim removes only earlier points. With `X₀=ω, X₁=ω\{1}`, the allowed
choice `a₁=1` survives that removal. Remove the first `n+1` points instead;
the constructed set itself remains a pseudointersection.
Already handled in [countable pseudointersection](entries/finite-errors-and-countable-diagonalization/entry.html#countable-pseudointersection).

### PHILIP-05

**The well-ordering justification shadows its fixed sentinel with its history argument.**
[Philip](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf#page=117),
revision 2025-12-30, Proposition 7.4, p. 117. The fallback of `H(x)` then
literally returns the input history instead of the external marker, contradicting
its advertised range. Use distinct names for the fixed marker and the argument.
Equation (7.1) already gives the intended recursion correctly; the corpus's
[Choice-to-well-ordering proof](entries/axiom-of-choice/entry.html#choice-implies-well-ordering)
also keeps the names distinct.

### BUTTON-08

**The rank proof's final subscript contradicts its starting hypothesis.**
[Button / Open Logic](https://st.openlogicproject.org/settheory-screen.pdf#page=171),
July 2026 revision, Proposition 11.17, p. 158 (PDF p. 171).
After starting with `x∈V_α`, the proof says induction gives `x∉V_α`.
For `x=∅, α=1` this is false. The intended statement is
`x∉V_{rank(x)}`; that rules out `rank(x)=α` and gives the true theorem.
Already correct in [rank and stages](entries/cumulative-hierarchy/entry.html#rank-characterizes-stages).

### COUSOT-01

**Several local relation symbols disagree with the definitions or diagram.**
[Cousot, *Lattice theory — Part I*](https://web.mit.edu/16.399/www/lecture_09-lattice1/Cousot_MIT_2005_Course_09_4-1.pdf),
2005-03-17, slides 8, 14 and 23 (PDF pp. 2, 4 and 6).
The slide-8 incomparability condition also admits `x=y`; add distinctness.
The slide-14 reflexivity line should end `[x]≤[x]`.
The slide-23 diamond's relation list needs `−≤−` in place of `−≤+`,
as its diagram makes those two side points incomparable.
The general constructions remain valid. The corpus's
[orders](entries/ordered-sets/entry.html#partial-and-total-orders),
[quotient order](entries/ordered-sets/entry.html#quotient-order), and
[Hasse diagrams](entries/ordered-sets/entry.html#chains-and-hasse-diagrams) are unaffected.

### MARKS-19

**The derivative hint names the removed set as closed.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=27),
revision 2026-01-31, Exercise 5.19 hint, p. 27. For
`A={0}∪{1/n:n≥1}`, its first derivative is `{0}`, but the removed set
`{1/n:n≥1}` is not closed. The intended closed object is the derivative
`A_α`, not `A\A_α`. The Cantor–Bendixson theorem is not refuted.
This topological exercise is adjacent to the cited normal-function pages and
is not imported by a current entry.

### MARKS-20

**One Goodstein ordinal measure has the wrong constant term.**
[Marks](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf#page=28),
revision 2026-01-31, p. 28. The numeral
`G₄(5)=2·6²+6+5=83` gives measure `ω²·2+ω+5`, rather than the displayed
constant term 4. The sequence's termination argument is unaffected; the
earlier values used in [the corpus's example](entries/normal-functions/entry.html#goodstein-growth-question)
are correct. The enormous terminal index was not recomputed in this audit.

### WEISS-02

**The pair-coloring tree's displayed height is shifted by one.**
[Weiss](https://www.math.toronto.edu/~weiss/Set_Theory.pdf#page=89),
2014-11-21, Theorem 33, p. 89. As untagged graphs, the colorings on 0 and 1
points are the same empty function. Height `r` therefore corresponds to
domain `[r+1]^2`, not `[r]^2`; the printed count `2^{r(r+1)/2}` is correct
with that reindexing. Finite levels and the König argument survive.
The corpus's [length-tagged coloring tree](entries/partition-relations/entry.html#finite-colouring-trees)
keeps length and height equal for every arity. This is an indexing slip, not
a failure of finite Ramsey's theorem.

### CAICEDO-03

**The singular-case coloring has the wrong displayed domain.**
[Caicedo, *580 — Partition calculus (5)*](https://caicedoteaching.wordpress.com/2009/04/21/580-partition-calculus-5/),
2009-04-21, §1, opening of the singular proof of Theorem 1.
It writes `f:[κ]^2→2` with `κ=cf(λ)` and then applies `f` to pairs from `λ`.
Use `[λ]^2` as the domain. This is a local notation slip in adjacent,
non-adopted material; the remaining singular proof was not certified.
The [entry's coloring domain](entries/uncountable-pair-colourings/entry.html#asymmetric-partition-relation)
is correct.

### CAICEDO-04

**The strong-coloring statement has the wrong displayed codomain.**
[Caicedo, *580 — Partition calculus (4)*](https://caicedoteaching.wordpress.com/2009/04/09/580-partition-calculus-4/),
2009-04-09, §1, Theorem 4 statement. A map into `2` cannot have image `ω₁`
on each uncountable set. Replace its codomain by `ω₁`, as used in the
following proof. This is a local notation slip; that stronger theorem's proof
was not audited. The corpus adopts only the different
[Sierpiński two-color theorem](entries/uncountable-pair-colourings/entry.html#sierpinski-colouring).

### MARKER-02

**Adjoining one set to a proper filter is prematurely called an ultrafilter.**
[Marker, Orsay sections 1–3](https://homepages.math.uic.edu/~marker/orsay/orsay1.pdf),
Spring 2010, Lemma 3.4, p. 20 (same PDF page).
Adjoin `A=ω` to the cofinite filter on `ω`. The construction leaves that filter
unchanged; it decides neither the even nor the odd naturals. Replace the
conclusion by **proper filter**, which is what the proof establishes. The
subsequent maximality argument then supplies an ultrafilter. Planning only;
the underlying proper-filter construction remains valid.

### MARKER-03

**The conjunction case in Łoś's proof repeats one conjunct.**
[Marker, Orsay sections 1–3](https://homepages.math.uic.edu/~marker/orsay/orsay1.pdf),
Spring 2010, Theorem 3.11 proof, p. 22 (same PDF page).
The two displayed factor truth sets both use `ψ`, though the induction step
is for `θ∧ψ`. Replace one occurrence by `θ`. The next line and the filter
intersection argument give the intended proof. Planning only; this is a
typesetting slip, not a counterexample to Łoś's theorem.

### ZACH-IC-01

**The decidability proof's displayed test recognizes the complement.**
[Zach / Open Logic, *Incompleteness and Computability*](https://ic.openlogicproject.org/ic-screen.pdf),
cover Fall 2025, remix `6b09d98` (2026-07-11), Text `9620cc7` (2026-07-12),
Theorem 6.13 proof, p. 144 (PDF p. 161).
It names `A=dom(φ_d)` and its complement `dom(φ_e)`, but the displayed test
for membership in `A` uses the computation predicate for `e`. Replace that
index by `d`, and keep the same `d,e` names in the following paragraph instead
of the unexplained switch to `e,f`. For `A=∅`, the displayed `e` test reports
membership everywhere. The simultaneous-search method and the theorem are
correct with the indices aligned. Planning only; repair before using this
proof in `universal-computation`.

### SMITH-01

**The modular-inverse lemma permits modulus one.**
[Smith, *An Introduction to Gödel's Theorems*](https://logicmatters.net/igt/pdfs/GodelBookLM.pdf),
second edition, Logic Matters corrected reprint August 2020, p. 116, footnote 4
(PDF p. 130). The lemma assumes coprime `x,y` and concludes that some `b<y`
gives remainder 1 for `bx` modulo `y`. With `x=y=1`, the only candidate is
`b=0`, whose remainder is 0. Require **modulus greater than one**. In the
following general CRT proof, ignore a modulus-one constraint, whose prescribed
remainder must be zero. The beta construction uses moduli at least two and is
unaffected. Coprime cancellation needed by the proof should be explained locally;
its omission is not a separate false claim. Planning only.

### AVIGAD-CC-01

**The Bézout example has a sign and a bound-variable slip.**
[Avigad, *Classical and constructive logic*](https://www.andrew.cmu.edu/user/avigad/Teaching/classical.pdf),
2000-09-19, revised 2001-11-02, §2, Theorem 2.3 proof, p. 6 (same PDF page).
The residual expansion should be `a(1−qx)−b(qy)`, rather than adding the last
term. The preceding set of integer combinations should bind `v∈Z`, instead
of the stray `y∈Z`. Both repairs preserve the least-positive-combination proof;
the theorem is unaffected. Adjacent planning material read from the PDF's
extracted page text, unused by current entries.

### BONEY-01

**The polynomial-ring example drops the zero constant.**
[Boney, *MATH 144: Course Notes*](https://people.math.harvard.edu/~wboney/spring16/144-modeltheory-notes_02_05_2016.pdf),
PDF dated 2016-02-02, Example 4.2(3), p. 2. Type: local mathematical slip.

The units of a polynomial ring over a field are the nonzero constant polynomials,
so `∃y(xy=1)` defines `F×`, not `F`: zero has no inverse.

**Repair and corpus disposition:** add the case `x=0` to define the embedded field,
or describe the displayed formula as defining its nonzero elements. The surrounding
definability claim survives this local repair. This algebra example is outside the
[definability entry's](entries/definability-and-automorphisms/entry.html#definable-sets) order/natural-number scope and has no current consumer.

## Coverage

Check dates apply to the listed passages, not to an entire publication.
A no-defect outcome applies only to those passages. Source statements and proof
constructions were checked mathematically; this is not a line-by-line audit of entire books or a claim that
all exercise solutions have been verified. Adjacent defects are identified in
their records above. Citation metadata mistakes are corpus issues and do not
count as source errors.

| Publication and inspected version | Checked passages | Cited by current entries | Outcome | Checked on |
| --- | --- | --- | --- | --- |
| [Button / Open Logic, *Set Theory: An Open Introduction*](https://st.openlogicproject.org/settheory-screen.pdf). Fall 2021; revision `2138a50` (2026-07-11), generated from Open Logic Text `9620cc7` (2026-07-12). Printed p. + 13 = PDF p. | 14–50; 52–65; Problems 5.3–5.4 on 70; 73–88; 95–99; 120–130; 132–136; 142–144; 149–159; Definition 10.29 on 146. Includes the definitions and supplied proofs. | [Axiomatic set theory](entries/axiomatic-set-theory/entry.html); [Comparing sizes](entries/comparing-sizes/entry.html); [Constructing number systems](entries/constructing-number-systems/entry.html); [The cumulative hierarchy](entries/cumulative-hierarchy/entry.html); [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html); [Finite and countable sets](entries/finite-and-countable-sets/entry.html); [Foundation](entries/foundation-and-rank/entry.html); [Natural numbers as sets](entries/natural-numbers-as-sets/entry.html); [Ordered sets](entries/ordered-sets/entry.html); [Sets and maps](entries/sets-and-maps/entry.html); [Well-ordered sets](entries/well-ordered-sets/entry.html) | [BUTTON-01](#button-01), [02](#button-02), [03](#button-03), [05](#button-05), [06](#button-06), [07](#button-07); local [08](#button-08). Definitions 6.7–6.9 omit nontriviality, but no false deduction about the constructed fields was found; this convention qualification is excluded from the error register. | 2026-10-07 |
| [Andrew Marks, *Set Theory*](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf). Updated 2026-01-31; 106-page PDF. Printed p. = PDF p. | 4; 10–13; 15–41; 43–53; 61–65; 68–69; adjacent 14, 42, 54, and the named Mostowski theorem on 32; 73–74, Definition 17.7, Proposition 17.8, Theorem 17.9 and supporting Lemma 17.10. The tree proof is supplemented with explicit coding and normality details; Suslin-line equivalence is not adopted. Statements, definitions, and supplied proofs in these passages. Logic-area planning: §13, 57–58, Łoś/finite-cone compactness; §18, 75–80, membership models, relativization and absoluteness; §19, 82–84, reflection/finite fragments; §20, 86, definability opening; §23, 94–95, well-foundedness from a complete ultrafilter; §24, 97–99, forcing definitions/generic construction; 105, finite-fragment consistency discussion. Selected formula-induction and witness arguments checked; full constructibility and forcing proofs not audited. | [The axiom of choice](entries/axiom-of-choice/entry.html); [Axiomatic set theory](entries/axiomatic-set-theory/entry.html); [Clubs and stationary sets](entries/clubs-and-stationary-sets/entry.html); [Cofinality](entries/cofinality/entry.html); [The continuum function](entries/continuum-function/entry.html); [The cumulative hierarchy](entries/cumulative-hierarchy/entry.html); [Filters and ultrafilters](entries/filters-and-ultrafilters/entry.html); [Foundation](entries/foundation-and-rank/entry.html); [Infinite cardinal arithmetic](entries/infinite-cardinal-arithmetic/entry.html); [Infinite sums and products](entries/infinite-sums-and-products/entry.html); [Infinite trees](entries/infinite-trees/entry.html); [Diamond and Suslin trees](entries/diamond-and-suslin-trees/entry.html); [The Mostowski collapse](entries/mostowski-collapse/entry.html); [Natural numbers as sets](entries/natural-numbers-as-sets/entry.html); [Normal functions](entries/normal-functions/entry.html); [Ordinal arithmetic](entries/ordinal-arithmetic/entry.html); [Ordinal powers](entries/ordinal-powers/entry.html); [Ordinals](entries/ordinals/entry.html); [Pressing down](entries/pressing-down-and-delta-systems/entry.html); [Weaker forms of choice](entries/weaker-forms-of-choice/entry.html); [Well-ordered sets](entries/well-ordered-sets/entry.html) | [MARKS-01](#marks-01)–[18](#marks-18); local [19](#marks-19)–[20](#marks-20). Named results were checked on their actual pages. Citation-location audit on 2026-10-14 reconciled all 21 current entry references with the January 31 revision, checking named passages and printed footers against the 106-page PDF; corrected entry page ranges without extending the mathematical review. The enormous Goodstein terminal index and historical independence attributions were not independently verified. Logic-planning defects [MARKS-21](#marks-21) and [22](#marks-22); these passages are not consumed by current entries. | 2026-10-07; logic planning 2026-10-11; citation locations 2026-10-14 |
| [Peter Philip, *Axiomatic Set Theory*](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf). Title-page revision 2025-12-30 (course originally summer 2024). Printed p. = PDF p. | 33–34; 58–60; 89–92; 100–101; 111–112; 117–121; 137–138; 147–149; 165–168; contextual definitions on 32, 35–36, 99, 116. Planning check: Appendix C, 162–164, Proposition C.2 and its proof, Lemma C.3, and Theorem C.5 implications; the converse was independently checked without Lemma C.4. C.4 is not certified. Logic-area planning: §§2.2–2.3, 15–19, finite membership structures and comprehension/independence examples; selected Extensionality and Empty Set examples checked directly. | [The axiom of choice](entries/axiom-of-choice/entry.html); [The continuum function](entries/continuum-function/entry.html); [The cumulative hierarchy](entries/cumulative-hierarchy/entry.html); [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html); [Normal functions](entries/normal-functions/entry.html); [Weaker forms of choice](entries/weaker-forms-of-choice/entry.html) | [PHILIP-01](#philip-01)–[04](#philip-04); local [05](#philip-05). The cited normal-function, beth, Hartogs, Choice-equivalence, Foundation, and relation-composition arguments are otherwise valid in the checked scope. No new serious defect found in the checked Tarski-converse passages. No new serious defect found in those toy-model examples. | 2026-10-07; planning 2026-10-08; logic planning 2026-10-11 |
| [Richard Hammack, *Book of Proof*](https://richardhammack.github.io/BookOfProof/Main.pdf). Third edition, revision 3.4; copyright 2018, PDF generated 2025-02-05. Printed p. + 12 = PDF p. | 233; 269–287: finite pigeonhole, enumerations, countability, cardinal comparison, Cantor, and the full supplied Cantor–Bernstein proof. | [Comparing sizes](entries/comparing-sizes/entry.html); [Finite and countable sets](entries/finite-and-countable-sets/entry.html) | No serious mathematical defect found. Canonical decimals and repetition-free enumerations are valid conventions, rather than proof errors. | 2026-10-07 |
| [Martin Bays, *B1.2 Set Theory*](https://people.maths.ox.ac.uk/bays/teaching/b1set/B1.2.pdf). HT26 Oxford; PDF generated 2026-03-13. Printed p. = PDF p. | 38–39: initial cardinals and aleph recursion; 42: Definition 9.12 and cardinal arithmetic; 43: Theorem 10.2(ii), with adjacent Definition 10.1 on 42–43. | [Cofinality](entries/cofinality/entry.html); [Finite and countable sets](entries/finite-and-countable-sets/entry.html); [Infinite cardinal arithmetic](entries/infinite-cardinal-arithmetic/entry.html) | [BAYS-01](#bays-01)–[02](#bays-02). The initial-cardinal, aleph, and CH passages are valid under the source’s explicit Choice assumption. | 2026-10-07 |
| [Jonathan Pila, *B1.2 Set Theory*](https://www.maths.ox.ac.uk/system/files/attachments/SetTheoryHT18.pdf). HT2018; PDF metadata 2018-01-03. Printed p. = PDF p. | §14, 36–39: ordinal arithmetic and order interpretations, specifically Lemma 14.9 and Theorem 14.11, and the displayed finite Goodstein illustration. | [Ordinal arithmetic](entries/ordinal-arithmetic/entry.html) | [PILA-01](#pila-01), in the supporting order-sum proof. Lemma 14.9 and Theorem 14.11 are valid. | 2026-10-07 |
| [Ivo Terek, *Equivalence Relations, Quotients, and Examples*](https://math-terek.github.io/texts/quotients.pdf). Undated PDF; generation metadata 2021-07-23. Printed p. = PDF p. | §1, 1–4 through Corollary 1: equivalence classes, partitions, fibers, quotient factorization, and quotient-to-image bijection. §2’s vector-space material is outside this audit. | [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html) | [TEREK-01](#terek-01)–[02](#terek-02). The quotient propositions and their proofs are otherwise valid, including empty carriers. | 2026-10-07 |
| [Romyar Sharifi, *Abstract Algebra — Chapter 1: Set theory*](https://www.math.ucla.edu/~sharifi/notes/algebra-ch01.html). Undated HTML retrieved 2026-10-07. | Example 1.3.16 in full, with the positive-modulus convention from Example 1.2.6(c). The rest of the chapter was not audited. | [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html) | No serious mathematical defect found in the cited class-arithmetic example. | 2026-10-07 |
| [Mariusz Wodzicki, *Notes on Ordered Sets*](https://math.berkeley.edu/~wodzicki/H104/OrderedSets.pdf). 2009-09-22. Printed p. = PDF p. | 1–7, §§1.1–1.2: Definitions 1.1–1.6, Exercises 1–7, identities (1)–(40), order duality, bounds, and closure identities. | [Ordered sets](entries/ordered-sets/entry.html) | No serious mathematical defect found. Empty-set and empty-poset qualifications are correctly handled. | 2026-10-07 |
| [Patrick Cousot, *Lattice theory — Part I*](https://web.mit.edu/16.399/www/lecture_09-lattice1/Cousot_MIT_2005_Course_09_4-1.pdf). MIT 16.399, 2005-03-17. Four slides per PDF page; slide s is on PDF page ⌈s/4⌉. | Slides 6–28, 34–36, 41–42: orders, preorder quotients, restrictions, duality, chains, antichains, extrema, and Hasse diagrams. Later lattice/ACC material is outside this audit. | [Ordered sets](entries/ordered-sets/entry.html) | No serious defect in the main constructions; local symbol slips [COUSOT-01](#cousot-01). | 2026-10-07 |
| [Alfred Tarski, *A lattice-theoretical fixpoint theorem and its applications*](https://people.csail.mit.edu/carroll/probSem/Documents/Tarski.pdf). *Pacific Journal of Mathematics* 5(2), 1955; received 1953-06-29. Printed 285 = PDF 1. | 285–287: definitions and the complete proof of Theorem 1. | [Ordered sets](entries/ordered-sets/entry.html) | No serious mathematical defect found. The invariant interval and the fixed-point lattice’s bounds are justified. | 2026-10-07 |
| [William A. R. Weiss, *An Introduction to Set Theory*](https://www.math.toronto.edu/~weiss/Set_Theory.pdf). 2014-11-21. Both `/weiss/` and `/~weiss/` citations identify this edition; printed p. = PDF p. in the checked ranges. | 63–64: Mostowski Theorems 19–20 and Exercise 14; 79–82: dense linear orders and adjacent almost-disjoint construction; 89: Theorem 33 and Exercise 29. Planning check: 101–102, Theorems 41–42 and Exercise 34 on hereditary cardinality and inaccessible closure; 149, measurable-cardinal definition; 151, Theorem 59 and its complete direct proof that a measurable cardinal is strongly inaccessible. Logic-area planning: chapter 11, 103–110, isomorphism/transitive models/bounded absoluteness; 113–116, relativized Replacement/Hκ; 117–120, reflection. Selected formula inductions and reflection witness closure inspected; not all internal-rank arguments audited. | [Dense linear orders](entries/dense-linear-orders/entry.html); [The Mostowski collapse](entries/mostowski-collapse/entry.html); [Partition relations](entries/partition-relations/entry.html); [Hereditarily small sets](entries/hereditarily-small-sets/entry.html#hereditary-rank-bound) | [WEISS-01](#weiss-01), in the adjacent almost-disjoint construction; local [02](#weiss-02), in the Ramsey tree indexing. The Mostowski and dense-order arguments are valid. No new serious defect found in these planning passages; model-theoretic claims are outside this check. No new serious defect confirmed in the selected logic-planning arguments. | 2026-10-07; planning 2026-10-08; logic planning 2026-10-11 |
| [Michael Makkai, *Set Theory*, §§13–14 extracts](https://www.math.mcgill.ca/makkai/SetTheory/SETSEC14.pdf). Undated lecture-note extracts. §13: printed 133 = PDF 1; §14: Printed 146 = PDF 1. | 146–161, §§14.1–14.3: all sixteen pages of the extract, including Boolean operations, ideals/filters, prime filters, and Stone representation. Planning check: [§13, Inaccessible cardinals](https://www.math.mcgill.ca/makkai/SetTheory/SETSEC13.pdf), 133–137, Lemma (2), Corollary (7), and Proposition (8)(v), including the small-domain rank-bound argument. The MK model equivalence and later converse were not audited. | [Boolean algebras](entries/boolean-algebras/entry.html) | No serious defect in the prime-filter or representation arguments; local power-set display [MAKKAI-01](#makkai-01). [MAKKAI-02](#makkai-02) affects the supporting union proof; its conclusion has a checked finite-case repair. The inaccessible rank-closure argument remains valid. | 2026-10-07; planning 2026-10-08 |
| [Moshe Kamensky, *Set Theory*](https://mkamensky.github.io/teaching/2012f/set-theory/notes.pdf). Course URL `2012f`; embedded revision dated 2011-12-07. Printed p. = PDF p. | 4 and 6, §1.3: Definitions 1.3.1–1.3.2, Example 1.3.4, and Theorem 1.3.9 with its supporting finite-change construction. | [Infinite trees](entries/infinite-trees/entry.html) | [KAMENSKY-01](#kamensky-01). The finite-collision repair instruction itself is valid compression. | 2026-10-07 |
| [Thomas Jech, *Set Theory: The Third Millennium Edition, revised and expanded*](https://fa.ewi.tudelft.nl/~hart/37/onderwijs/set_theory/Jech/05-AC_and_cardinal_arithmetic.pdf). 2003 edition in corpus metadata, three chapter extracts; Chapter 9 omits an imprint. Chapter 5: printed 47 = PDF 1; Chapter 7: printed 73 = PDF 1; Chapter 9: printed 107 = PDF 1. | [Chapter 5](https://fa.ewi.tudelft.nl/~hart/37/onderwijs/set_theory/Jech/05-AC_and_cardinal_arithmetic.pdf), 57: Lemma 5.19 and Theorem 5.20. [Chapter 7](https://fa.ewi.tudelft.nl/~hart/set_theory/Jech/07-filters_ultrafilters_and_Boolean_algebras.pdf), 75–76: Theorem 7.6 and Lemma 7.7, independent families and the ultrafilter count. Planning check: [Chapter 9](https://fa.ewi.tudelft.nl/~hart/set_theory/Jech/09-combinatorial_set_theory.pdf), 111–113, Theorem 9.6 pair-pattern argument and Theorem 9.7 regular/singular Dushnik–Miller proofs. Higher-arity induction and later results were not audited. | [The continuum function](entries/continuum-function/entry.html); [Independent families](entries/independent-families/entry.html) | No serious mathematical defect found. Cardinal-exponentiation reduction, cofinal coding, and finite-trace construction are valid under the stated assumptions. The pair argument and singular-cardinal thinning were checked; ordered blocks or symmetric neighbor sets must be explicit in an adaptation. | 2026-10-07; planning 2026-10-08 |
| [J. Donald Monk, *Lectures on Set Theory*](https://euclid.colorado.edu/~monkd/setth.pdf). 2019-03-11. Printed p. + 5 = PDF p. | 135–136 and 139–140: Proposition 12.43’s power identities, Theorem 12.46, Lemma 12.56, and Theorems 12.57–12.58. Theorem 12.46 is on 136 despite the corpus’s narrower page label. | [The continuum function](entries/continuum-function/entry.html) | No serious defect in the cited cofinal coding or cardinal reduction; local reversed arguments in an adjacent currying witness [MONK-01](#monk-01). | 2026-10-07 |
| [Lorenz J. Halbeisen, *Combinatorial Set Theory: with a gentle introduction to forcing*](https://user.math.uzh.ch/halbeisen/publications/pdf/cst.pdf). Author-hosted 492-page PDF dated 2011-11-17. Printed p. + 16 = PDF p. | 190–192, Chapter 8: almost containment, pseudointersections, Theorems 8.1 and 8.3, bounding/dominating definitions, and Fact 8.2. Planning check: 192–194, Theorems 8.4–8.5 and the splitting/reaping definitions and proofs. | [Bounding and dominating families](entries/bounding-and-dominating-families/entry.html); [Finite errors and countable diagonalization](entries/finite-errors-and-countable-diagonalization/entry.html) | [HALBEISEN-01](#halbeisen-01), strict domination witness; local [02](#halbeisen-02), pseudointersection containment index. No new serious defect found in the checked splitting/reaping arguments. | 2026-10-07; planning 2026-10-08 |
| [Spencer Unger, *Forcing Summer School Lecture Notes*](https://math.huji.ac.il/~sunger/ucla/LogicSummerSchool/ForcingNotes.pdf). UCLA Logic Summer School, 2013-07-15. Printed p. = PDF p. | 5–6, all of §2 through Theorem 2.8; 1–4 checked for contextual conventions. | [Almost disjoint families](entries/almost-disjoint-families/entry.html); [Finite errors and countable diagonalization](entries/finite-errors-and-countable-diagonalization/entry.html) | [UNGER-01](#unger-01)–[02](#unger-02). The countable strict bound and continuum-sized almost-disjoint construction are valid. | 2026-10-07 |
| [James Cummings, *21602 Set theory: Homework One solutions*](https://www.math.cmu.edu/~jcumming/teaching/sets_2006/hw1sol.pdf). Undated one-page PDF in the `sets_2006` course directory. | 1, solutions 2–3: countable eventual domination and prefix-based almost-disjoint construction. | [Almost disjoint families](entries/almost-disjoint-families/entry.html); [Finite errors and countable diagonalization](entries/finite-errors-and-countable-diagonalization/entry.html) | No serious mathematical defect found. The added 1 supplies strict domination, and length-tagged prefixes separate the branches. | 2026-10-07 |
| [Corey Bacal Switzer, *Lecture Notes on Iterated Forcing*](https://coreyswitzer.wordpress.com/wp-content/uploads/2021/12/complete-lecture-notes.pdf). Vienna winter term 2021; December 2021 host path, 44-page PDF. Printed p. = PDF p. | 18, §4.2: definitions, Definition 4.17, and Lemma 4.18; the earlier bounding definition on 1 checked for comparison. | [Bounding and dominating families](entries/bounding-and-dominating-families/entry.html) | [SWITZER-01](#switzer-01)–[02](#switzer-02). The displayed cofinality-cover argument for the dominating number is valid. | 2026-10-07 |
| [Andrés E. Caicedo, *580 — III. Partition calculus*](https://andrescaicedo.wordpress.com/2009/03/21/580-iii-partition-calculus/). HTML published 2009-03-21, retrieved 2026-10-07. | §1, Definition 1; §2, infinite Ramsey Theorem 3 with proof; adjacent finite Ramsey Theorem 4 with proof. | [Partition relations](entries/partition-relations/entry.html) | [CAICEDO-01](#caicedo-01), failed finite-bound recurrence. The infinite nested-tail proof is valid. Exact-image and vacuous-homogeneity conventions are distinguished in the proposed repair. | 2026-10-07 |
| [Stanley Burris and H. P. Sankappanavar, *A Course in Universal Algebra*](https://www.math.uwaterloo.ca/~snburris/htdocs/UALG/univ-algebra2012.pdf). Millennium edition, 2012 updated PDF. Printed p. + 14 = PDF p. | 127–130, Chapter IV §3: Definition 3.1, Theorem 3.5, Definition 3.6, and supporting ideal/filter and quotient-ring context. | [Subsets modulo small sets](entries/subsets-modulo-small-sets/entry.html) | No serious mathematical defect found in the cited ideal-congruence correspondence. Translating Boolean-ring operations into set operations is an exposition choice. | 2026-10-07 |
| [Andreas Blass, *Combinatorial Cardinal Characteristics of the Continuum*](https://sites.lsa.umich.edu/ablass/wp-content/uploads/sites/1471/2025/10/hbk.pdf). Author draft dated 2003-11-24, 104-page PDF; printed p. = PDF p. The 2025 hosting path is not the revision date. | 37, Definition 6.16 and Remark 6.17; 39–40, Definitions 6.22 and Proposition 6.23; 51–52, Proposition 8.1, Definition 8.3 and Proposition 8.4; 56–58, Definition 9.1 and Definition 9.6. Definitions, finite-change reduction and the bounding comparison checked; forcing assertions are outside this review. Planning check: Theorem 2.6, Definition 2.9/Theorem 2.10; Definition 3.1/Theorem 3.3 and Definition 3.6/Theorem 3.8; Definition 6.2/Proposition 6.4, direct thinning in Proposition 6.8/Theorem 6.9, Theorem 6.14/Corollary 6.15, Proposition 6.24/Theorem 6.25; Definition 8.11/Proposition 8.12/Theorem 8.13. This covers elementary scales, interval partitions, splitting/reaping, towers, and maximal independence; forcing proofs remain outside the check. Abstract motivation only: Introduction, 2–4, read on 2026-10-10 for the question of where countable conclusions first fail; this adds no proof audit. | [Small families of subsets](entries/small-families-of-subsets/entry.html); [Splitting and reaping](entries/splitting-and-reaping/entry.html#cardinal-comparisons) | No serious defect in the adopted passages. In 8.4 the omitted partition adjustment is valid: remove finitely many overlaps from each selected set, then distribute residual points finitely among them. The entry uses a direct selection proof. The free-filter convention in 9.1 must be retained in 9.6. No new serious defect found in these elementary passages. The 2003 discussion of whether p<t is historical: p=t is now known, as recorded in the Malliaris–Shelah planning row. | 2026-10-07; planning 2026-10-08; abstract motivation 2026-10-10 |
| [Andrés E. Caicedo, *580 — Cardinal arithmetic (5)*](https://caicedoteaching.wordpress.com/2009/02/13/580-cardinal-arithmetic-5/). HTML published 2009-02-13. | Definition 12, the three Ulam-matrix identities, and Theorem 13 with its preceding proof. | [Splitting stationary sets](entries/splitting-stationary-sets/entry.html) | No serious defect in the adopted successor-cardinal argument with infinite kappa. Disjoint stationary subsets become a partition by assigning the remainder to one cell. The finite-cardinal phrasing and later Silver material are not adopted. | 2026-10-07 |
| [Andrés E. Caicedo, *580 — Partition calculus (4)*](https://caicedoteaching.wordpress.com/2009/04/09/580-partition-calculus-4/). HTML published 2009-04-09. | Theorem 2 and Lemma 3, Sierpiński's two-colour construction; adjacent Theorem 4 statement only. | [Uncountable pair colourings](entries/uncountable-pair-colourings/entry.html) | No serious defect found in the adopted well-order/linear-order construction. For omega1 the entry supplies a direct rational-separation proof rather than the generalized lexicographic lemma. Local [CAICEDO-04](#caicedo-04), wrong codomain in the adjacent Theorem 4 statement. Its proof and later strong colourings are outside this check. | 2026-10-07 |
| [Andrés E. Caicedo, *580 — Partition calculus (5)*](https://caicedoteaching.wordpress.com/2009/04/21/580-partition-calculus-5/). HTML published 2009-04-21. | Theorem 1, its regular-cardinal statement, and the large-neighborhood recursion in its proof; adjacent singular-proof opening and negation step only. | [Uncountable pair colourings](entries/uncountable-pair-colourings/entry.html) | No serious defect in the adopted dichotomy. The regular case is proved directly using small unions. Adjacent [CAICEDO-02](#caicedo-02), false cofinality bound, and local [03](#caicedo-03), domain slip. The remaining singular argument, stronger topological theorem and Jónsson material are not adopted or certified. | 2026-10-07 |
| [Justin Tatch Moore, *MATH 6870: Set Theory*](https://pi.math.cornell.edu/~justin/Limited2Cornell/lecture_notes.pdf). Undated author-hosted 105-page PDF retrieved 2026-10-07; printed p. + 2 = PDF p. | 47–48, section 19: diamond's definition and Theorem 19.3, including the countable-branch extension and antichain closure argument. | [Diamond and Suslin trees](entries/diamond-and-suslin-trees/entry.html) | No serious defect in the adopted construction. The entry spells out coding/height alignment and sufficient closure bounds. Proposition 19.1 and the constructibility proof 19.2 are not adopted or certified. | 2026-10-07 |
| [Andrés E. Caicedo, *580 — Cardinal arithmetic (4)*](https://caicedoteaching.wordpress.com/2009/02/11/580-cardinal-arithmetic-4/). HTML published 2009-02-11; supporting publication cited by *Cardinal arithmetic (5)*. | Theorem 7 and its club-intersection proof only. | Supporting source for [Splitting stationary sets](entries/splitting-stationary-sets/entry.html#ulam-splitting); not an additional `based_on` citation. | No serious defect in the checked intersection argument. The empty-family case is valid routine compression. Other passages were not audited. | 2026-10-07 |
| [Andreas Lietz, *Set Theory — Lecture Notes*](https://andreas-lietz.github.io/resources/PDFs/Lecture_Notes.pdf). Version 2025-02-27, originating March 2024; 110 pages, printed p. = PDF p. | Planning: §5.3, 43–45, Definitions 5.12/5.15, Proposition 5.13, Theorem 5.14, Lemma 5.16 and Claims 5.17–5.18; Solovay splitting and trace arguments checked. §1, 5–7, Definitions 1.7/1.9 through Lemma 1.12 inspected; Lemma 1.10's deferred proof was not audited. | Planning only; no current consuming entry. | No serious defect found in the checked splitting proof. [LIETZ-01](#lietz-01) invalidates the unique-real-representation step in Lemma 1.12. | 2026-10-07–08 |
| [Assaf Rinot, *Dushnik-Miller for singular cardinals (part 1)*](https://blog.assafrinot.com/?p=603). HTML post dated 2012-01-20, retrieved 2026-10-08. | Planning: main theorem, subclaim, ordered blocks, regular homogeneous sets, uniform-bound thinning, size-growth recursion, and cross-block proof. The final optimality observation was not audited. | Planning only; no current consuming entry. | No serious defect confirmed. Continuing to use Y_i after obtaining its full-size bounded-neighbor subfamily is valid implicit thinning/renaming; an adaptation should state it. | 2026-10-07–08 |
| [Andrés E. Caicedo, *580 — Partition calculus (6)*](https://caicedoteaching.wordpress.com/wp-content/uploads/2009/04/580-partition6.pdf). Undated five-page extract hosted under 2009/04. | Planning: Theorems 1/3 statements and Theorem 5's final end-homogeneous/tree mechanism, 3–5. Elementary-submodel proofs and full choiceless cardinal bookkeeping were not independently verified; Theorem 3's proof is not supplied here. | Planning only; no current consuming entry. | Supporting scope inspection; no complete proof audit or no-defect certification. The Jech pair argument is the preferred proof source. | 2026-10-07–08 |
| [Takayuki Kihara, Alberto Marcone and Arno Pauly, *Searching for an analogue of ATR₀ in the Weihrauch lattice*](https://arxiv.org/pdf/1812.01549v2). arXiv:1812.01549v2, 2020-01-13; 35 pages. | Planning: 2, Perfect Tree Theorem statement; §6, 18, perfect-tree definition, restatement, Definition 6.2 and Proposition 6.3 inspected to distinguish an invocation from a classical proof. | [Perfect subtrees](entries/perfect-subtrees/entry.html#branch-cardinality). | Statement/definition coverage only. Classical perfect-tree proof and Weihrauch reductions were not audited. An alternative author-hosted PDF was inaccessible. | 2026-10-07–08 |
| [Yiannis N. Moschovakis, *Descriptive Set Theory*](https://www.math.ucla.edu/~ynm/lectures/dst2009/dst2009.pdf). Second-edition author manuscript dated 2009-04-08; 516 pages; printed p. + 13 = PDF p. | Planning: 50–51, Theorem 2A.1 and Corollary 2A.2, condensation-point/countable-neighborhood proof checked. §2C, 57–61, tree/body definitions and binary recursion inspected for the tree-only adaptation. | [Perfect subtrees](entries/perfect-subtrees/entry.html#perfect-kernel). | No serious defect found in the checked elementary argument. The full generalized κ-Suslin proof, prior Polish-space cardinality theorem, and derivative exercise were not independently audited. | 2026-10-07–08 |
| [Peter J. Cameron, *Hall's marriage theorem*](https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/33424/Cameron_2026_JLMS_Halls-marriage-theorem_CC.pdf?isAllowed=y&sequence=1). Journal of the London Mathematical Society (2), 2026, 113:e70378; DOI 10.1112/jlms.70378; nine pages. | Planning: 2, Theorem 1.1 statement and sketch structure; 7, Theorem 8.1 statement and preceding infinite-member counterexample. | [Finite constraints and distinct representatives](entries/finite-constraints-and-distinct-representatives/entry.html#infinite-hall). | Formulations and counterexample checked. The finite sketch omits its auxiliary lemma, and §8 supplies no proof of infinite Hall; complete proofs must be supplied separately. Other sections were not audited. | 2026-10-07–08 |
| [Kenneth K. Hickin and J. M. Plotkin, *A patching lemma*](https://doi.org/10.1305/ndjfl/1093887438). Notre Dame Journal of Formal Logic 17(1), January 1976, 158–160; received 1974-03-02. | Planning: 158, patching statement, ultrafilter proof and n=1 Rado specialization, checked from complete page text exposed by search for the [scanned PDF](https://scispace.com/pdf/a-patching-lemma-4do9ffsepy.pdf). | [Finite constraints and distinct representatives](entries/finite-constraints-and-distinct-representatives/entry.html#rado-selection). | No serious defect found in the exposed page's finite-partition argument. Full PDF fetches failed; 159–160 were not inspected. This is not a whole-paper review. | 2026-10-07–08 |
| [Andrej Bauer and Peter LeFanu Lumsdaine, *On the Bourbaki-Witt Principle in Toposes*](https://math.andrej.com/wp-content/uploads/2012/01/bw.pdf). Author manuscript dated 2012-01-04; 19 pages. | Planning: 1, classical iteration description; 2–3, chain-completeness and progressive/monotone definitions; 4, Theorem 3.1 Knaster–Tarski proof checked. | Planning only; no current consuming entry. | No serious defect found in the checked fixed-point argument. Introductory iteration is not a complete stabilization proof; constructive comparisons and topos results were not audited. | 2026-10-07–08 |
| [Maryanthe Malliaris and Saharon Shelah, *Cofinality spectrum theorems in model theory, set theory, and general topology*](https://shelah.logic.at/papers/998/). Author publication record Sh:998 for Journal of the American Mathematical Society 29(1), 2016, 237–297. | Planning: publication metadata and abstract's p=t result checked against older tower discussions. | Planning only; no current consuming entry. | Result statement confirmed; the model-theoretic proof was not audited and is outside the proposed elementary tower entry. | 2026-10-08 |
| [Richard Zach / Open Logic Project, *Sets, Logic, Computation*](https://slc.openlogicproject.org/archives/f25/slc-screen.pdf). Archived Fall 2025, remix `38828e6`, Text `0c1e9e3`, both 2025-07-01; 437 pages. Printed p. + 21 = PDF p. | Logic planning: countable-language convention §6.2, 89–90; substitution §6.9, 108–110; semantic substitution §7.6, 128–130; rules §§11.1–11.4, 194–200; soundness §11.11, 216–221; completeness §§12.2–12.9, 230–249, including equality quotient; §12.11, 251–252, Löwenheim–Skolem discussion. Opening-entry check: §§6.2–6.3, 89–95, language, formula constructors and structural induction; §§6.8–6.9, 107–110, free variables and capture-safe substitution; §§7.2, 7.4–7.6, 114–116, 117–130, structures, assignments, satisfaction, agreement and substitution; §7.7 opening definitions, 130; §§11.1–11.4, 11.7, 11.11, 194–200, 209–211, 216–221, all propositional deduction rules, finite derivations, weakening and soundness. Adjacent 95–99 read for context; string parsing is not adopted. Batch checks: §§11.1–11.13, 194–223, sentence natural deduction with quantifier/equality side conditions, finite proof operations and all soundness cases; §§12.2–12.8, 230–246, conservative auxiliary-constant expansion, witness/Lindenbaum extensions, equality quotient, strengthened scoped truth induction and countable completeness; §12.9, 246–249, compactness, unnamed elements and size requirements. These adopted arguments and routine exercise cases were checked on 2026-10-12. | [Propositional logic](entries/propositional-logic/entry.html#formulas); [Propositional proofs](entries/propositional-proofs/entry.html#deduction-rules); [First-order languages](entries/first-order-languages/entry.html#scoped-formulas); [First-order structures](entries/first-order-structures/entry.html#satisfaction). [First-order proofs](entries/first-order-proofs/entry.html#fresh-parameters); [Henkin completeness](entries/henkin-completeness/entry.html#truth-lemma); [Logical compactness](entries/logical-compactness/entry.html#compactness). | No serious defect found in these selected arguments. Routine exercise cases and previous-lemma dependencies are expanded for the adopted entry scopes; this is not a whole-book audit. Opening entries supply the compressed induction and exercise cases explicitly and use disjoint free/bound-variable slots to avoid capture. No defect found in these adopted passages. No serious defect found in the batch passages. The new entries explicitly supply finite-empty-case bounds and omitted connective, quantifier and finite-support details; these are valid source compressions, not registered defects. | 2026-10-11; opening-entry checks 2026-10-11; batch checks 2026-10-12 |
| [Magnus, Button, Trueman and Zach, *forall x: Calgary*](https://forallx.openlogicproject.org/forallxyyc.pdf). Cover Fall 2025; served revision `c5cb415`, 2026-09-27; 437 pages. Printed p. + 10 = PDF p. | Logic planning: validity 2–10; truth tables 80–82; natural-deduction introduction 113–114; soundness chapter 48, 390–397. Opening propositional-entry check: §§6.1–6.3, 49–55; chapters 9–10, 69–73; §§11.1–11.3 and adjacent exercises, 77–84; §§12.1–12.6 and adjacent exercises, 85–92. Used portions are 49–54, 69–71, 77–81, 85–90 and 92. Further planning 2026-10-12: chapters 45–46, 369–380, actual normal-form and positive functional-completeness arguments; NAND/NOR constructions on 378–379. The exclusive binary-connective classification is stated without proof. | [Propositional logic](entries/propositional-logic/entry.html#formulas); [Propositional normal forms](entries/propositional-normal-forms/entry.html#normal-form-theorem) and [complete connective bases](entries/propositional-normal-forms/entry.html#complete-connectives). | No serious defect found in this limited scope. Several source soundness rule cases are exercises; the corpus supplies its fixed calculus's full proof. No defect found in the adopted passages; locality, simultaneous substitution, and the finite-row test are proved explicitly. Positive normal-form arguments are usable; atomless formulas and constants need adaptation. In particular implication with the corpus falsity constant expresses negation, so the source's implication-only failure example cannot be transferred unchanged. | 2026-10-11; opening-entry checks 2026-10-11; further planning 2026-10-12 |
| [Kees Doets, *Basic Model Theory*](https://web.stanford.edu/group/cslipublications/cslipublications/Online/doets-basic-model-theory.pdf). CSLI / FoLLI, 1996; 141 pages. Printed p. + 8 = PDF p. | Logic planning: §2.2, 13–17, Tarski–Vaught, witness closure, downward Löwenheim–Skolem and elementary chains; §3.44, 44, Łoś–Vaught statement; §3.4, 44–45, countable back-and-forth; appendix A.1, 94–95, A.2, 100, A.3.2, 103–106, Henkin construction. Batch checks 2026-10-12: §2.2, 13–16, Tarski–Vaught and selected-witness closure/counting, with 17 read for boundary context; Appendix A.3.2, 103–106, finite constant-replacement and equality-quotient cross-check. The corpus uses its fixed sentence/fresh-constant calculus rather than silently importing Doets' free-variable rules. Further planning 2026-10-12: Definition 2.16/Lemma 2.17, 17, elementary-chain induction; §4.2, 55–58, diagrams, Theorem 4.10 upward Löwenheim–Skolem and universal-preservation argument. Diagram Lemma 4.8 is an exercise, and routine preservation/union details need expansion. | [Elementary submodels](entries/elementary-submodels/entry.html#tarski-vaught); [Henkin completeness](entries/henkin-completeness/entry.html#fresh-constants). | [DOETS-01](#doets-01) affects the adjacent Łoś–Vaught statement. Selected witness-closure and Henkin constructions inspected; no whole-book certification. Extracted fonts are damaged, so original notation needs checking when adopted. No new serious defect found in the adopted batch passages; finite tuple counts and function/constant closure from witness formulas are expanded explicitly. No new serious defect in the newly checked chain/diagram/upward passages; the infinite-model hypothesis and signed diagram are explicit. | 2026-10-11; batch checks 2026-10-12; further planning 2026-10-12 |
| [Jeremy Avigad, *Logic and Computation*](https://www.andrew.cmu.edu/user/avigad/Teaching/landc_notes.pdf). January 2002 lecture notes; 120 pages. Printed p. + 6 = PDF p. | Logic planning: contents/chapter boundaries; §4.9 finite propositional completeness strategy; §7.4, 90–93, diagrams and Löwenheim–Skolem; §7.6, 96, preservation argument. §8.3, 101–106, second-order material located, not fully proof-audited. Opening proof-entry check: §4.9, 50–51, row-simulation strategy; adjacent §4.2, 38–39, derivation presentation. Further planning 2026-10-12: §3.8, 36, normal-form discussion; §4.6, 46, compactness from strong completeness; §5.4, 61, prenex recipe; §7.3, 89–90, parameter-free order-automorphism examples and the rigid natural successor structure. These notes refer to van Dalen for the full normal-form/prenex proof. | [Propositional proofs](entries/propositional-proofs/entry.html#signed-valuations); [positive-ray nondefinability](entries/definability-and-automorphisms/entry.html#positive-ray); [rigid natural structure](entries/definability-and-automorphisms/entry.html#rigid-structure). | [AVIGAD-LC-01](#avigad-lc-01), [02](#avigad-lc-02). Propositional signed-valuation cases are not all supplied. The notes are a different publication from the 2022 book. The entry supplies every signed-valuation connective case and finite case-elimination, including empty support. No serious defect found in the adopted propositional scope. The basic automorphism examples are usable with their language/parameter scope; later nonstandard strip arguments are outside this pass. | 2026-10-11; opening-entry checks 2026-10-11; further planning 2026-10-12 |
| [Philipp Schlicht, *Lecture Notes: Introduction to Mathematical Logic*](https://philippschlicht.github.io/teaching/files/mathematicallogic2021.pdf). Bonn summer 2021, PDF dated 2022-02-01. Printed p. = PDF p. | Logic planning: front matter, §5.1 definitions 5.1.1–5.1.5 and complete proof of Lemma 5.1.6, 65–66, direct dense-order quantifier elimination. | Planning only; no current consuming entry. | [SCHLICHT-01](#schlicht-01). Corrected elimination retains parameter conditions and lower/upper comparisons. Other model-theory and algebra chapters were not audited. | 2026-10-11 |
| [Marcus Tressl, *Introduction to Model Theory*](https://personalpages.manchester.ac.uk/staff/marcus.tressl/papers/ModelTheory.pdf). Author PDF dated 2026-10-03. | Logic planning: front matter/contents; Tarski–Vaught and downward Löwenheim–Skolem §§2.3.1–2.3.2, 27–28; later dense-order/quantifier-elimination locations. | Planning only; no current consuming entry. | Supplementary scope inspection; no full chapter audit or no-defect certification of later arguments. | 2026-10-11 |
| [David Marker, *Model Theory for Algebra and Algebraic Geometry*, Orsay sections 1–3](https://homepages.math.uic.edu/~marker/orsay/orsay1.pdf). Spring 2010, 25 pages. Printed p. = PDF p. | Logic planning: §1, 1–7, syntax/structures/satisfaction/isomorphism; §3, 20–24, generated filters, quotient operations, Łoś, compactness, and diagonal ultrapower embedding; adjacent 19–20 maximality. Opening semantics-entry check: Definition 1.3, 2, isomorphisms; Theorem 1.10, 6–7, term transport and formula invariance, including both quantifier directions; theories paragraph, 7. | [First-order structures](entries/first-order-structures/entry.html#isomorphism-invariance). | [MARKER-01](#marker-01); local [02](#marker-02), [03](#marker-03). Selected quotient and Łoś induction usable with corrections and explicit witness choice. Algebraic applications were not audited. No defect found in this adopted scope; the existing findings concern later material unused here. | 2026-10-11; opening-entry checks 2026-10-11 |
| [William Weiss and Cherie D'Mello, *Fundamentals of Model Theory*](https://www.math.toronto.edu/weiss/model_theory.pdf). ©2015, 64 pages. Printed p. + 2 = PDF p. | Logic planning: introduction 1; elementary-chain proof 16–18; Lemma 5, 19, Tarski–Vaught; Theorem 5, 20, downward Löwenheim–Skolem with a prescribed subset. Batch check 2026-10-12: printed 19–20, Lemma 5 and Theorem 5, both witness-criterion directions and the prescribed-subset downward size bound; used as an independent cross-check. Further planning 2026-10-12: 16–18, Definitions 21–22/Theorem 4, full omega-chain union proof and the isomorphic-tail counterexample; 24–25, diagrams definitions and Theorem 9 sketch/exercise. | [Elementary submodels](entries/elementary-submodels/entry.html#tarski-vaught); [Downward size bound](entries/elementary-submodels/entry.html#downward-size-bound). | No serious defect found in these selected witness-closure and induction arguments. Later chapters were not audited. No serious defect found in these adopted passages; nonempty seeds, metatheoretic witness choice, and finite-tuple/cardinal counting are explicit in the corpus. No serious defect found in the chain argument; the diagram proof is not supplied in full. | 2026-10-11; batch checks 2026-10-12; further planning 2026-10-12 |
| [David Marker, *Model Theory II: Quantifier Elimination*](https://homepages.math.uic.edu/~marker/MSRI-2.pdf). MSRI slides dated 2020-10-14. | Logic planning: slides 1–13, introductory quantifier-elimination statements and algebraic orientation. | Planning only; no current consuming entry. | Orientation/statement inspection only; not a completed proof audit or a prerequisite for the opening logic batches. | 2026-10-11 |
| [Arnold W. Miller, *Introduction to Mathematical Logic: A Problem Solving Course*](https://people.math.wisc.edu/~miller/old/m771-98/logintro.pdf). Title Fall 1995; 75 pages; the hosting folder is not the edition date. | Logic planning: front matter and propositional material 4–5; syntax/models 25–28; Tarski–Vaught/witness-closure Löwenheim–Skolem 40–43; later coding/Tarski/incompleteness statements 68–70. | Planning only; no current consuming entry. | Selected definitions and witness-closure arguments inspected. Later statements and exercises are dependency pointers, not certified proofs. This is a problem-solving text, not the selected detailed proof spine. | 2026-10-11 |
| [Arnold W. Miller, model-theory homework collection](https://people.math.wisc.edu/~awmille1/old/m776-09/home.pdf). Spring 2009, dated 2009-05-07. | Logic planning: opening theorem/problem statements only. | Planning only; no current consuming entry. | Statement inspection only; no solution/proof audit. | 2026-10-11 |
| [David W. Kueker, *Notes on Mathematical Logic*](https://math.umd.edu/~dkueker/712.pdf). Undated author PDF, retrieved 2026-10-11. | Logic planning: selected Henkin-model discussion 49–51; elementary substructures/back-and-forth §§4.2–4.3, 66–71. | Planning only; no current consuming entry. | Alternative-source scope inspection; not a whole-chapter proof certification. No edition date inferred. | 2026-10-11 |
| [Avigad, Hua, Lewis and van Doorn, *Logic and Proof*](https://leanprover-community.github.io/logic_and_proof/semantics_of_propositional_logic.html). HTML labelled version 3.18.4, ©2017, retrieved 2026-10-11. | Logic planning: §§6.1–6.3, valuations, truth tables and the finite completeness strategy. | Planning only; no current consuming entry. | Explanatory reading only. The text expressly does not give a fully rigorous metalogical completeness treatment; no full proof certification. | 2026-10-11 |
| [Jeremy Avigad, *Computability and Incompleteness*](https://www.andrew.cmu.edu/user/avigad/Teaching/candi_notes.pdf). Version 2007-01-09; 128 pages. Printed p. + 4 = PDF p. | Logic planning: §§2.1–2.4, machine examples, primitive recursion and coding; §2.7, universal/halting argument; §§4.3–4.5, Q representation, undecidability and diagonal lemma; §4.7, conditional second incompleteness. Model equivalence §2.6 and c.e./Rice chapters located but not fully audited. | Planning only; no current consuming entry. | [AVIGAD-CI-01](#avigad-ci-01), [02](#avigad-ci-02). Concrete derivability conditions are accepted rather than fully proved in the inspected argument; this is an explicit coverage limit. CRT is invoked without its proof. | 2026-10-11 |
| [Peter Smith, *An Introduction to Gödel's Theorems*](https://logicmatters.net/igt/pdfs/GodelBookLM.pdf). Second edition, Logic Matters corrected reprint August 2020. Printed p. + 14 = PDF p. | Logic planning: PA/schema 90–94; recursion/coding 107–112; beta/CRT 113–116; representation distinctions 119–121; Rosser 185–189; Goodstein sketch 220–224; derivability-condition discussion 258–261; author corrections list. Other chapter locations were checked from contents. | Planning only; no current consuming entry. | Local boundary case [SMITH-01](#smith-01). No further serious defect confirmed in these selected passages. CRT needs an explicit coprime-cancellation lemma for self-contained use. Formalized Σ₁ completeness is sketched, not fully audited; Goodstein unprovability is not proved by its introduction. | 2026-10-11 |
| [Richard Zach / Open Logic Project, *Incompleteness and Computability*](https://ic.openlogicproject.org/ic-screen.pdf). Cover Fall 2025; remix `6b09d98`, 2026-07-11, Text `9620cc7`, 2026-07-12; 329 pages. Printed p. + 17 = PDF p. | Logic planning: selected beta/simulation 81–86; minimization representation 92–96; conditional second incompleteness 117–120; halting/c.e. equivalences 136–144. Full two-page [fixed-point](https://builds.openlogicproject.org/content/incompleteness/incompleteness-provability/fixed-point-lemma.pdf) and [truth](https://builds.openlogicproject.org/content/incompleteness/incompleteness-provability/tarski-thm.pdf) modules at Text `9620cc7`; other chapter locations checked from contents. | Planning only; no current consuming entry. | Local index error [ZACH-IC-01](#zach-ic-01). Fixed-point proof depends on representation of substitution; that prerequisite was identified. Concrete derivability conditions and imported CRT proof are not fully supplied. The text shares Avigad material, so agreement is not independent corroboration. | 2026-10-11 |
| [Laurie Kirby and Jeff Paris, *Accessible Independence Results for Peano Arithmetic*](https://www.cs.tau.ac.il/~nachumd/term/Kirbyparis.pdf). BLMS 14(4), 1982, 285–293; DOI 10.1112/blms/14.4.285. | Later logic planning: all nine pages read as extracted text; Theorem 1 statement on 285; ordinal-descent argument 287–289; dependency structure of the unprovability argument 289–291. | Planning only; no current consuming entry. | Imported interval/indicator, growth and nonstandard-model results were not audited. Ordinal-heavy notation needs original-page checking. Not a complete audit or a self-contained unprovability source. | 2026-10-11 |
| [Jeremy Avigad, *Ordinal analysis without proofs*](https://www.andrew.cmu.edu/user/avigad/Papers/ordinals.pdf). Author preprint, 37 pages, copyright 2000; publication 2002, 1–36. | Later logic planning: introduction and early weak-arithmetic discussion. | Planning only; no current consuming entry. | Orientation only; later ordinal-analysis proofs were not audited. Preprint pagination is not publication pagination. | 2026-10-11 |
| [Jeremy Avigad, *Proof Theory*](https://arxiv.org/pdf/1711.01994v2). arXiv v2, 2017-12-16; 13 pages. | Later logic planning: §2, 2–4, natural-deduction/sequent rules and cut-elimination/Herbrand statements. | Planning only; no current consuming entry. | Survey/statement scope. The full cut-elimination proof is not supplied or certified by this reading. | 2026-10-11 |
| [Jeremy Avigad, *Classical and constructive logic*](https://www.andrew.cmu.edu/user/avigad/Teaching/classical.pdf). 2000-09-19, revised 2001-11-02; 23 pages. | Later logic planning: introductory §§1–2, 1–7, classical/constructive examples and selected elementary number-theory arguments, read from extracted PDF text. | Planning only; no current consuming entry. | Local [AVIGAD-CC-01](#avigad-cc-01). No audit of later translations or constructive analysis; the introductory discussion is not a proof source for those claims. | 2026-10-11 |
| [Jeremy Avigad, *Mathematical Logic and Computation*](https://assets.cambridge.org/97811084/78755/frontmatter/9781108478755_frontmatter.pdf). Cambridge University Press, 2022; DOI 10.1017/9781108778756. | Bibliographic reserve: publisher front matter/contents and chapter locations only. | Planning only; no current consuming entry. | No mathematical proof audit; full chapter proofs unavailable in this pass. Findings about the 2002/2007 notes are not attributed to this book. | 2026-10-11 |
| [Boolos, Burgess and Jeffrey, *Computability and Logic*](https://assets.cambridge.org/97805217/01464/frontmatter/9780521701464_frontmatter.pdf). Fifth edition, Cambridge University Press, 2007; DOI 10.1017/CBO9780511804076. | Bibliographic reserve: publisher metadata/front matter only. | Planning only; no current consuming entry. | No mathematical proof audit; no complete accessible primary text was inspected. | 2026-10-11 |
| [Christopher C. Leary and Lars Kristiansen, *A Friendly Introduction to Mathematical Logic*](https://textbooks.aimath.org/textbooks/approved-textbooks/leary-kristiansen/). Second edition, 2015. | Bibliographic reserve: AIM edition/catalog and chapter descriptions only. | Planning only; no current consuming entry. | No mathematical proof audit. Publisher download timed out; inaccessible chapter proofs were not read. | 2026-10-11 |
| [David Marker, *An Invitation to Mathematical Logic*](https://homepages.math.uic.edu/~marker/ml-web.pdf). Author-hosted 12-page preface/contents preview, retrieved 2026-10-11; edition date not established from this preview. | Bibliographic reserve: title, preface, chapter overview and contents only. | Planning only; no current consuming entry. | No chapter proof audit; the available preview does not contain the book's completeness or incompleteness proofs. | 2026-10-11 |
| [Stephen Cook, *CSC 438F/2404F Notes*, propositional portion](https://www.cs.toronto.edu/~sacook/csc438h/notes/page1revised.pdf). Cover Winter 2014; Fall 2017 course hosting; 18 pages. Printed p. = PDF p. | Planning and entry check: 3–4, truth clauses/consequence; 16, three compactness formulations and complete countable-atom pruning/König proof; 17, uncountable exercise outlines. Normal-form material on 5–6 located, not needed as the main proof source. | [Countable propositional compactness](entries/propositional-compactness/entry.html#countable-atoms); [finite semantic support](entries/propositional-compactness/entry.html#finite-semantic-support). | No serious defect found in the countable argument. Handle finite or empty atom types separately instead of assuming an infinite distinct-atom listing; the corpus also has atomless truth/falsity formulas. General-atom exercise proofs were not completed in this source audit. | 2026-10-12 |
| [Stephen Cook, first-order CSC 438F/2404F notes, portion beginning at 18](https://www.cs.toronto.edu/~sacook/csc438h/notes/page18.pdf), and [portion beginning at 39](https://www.cs.toronto.edu/~sacook/csc438h/notes/page39.pdf). Fall 2008 version. | Planning: 27, alpha-renaming; 41, six quantifier equivalences and prenex recipe. | Planning alternative only; no current consumer. | Freshness conditions are stated, but proofs are verification exercises/recipes. These portions are a different dated version from the Winter 2014 propositional portion and are not a fully supplied prenex proof. | 2026-10-12 |
| [Dino Rossegger, *Introduction to mathematical logic*](https://drossegger.github.io/assets/files/pmath330_notes.pdf). PMATH 330 Fall 2019, compiled 2023-10-13; 91 pages. Printed p. = PDF p. | Planning: 79–84, §3.3.2, Lemma 3.3.15(4)–(6) quantifier duality, scope and correctly fresh alpha-renaming; Lemma 3.3.17 reduced-basis prenex proof. Actual notation and conjunction step visually checked. | [Fresh renaming](entries/first-order-normal-forms/entry.html#fresh-renaming); [negation normal form](entries/first-order-normal-forms/entry.html#negation-normal-form); [prenex form](entries/first-order-normal-forms/entry.html#prenex-normal-form). | No serious defect found in this scope. Expand the subsidiary structural induction, existential scope case and falsity base. The additional disjunction/implication rules are exercises; that is not a source error. Earlier replacement is supported by existing corpus locality/substitution results. Other chapters were not proof-audited. | 2026-10-12 |
| [Will Boney, *MATH 144: Course Notes*](https://people.math.harvard.edu/~wboney/spring16/144-modeltheory-notes_02_05_2016.pdf). PDF dated 2016-02-02; February 1/3/5 lecture headings; 13 pages. Printed p. = PDF p. | Planning: 1–3, Definition 4.1, closure sketch 4.3, and actual proofs of counting 4.4 and automorphism invariance 4.5; adjacent Example 4.2(3). 8–9, Lemma 5.7's induced-subgraph formula and adjacent coloring context. Relevant original formulas visually checked. | [Definable sets](entries/definability-and-automorphisms/entry.html#definable-sets); [closure](entries/definability-and-automorphisms/entry.html#boolean-closure); [automorphism invariance](entries/definability-and-automorphisms/entry.html#invariance); [counting definitions](entries/definability-and-automorphisms/entry.html#counting-definitions). Algebra/graph examples unused. | Serious [BONEY-02](#boney-02); local [BONEY-01](#boney-01). The selected counting/invariance arguments are unaffected. The general closure proof is compressed and needs expansion; complex-field and saturation claims are outside the checked proof scope. | 2026-10-12 |
| [Marcus Tressl, *Predicate Logic*](https://personalpages.manchester.ac.uk/staff/Marcus.Tressl/teaching/Goedel/PredicateLogic.pdf). Dated 2018-02-17; 63 pages. Printed p. + 1 = PDF p. | Planning: Definition 1.6.6, 17; §6, 56–57, quantifier scope, alpha Lemma 6.3 and prenex Theorem 6.4. Original alpha statement and proof's prefix step visually inspected. | Planning alternative only; no current consumer. | [TRESSL-PRED-01](#tressl-pred-01). Use a fresh new variable; the prenex theorem remains correct after repairing this prerequisite and expanding the routine prefix argument. Different publication from Tressl's 2026 model-theory notes. | 2026-10-12 |
| [Philipp Schlicht, *Lecture Notes: An Introduction to Model Theory*](https://philippschlicht.github.io/teaching/files/modeltheory2017.pdf). Bonn October–November 2017 course; PDF dated 2021-07-13; 31 pages. Printed p. = PDF p. | Planning: 4, original-language theory/elementary-diagram distinction and Lemma 1.1.15; 6, upward Theorem 1.2.8(2); 7, full finite-axiomatizability Lemma 1.2.9 and connectedness Example 1.2.10. Original diagram notation/date visually checked. | Planning only; expressive-limit extension candidate. | [SCHLICHT-02](#schlicht-02) affects the adjacent upward construction. No serious defect found in the finite-axiomatizability proof. Connectedness needs the stated-easy finite-path witness supplied explicitly. Different publication from the 2021 mathematical-logic course notes. | 2026-10-12 |
| [Alex Kruckman, *Math 509 Lecture Notes*](https://akruckman.faculty.wesleyan.edu/files/2025/12/Lecture-Notes.pdf). Fall 2025, updated 2025-12-18; 92 pages; [author inventory](https://akruckman.faculty.wesleyan.edu/notes-slides/). Printed p. = PDF p. | Planning: Proposition 2.8, 15, embeddings and literals; §2.4, 18–19, Proposition 2.19's full diagram-to-morphism proof on 19; Theorem 5.19/Corollary 5.20, 48, finite-diagram/elementary amalgamation; Theorem 5.21 and Corollaries 5.22–5.23, 48–49, preservation converse. The opening direct-limit construction on 49–50 was inspected only. | Planning only; proposed `diagrams-and-extensions`, later preservation branch. | No serious mathematical defect confirmed in these narrow scopes. Signed diagrams and positive diagrams are distinguished explicitly. Full direct-limit and other graduate-course developments were not audited. | 2026-10-12 |
| [Samuel R. Buss, *Introduction to Mathematical Logic*](https://www.math.ucsd.edu/~sbuss/IntroMathLogic/Fullbook_Draft.pdf). Draft B.2.e, 2023-08-14; 302 PDF pages. Printed p. + 7 = PDF p. | Planning cross-check: Theorem III.64, 99–100, fresh bound-variable renaming; §III.8, 104–107, prenex transformation and decreasing-pair measure. | Independent cross-check for [fresh renaming](entries/first-order-normal-forms/entry.html#fresh-renaming) and [prenex form](entries/first-order-normal-forms/entry.html#prenex-normal-form). | Correct fresh-variable hypotheses. Scope and transformation details partly remain exercises, so not a fully detailed proof source. Adjacent Example III.65 is excluded from the adopted scope; its notation was not visually audited. | 2026-10-12 |
| [P. Madhusudan and Mahesh Viswanathan, *Logic in Computer Science*](https://courses.grainger.illinois.edu/CS474/fa2021/DraftNotes.pdf). Rough course notes, 2021-10-11; 106 PDF pages. | Planning search: cover/contents; §1.4 compactness, 16–20, and §2.2 resolution, 27–34, located. Opening compactness definitions and finite-support argument were inspected in web text; complete resolution proof not yet audited. | Planning only; optional finite-resolution branch. | Source collection/limited passage check only, not whole-chapter certification. Requires a full selected-proof audit before an entry. Complexity, planar graphs and other applications were not adopted. | 2026-10-12 |
| [Cambridge, *Logic and Proof*, 2024–25 course notes](https://www.cl.cam.ac.uk/teaching/2425/LogicProof/logic-notes.pdf). 35 PDF pages; course-year URL identifies the version. | Planning alternative: §5.3 quantifier duality and scope-motion rules; §7 Skolemization discussion. | Planning only; normal-form/Skolemization alternatives, no current consumer. | Scope-motion freshness conditions are present. This pass located transformation rules and examples, not a full prenex or Skolemization proof. No broad no-defect claim. | 2026-10-12 |
| [Thomas Scanlon, Math 225A lecture notes, 2013-10-09](https://math.berkeley.edu/~scanlon/225af13lectures/20131009Lec4.pdf). Seven PDF pages. | Planning alternative: p. 5 definable-set invariance under parameter-fixing automorphisms, from primary web text. | Planning only; alternative definability reference, no current consumer. | Lemma statement inspected; a full proof audit of the lecture's infinitary-logic/arithmetic material was not performed. Boney's elementary proof and existing isomorphism invariance supply the chosen argument. | 2026-10-12 |

## Maintenance

Follow the [source-error contract](../docs/corpus.md#source-errors). Before reusing
a cited argument, read its existing records. Save new confirmed findings and
extensions of checked coverage during the same pipeline step; do not leave them
only in chat or a pull request. Keep stable finding IDs, exact source versions and
locations, evidence, repairs, and actual entry/block links. Keep unsupported
suspicions in the task handoff, clearly marked as uncertain.

When a publication changes, record which revision was checked. Preserve previous
findings and add the upstream resolution rather than deleting their history.
Keep each check date attached to its reviewed scope when extending coverage.
Do not conflate an upstream fix with a correct corpus proof. Keep entry editorial
issues and Lean correspondence issues in their own review handoffs.
