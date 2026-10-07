# Source errors

Last checked: **2026-10-08**. Scope: the publications cited by the current **42
entries**, using their `based_on` locations and the named results those citations
identify, together with explicitly scoped supporting, adjacent, and entry-planning passages.
The [coverage](#coverage) records **37 distinct publications**: all 31 directly
cited publications, one checked supporting publication, and five planning sources.
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
The corpus does not currently define `a` or assert the affected invariant bounds.

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
material on a cited page; [the almost-disjoint entry](entries/almost-disjoint-families/entry.html#maximal-almost-disjoint)
does not use this inequality or construction.

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
| [Andrew Marks, *Set Theory*](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf). Updated 2026-01-31; 106-page PDF. Printed p. = PDF p. | 4; 10–13; 15–41; 43–53; 61–65; 68–69; adjacent 14, 42, 54, and the named Mostowski theorem on 32; 73–74, Definition 17.7, Proposition 17.8, Theorem 17.9 and supporting Lemma 17.10. The tree proof is supplemented with explicit coding and normality details; Suslin-line equivalence is not adopted. Statements, definitions, and supplied proofs in these passages. | [The axiom of choice](entries/axiom-of-choice/entry.html); [Axiomatic set theory](entries/axiomatic-set-theory/entry.html); [Clubs and stationary sets](entries/clubs-and-stationary-sets/entry.html); [Cofinality](entries/cofinality/entry.html); [The continuum function](entries/continuum-function/entry.html); [The cumulative hierarchy](entries/cumulative-hierarchy/entry.html); [Filters and ultrafilters](entries/filters-and-ultrafilters/entry.html); [Foundation](entries/foundation-and-rank/entry.html); [Infinite cardinal arithmetic](entries/infinite-cardinal-arithmetic/entry.html); [Infinite sums and products](entries/infinite-sums-and-products/entry.html); [Infinite trees](entries/infinite-trees/entry.html); [Diamond and Suslin trees](entries/diamond-and-suslin-trees/entry.html); [The Mostowski collapse](entries/mostowski-collapse/entry.html); [Natural numbers as sets](entries/natural-numbers-as-sets/entry.html); [Normal functions](entries/normal-functions/entry.html); [Ordinal arithmetic](entries/ordinal-arithmetic/entry.html); [Ordinal powers](entries/ordinal-powers/entry.html); [Ordinals](entries/ordinals/entry.html); [Pressing down](entries/pressing-down-and-delta-systems/entry.html); [Weaker forms of choice](entries/weaker-forms-of-choice/entry.html); [Well-ordered sets](entries/well-ordered-sets/entry.html) | [MARKS-01](#marks-01)–[18](#marks-18); local [19](#marks-19)–[20](#marks-20). Named results were checked on their actual pages even where corpus page ranges were inaccurate. The enormous Goodstein terminal index and historical independence attributions were not independently verified. | 2026-10-07 |
| [Peter Philip, *Axiomatic Set Theory*](https://www.math.lmu.de/~philip/publications/lectureNotes/philipPeter_AxiomaticSetTheory.pdf). Title-page revision 2025-12-30 (course originally summer 2024). Printed p. = PDF p. | 33–34; 58–60; 89–92; 100–101; 111–112; 117–121; 137–138; 147–149; 165–168; contextual definitions on 32, 35–36, 99, 116. Planning check: Appendix C, 162–164, Proposition C.2 and its proof, Lemma C.3, and Theorem C.5 implications; the converse was independently checked without Lemma C.4. C.4 is not certified. | [The axiom of choice](entries/axiom-of-choice/entry.html); [The continuum function](entries/continuum-function/entry.html); [The cumulative hierarchy](entries/cumulative-hierarchy/entry.html); [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html); [Normal functions](entries/normal-functions/entry.html); [Weaker forms of choice](entries/weaker-forms-of-choice/entry.html) | [PHILIP-01](#philip-01)–[04](#philip-04); local [05](#philip-05). The cited normal-function, beth, Hartogs, Choice-equivalence, Foundation, and relation-composition arguments are otherwise valid in the checked scope. No new serious defect found in the checked Tarski-converse passages. | 2026-10-07; planning 2026-10-08 |
| [Richard Hammack, *Book of Proof*](https://richardhammack.github.io/BookOfProof/Main.pdf). Third edition, revision 3.4; copyright 2018, PDF generated 2025-02-05. Printed p. + 12 = PDF p. | 233; 269–287: finite pigeonhole, enumerations, countability, cardinal comparison, Cantor, and the full supplied Cantor–Bernstein proof. | [Comparing sizes](entries/comparing-sizes/entry.html); [Finite and countable sets](entries/finite-and-countable-sets/entry.html) | No serious mathematical defect found. Canonical decimals and repetition-free enumerations are valid conventions, rather than proof errors. | 2026-10-07 |
| [Martin Bays, *B1.2 Set Theory*](https://people.maths.ox.ac.uk/bays/teaching/b1set/B1.2.pdf). HT26 Oxford; PDF generated 2026-03-13. Printed p. = PDF p. | 38–39: initial cardinals and aleph recursion; 42: Definition 9.12 and cardinal arithmetic; 43: Theorem 10.2(ii), with adjacent Definition 10.1 on 42–43. | [Cofinality](entries/cofinality/entry.html); [Finite and countable sets](entries/finite-and-countable-sets/entry.html); [Infinite cardinal arithmetic](entries/infinite-cardinal-arithmetic/entry.html) | [BAYS-01](#bays-01)–[02](#bays-02). The initial-cardinal, aleph, and CH passages are valid under the source’s explicit Choice assumption. | 2026-10-07 |
| [Jonathan Pila, *B1.2 Set Theory*](https://www.maths.ox.ac.uk/system/files/attachments/SetTheoryHT18.pdf). HT2018; PDF metadata 2018-01-03. Printed p. = PDF p. | §14, 36–39: ordinal arithmetic and order interpretations, specifically Lemma 14.9 and Theorem 14.11, and the displayed finite Goodstein illustration. | [Ordinal arithmetic](entries/ordinal-arithmetic/entry.html) | [PILA-01](#pila-01), in the supporting order-sum proof. Lemma 14.9 and Theorem 14.11 are valid. | 2026-10-07 |
| [Ivo Terek, *Equivalence Relations, Quotients, and Examples*](https://math-terek.github.io/texts/quotients.pdf). Undated PDF; generation metadata 2021-07-23. Printed p. = PDF p. | §1, 1–4 through Corollary 1: equivalence classes, partitions, fibers, quotient factorization, and quotient-to-image bijection. §2’s vector-space material is outside this audit. | [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html) | [TEREK-01](#terek-01)–[02](#terek-02). The quotient propositions and their proofs are otherwise valid, including empty carriers. | 2026-10-07 |
| [Romyar Sharifi, *Abstract Algebra — Chapter 1: Set theory*](https://www.math.ucla.edu/~sharifi/notes/algebra-ch01.html). Undated HTML retrieved 2026-10-07. | Example 1.3.16 in full, with the positive-modulus convention from Example 1.2.6(c). The rest of the chapter was not audited. | [Equivalence relations, partitions, and quotients](entries/equivalence-relations/entry.html) | No serious mathematical defect found in the cited class-arithmetic example. | 2026-10-07 |
| [Mariusz Wodzicki, *Notes on Ordered Sets*](https://math.berkeley.edu/~wodzicki/H104/OrderedSets.pdf). 2009-09-22. Printed p. = PDF p. | 1–7, §§1.1–1.2: Definitions 1.1–1.6, Exercises 1–7, identities (1)–(40), order duality, bounds, and closure identities. | [Ordered sets](entries/ordered-sets/entry.html) | No serious mathematical defect found. Empty-set and empty-poset qualifications are correctly handled. | 2026-10-07 |
| [Patrick Cousot, *Lattice theory — Part I*](https://web.mit.edu/16.399/www/lecture_09-lattice1/Cousot_MIT_2005_Course_09_4-1.pdf). MIT 16.399, 2005-03-17. Four slides per PDF page; slide s is on PDF page ⌈s/4⌉. | Slides 6–28, 34–36, 41–42: orders, preorder quotients, restrictions, duality, chains, antichains, extrema, and Hasse diagrams. Later lattice/ACC material is outside this audit. | [Ordered sets](entries/ordered-sets/entry.html) | No serious defect in the main constructions; local symbol slips [COUSOT-01](#cousot-01). | 2026-10-07 |
| [Alfred Tarski, *A lattice-theoretical fixpoint theorem and its applications*](https://people.csail.mit.edu/carroll/probSem/Documents/Tarski.pdf). *Pacific Journal of Mathematics* 5(2), 1955; received 1953-06-29. Printed 285 = PDF 1. | 285–287: definitions and the complete proof of Theorem 1. | [Ordered sets](entries/ordered-sets/entry.html) | No serious mathematical defect found. The invariant interval and the fixed-point lattice’s bounds are justified. | 2026-10-07 |
| [William A. R. Weiss, *An Introduction to Set Theory*](https://www.math.toronto.edu/~weiss/Set_Theory.pdf). 2014-11-21. Both `/weiss/` and `/~weiss/` citations identify this edition; printed p. = PDF p. in the checked ranges. | 63–64: Mostowski Theorems 19–20 and Exercise 14; 79–82: dense linear orders and adjacent almost-disjoint construction; 89: Theorem 33 and Exercise 29. Planning check: 101–102, Theorems 41–42 and Exercise 34 on hereditary cardinality and inaccessible closure; 149, measurable-cardinal definition; 151, Theorem 59 and its complete direct proof that a measurable cardinal is strongly inaccessible. | [Dense linear orders](entries/dense-linear-orders/entry.html); [The Mostowski collapse](entries/mostowski-collapse/entry.html); [Partition relations](entries/partition-relations/entry.html); [Hereditarily small sets](entries/hereditarily-small-sets/entry.html#hereditary-rank-bound) | [WEISS-01](#weiss-01), in the adjacent almost-disjoint construction; local [02](#weiss-02), in the Ramsey tree indexing. The Mostowski and dense-order arguments are valid. No new serious defect found in these planning passages; model-theoretic claims are outside this check. | 2026-10-07; planning 2026-10-08 |
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
| [Andreas Blass, *Combinatorial Cardinal Characteristics of the Continuum*](https://sites.lsa.umich.edu/ablass/wp-content/uploads/sites/1471/2025/10/hbk.pdf). Author draft dated 2003-11-24, 104-page PDF; printed p. = PDF p. The 2025 hosting path is not the revision date. | 37, Definition 6.16 and Remark 6.17; 39–40, Definitions 6.22 and Proposition 6.23; 51–52, Proposition 8.1, Definition 8.3 and Proposition 8.4; 56–58, Definition 9.1 and Definition 9.6. Definitions, finite-change reduction and the bounding comparison checked; forcing assertions are outside this review. Planning check: Theorem 2.6, Definition 2.9/Theorem 2.10; Definition 3.1/Theorem 3.3 and Definition 3.6/Theorem 3.8; Definition 6.2/Proposition 6.4, direct thinning in Proposition 6.8/Theorem 6.9, Theorem 6.14/Corollary 6.15, Proposition 6.24/Theorem 6.25; Definition 8.11/Proposition 8.12/Theorem 8.13. This covers elementary scales, interval partitions, splitting/reaping, towers, and maximal independence; forcing proofs remain outside the check. | [Small families of subsets](entries/small-families-of-subsets/entry.html); [Splitting and reaping](entries/splitting-and-reaping/entry.html#cardinal-comparisons) | No serious defect in the adopted passages. In 8.4 the omitted partition adjustment is valid: remove finitely many overlaps from each selected set, then distribute residual points finitely among them. The entry uses a direct selection proof. The free-filter convention in 9.1 must be retained in 9.6. No new serious defect found in these elementary passages. The 2003 discussion of whether p<t is historical: p=t is now known, as recorded in the Malliaris–Shelah planning row. | 2026-10-07; planning 2026-10-08 |
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
