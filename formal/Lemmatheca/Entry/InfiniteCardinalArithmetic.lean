import Lemmatheca.SetTheory.Choice
import Lemmatheca.Entry.FiniteAndCountableSets
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit witnesses for infinite arithmetic. The square order compares
(maximum, first coordinate, second coordinate) lexicographically.
New theorem bodies are intentionally unfinished at pipeline step 4. -/
namespace Lemmatheca.Entry.InfiniteCardinalArithmetic
open Set Function Ordinal Order
open scoped Ordinal
universe u

/-- Move the new final point to zero, shift finite positions, and fix all others. -/
noncomputable def successorShift (a b : Ordinal.{u}) : Ordinal.{u} :=
  if b = a then 0 else if b < ω then b + 1 else b

theorem successorShift_bijection (a : Ordinal.{u}) (ha : ω ≤ a) :
    Set.BijOn (successorShift a) (Set.Iio (a + 1)) (Set.Iio a) := by sorry

/-- The maximum is the primary key; the two coordinates break ties. -/
def squareLT {α : Type u} [LinearOrder α] (p q : α × α) : Prop :=
  Prod.Lex ((· < ·) : α → α → Prop)
    (Prod.Lex ((· < ·) : α → α → Prop) ((· < ·) : α → α → Prop))
    (max p.1 p.2, p) (max q.1 q.2, q)

theorem squareLT_wellOrder {α : Type u} [LinearOrder α] [WellFoundedLT α] :
    IsWellOrder (α × α) squareLT := by sorry

theorem squareLT_predecessors {α : Type u} [LinearOrder α] (p q : α × α)
    (hp : squareLT p q) : p.1 ≤ max q.1 q.2 ∧ p.2 ≤ max q.1 q.2 := by sorry

/-- The small domain keeps ranks in the cardinal's original universe. -/
noncomputable def squareRank (c : Cardinal.{u})
    (h : IsWellOrder (c.ord.ToType × c.ord.ToType) squareLT)
    (p : c.ord.ToType × c.ord.ToType) : Ordinal.{u} :=
  @Ordinal.typein (c.ord.ToType × c.ord.ToType) squareLT h p

theorem squareRank_injection (c : Cardinal.{u}) (hc : Cardinal.aleph0 ≤ c)
    (h : IsWellOrder (c.ord.ToType × c.ord.ToType) squareLT) :
    Function.Injective (squareRank c h) ∧ ∀ p, squareRank c h p < c.ord := by sorry

/-- Finite shell ranks displayed in the figure. -/
def shellRank (p : ℕ × ℕ) : ℕ :=
  let m := max p.1 p.2
  m * m + if p.1 < m then p.1 else m + p.2

theorem shellRank_order_iso :
    Function.Bijective shellRank ∧
    ∀ p q : ℕ × ℕ, squareLT p q ↔ shellRank p < shellRank q := by sorry

theorem shellRank_figure :
    (List.range 5).map (fun i => (List.range 5).map (fun j => shellRank (i, j))) =
      [[0, 1, 4, 9, 16], [2, 3, 5, 10, 17], [6, 7, 8, 11, 18],
       [12, 13, 14, 15, 19], [20, 21, 22, 23, 24]] := by sorry

/-- Use the least containing index and that set's supplied encoding. -/
noncomputable def unionCode {α : Type u} (A : ℕ → Set α)
    (e : ∀ n, A n → ℕ) (x : ⋃ n, A n) : ℕ × ℕ := by
  classical
  let hx : ∃ n, x.val ∈ A n := Set.mem_iUnion.mp x.property
  let n := Nat.find hx
  exact (n, e n ⟨x.val, Nat.find_spec hx⟩)

theorem unionCode_injective {α : Type u} (A : ℕ → Set α) (e : ∀ n, A n → ℕ)
    (he : ∀ n, Function.Injective (e n)) : Function.Injective (unionCode A e) := by sorry

/-- Which enumerated rationals lie below the real number? -/
def rationalCut (x : ℝ) : Set ℕ :=
  {n | (Lemmatheca.Entry.FiniteAndCountableSets.rationalList n : ℝ) < x}

theorem rationalCut_injective : Function.Injective rationalCut := by sorry

/-- The explicit rational between x and y in the density argument. -/
theorem separating_rational (x y : ℝ) (hxy : x < y) (n : ℕ)
    (hn : 1 < (n : ℝ) * (y - x)) :
    let q : ℚ := ((Int.floor ((n : ℝ) * x) + 1 : ℤ) : ℚ) / (n : ℚ)
    x < (q : ℝ) ∧ (q : ℝ) < y := by sorry

noncomputable def ternaryTerm (S : Set ℕ) (n : ℕ) : ℝ :=
  @ite ℝ (n ∈ S) (Classical.propDecidable _) (2 / (3 : ℝ) ^ (n + 1)) 0

noncomputable def ternaryCode (S : Set ℕ) : ℝ := ∑' n, ternaryTerm S n

theorem ternaryCode_spec :
    (∀ S, Summable (ternaryTerm S)) ∧
    (∀ S, ternaryCode S ∈ Set.Icc (0 : ℝ) 1) ∧
    Function.Injective ternaryCode := by sorry

/-- The first differing digit dominates all subsequent digits. -/
theorem ternaryCode_first_difference (S T : Set ℕ) (k : ℕ)
    (hbefore : ∀ n < k, n ∈ S ↔ n ∈ T) (hkS : k ∈ S) (hkT : k ∉ T) :
    (1 : ℝ) / 3 ^ (k + 1) ≤ ternaryCode S - ternaryCode T := by sorry

end Lemmatheca.Entry.InfiniteCardinalArithmetic
