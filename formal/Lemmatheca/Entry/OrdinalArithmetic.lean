import Lemmatheca.SetTheory.Ordinals
import Lemmatheca.Entry.WellOrderedSets

/-! Explicit order-preserving maps used in the arithmetic examples.
`Prod.Lex` puts the block index first, unlike coordinatewise product order. -/
namespace Lemmatheca.Entry.OrdinalArithmetic
open Ordinal Order
open scoped Ordinal

/-- The extra first point goes to zero; the following naturals shift by one. -/
def firstPointEnumeration : Unit ⊕ ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr n => n + 1

theorem firstPointEnumeration_order_iso :
    Function.Bijective firstPointEnumeration ∧
    ∀ x y, Sum.Lex (@emptyRelation Unit) ((· < ·) : ℕ → ℕ → Prop) x y ↔
      firstPointEnumeration x < firstPointEnumeration y := by sorry

def twoPointBlocks (p : ℕ × Fin 2) : ℕ := 2 * p.1 + p.2.val

theorem twoPointBlocks_order_iso :
    Function.Bijective twoPointBlocks ∧
    ∀ x y, Prod.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : Fin 2 → Fin 2 → Prop) x y ↔
      twoPointBlocks x < twoPointBlocks y := by sorry

/-- Recursion determines addition, including every nonzero limit stage. -/
theorem addition_recursion_unique (f : Ordinal → Ordinal → Ordinal)
    (hz : ∀ a, f a 0 = a)
    (hs : ∀ a b, f a (b + 1) = f a b + 1)
    (hl : ∀ a l, IsSuccLimit l → f a l = ⨆ b : Set.Iio l, f a b.val) :
    f = (· + ·) := by sorry

theorem multiplication_recursion_unique (f : Ordinal → Ordinal → Ordinal)
    (hz : ∀ a, f a 0 = 0)
    (hs : ∀ a b, f a (b + 1) = f a b + a)
    (hl : ∀ a l, IsSuccLimit l → f a l = ⨆ b : Set.Iio l, f a b.val) :
    f = (· * ·) := by sorry

end Lemmatheca.Entry.OrdinalArithmetic
