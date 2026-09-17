import Std

/-!
# A first sumset example

Sets of integers are represented by membership predicates. This small example
uses Lean's standard library only; it does not yet formalize the general finite
cardinality bound from the human corpus.
-/

namespace Lemmatheca

/-- An integer set, represented by its membership predicate. -/
abbrev IntSet := Int → Prop

/-- A sum belongs to `sumset A B` when it has a representation using one element
from each summand. Different representations do not create different elements. -/
def sumset (A B : IntSet) : IntSet :=
  fun x => ∃ a b : Int, A a ∧ B b ∧ a + b = x

/-- Fixing an element of the second summand puts a translate of the first
summand inside the sumset. -/
theorem translate_mem_sumset {A B : IntSet} {a b : Int}
    (ha : A a) (hb : B b) : sumset A B (a + b) := by
  exact ⟨a, b, ha, hb, rfl⟩

/-- Translation does not identify distinct integers: the cancellation step in
the human proof of the sumset lower bound. -/
theorem translate_injective (b : Int) :
    ∀ a a' : Int, a + b = a' + b → a = a' := by
  intro a a' h
  calc
    a = (a + b) - b := (Int.add_sub_cancel a b).symm
    _ = (a' + b) - b := congrArg (fun z : Int => z - b) h
    _ = a' := Int.add_sub_cancel a' b

/-- The first concrete example in `examples/sumsets/definition.md`:
`{0, 1} + {0, 2} = {0, 1, 2, 3}`, expressed as equivalence of membership.

The forward direction checks the four possible pairs. The reverse direction
explicitly supplies a representing pair for each of the four possible sums. -/
theorem example_sumset (x : Int) :
    sumset (fun a => a = 0 ∨ a = 1) (fun b => b = 0 ∨ b = 2) x ↔
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  constructor
  · intro hx
    rcases hx with ⟨a, b, ha, hb, rfl⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  · intro hx
    rcases hx with h | h | h | h
    · subst x
      exact ⟨0, 0, Or.inl rfl, Or.inl rfl, rfl⟩
    · subst x
      exact ⟨1, 0, Or.inr rfl, Or.inl rfl, rfl⟩
    · subst x
      exact ⟨0, 2, Or.inl rfl, Or.inr rfl, rfl⟩
    · subst x
      exact ⟨1, 2, Or.inr rfl, Or.inr rfl, rfl⟩

end Lemmatheca
