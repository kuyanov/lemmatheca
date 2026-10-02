import Lemmatheca.SetTheory.WellOrders
import Lemmatheca.Entry.FiniteAndCountableSets
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Well-ordered-sets entry: concrete relations and worked answers

`WithTop ℕ` represents the natural numbers followed by the new point ℓ.
`ℕ ×ₗ ℕ` carries first-coordinate-priority lexicographic order, not product order.
Integer comparison below is explicitly pulled back along `Equiv.intEquivNat`.
-/

namespace Lemmatheca.Entry.WellOrderedSets

open Lemmatheca.SetTheory

def integerEnumerationLT (a b : ℤ) : Prop := Equiv.intEquivNat a < Equiv.intEquivNat b

theorem usual_orders_fail :
    ¬ WellFounded ((· < ·) : ℤ → ℤ → Prop) ∧
    ¬ WellFounded ((· < ·) : ℚ → ℚ → Prop) ∧
    ¬ WellFounded ((· < ·) : ℝ → ℝ → Prop) ∧
    ¬ WellFounded ((· < ·) : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 → Prop) ∧
    (∀ z : ℤ, z - 1 < z) ∧
    (∀ x : ℚ, x ∈ Set.Ioo 0 1 → x / 2 ∈ Set.Ioo 0 1 ∧ x / 2 < x) ∧
    (∀ x : ℝ, x ∈ Set.Ioo 0 1 → x / 2 ∈ Set.Ioo 0 1 ∧ x / 2 < x) := by
  sorry

theorem discrete_two_has_no_least :
    ¬ Std.Total ((· = ·) : Fin 2 → Fin 2 → Prop) ∧
    ¬ ∃ a : Fin 2, ∀ b : Fin 2, a = b := by
  sorry

def topEnumeration : ℕ → WithTop ℕ
  | 0 => ⊤
  | n + 1 => (n : WithTop ℕ)

theorem topEnumeration_bijective : Function.Bijective topEnumeration := by
  sorry

theorem top_order_structure :
    Set.Iio (⊤ : WithTop ℕ) = Set.range (fun n : ℕ => (n : WithTop ℕ)) ∧
    Order.IsSuccLimit (⊤ : WithTop ℕ) ∧ IsMax (⊤ : WithTop ℕ) ∧
    (∀ n : ℕ, (n : WithTop ℕ) ⋖ ((n + 1 : ℕ) : WithTop ℕ)) ∧
    ¬ Nonempty (WithTop ℕ ≃o ℕ) := by
  sorry

theorem lex_predecessors :
    Set.Iio (toLex (1, 0) : ℕ ×ₗ ℕ) =
      Set.range (fun n : ℕ => (toLex (0, n) : ℕ ×ₗ ℕ)) ∧
    (Set.Iio (toLex (1, 0) : ℕ ×ₗ ℕ)).Infinite ∧
    ¬ Nonempty ((ℕ ×ₗ ℕ) ≃o ℕ) := by
  sorry

theorem lex_successors_limits :
    (∀ i j : ℕ, (toLex (i, j) : ℕ ×ₗ ℕ) ⋖ (toLex (i, j + 1) : ℕ ×ₗ ℕ)) ∧
    ∀ i : ℕ, 0 < i → Order.IsSuccLimit (toLex (i, 0) : ℕ ×ₗ ℕ) := by
  sorry

theorem proper_subsets_not_initial :
    ¬ IsLowerSet Lemmatheca.Entry.SetsAndMaps.evenNaturals ∧
    ¬ IsLowerSet {n : ℕ | 0 < n} := by
  sorry

theorem missing_limit_case :
    (0 : WithTop ℕ) ≠ ⊤ ∧
    (∀ a b : WithTop ℕ, a ⋖ b → a ≠ ⊤ → b ≠ ⊤) ∧
    (∀ x : WithTop ℕ, x < ⊤ → x ≠ ⊤) ∧
    ¬ ((⊤ : WithTop ℕ) ≠ ⊤) := by
  sorry

/-- p = 0, q = 1, r = 2; only p R r and q R r hold. -/
def forkDependency (a b : Fin 3) : Prop := (a = 0 ∨ a = 1) ∧ b = 2

theorem forkDependency_spec :
    WellFounded forkDependency ∧
    ¬ forkDependency 0 1 ∧ ¬ forkDependency 1 0 ∧
    (∀ b ∈ ({2} : Set (Fin 3)), ¬ forkDependency b 2) := by
  sorry

theorem proper_positive_divisibility_wellFounded :
    WellFounded (fun a b : ℕ+ => a ∣ b ∧ a ≠ b) := by
  sorry

theorem factorial_prefix : (List.range 5).map Nat.factorial = [1, 1, 2, 6, 24] := by
  sorry

def limitSetValue : WithTop ℕ → Set ℕ
  | none => Set.univ
  | some n => Set.Iio n

/-- Rules are defined even for histories that are not solutions. -/
def limitSetRule : RecursionRule (WithTop ℕ) (Set ℕ)
  | none, h => ⋃ n : ℕ, h ⟨(n : WithTop ℕ), WithTop.coe_lt_top n⟩
  | some 0, _ => ∅
  | some (n + 1), h => h ⟨(n : WithTop ℕ), by
      change (n : WithTop ℕ) < ((n + 1 : ℕ) : WithTop ℕ)
      exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)⟩ ∪ {n}

theorem limitSetValue_spec :
    (∀ x, limitSetValue x = limitSetRule x (fun b => limitSetValue b.val)) ∧
    limitSetValue 0 = ∅ ∧
    (∀ n : ℕ, limitSetValue ((n + 1 : ℕ) : WithTop ℕ) =
      limitSetValue (n : WithTop ℕ) ∪ {n}) ∧
    limitSetValue ⊤ = ⋃ n : ℕ, limitSetValue (n : WithTop ℕ) ∧
    limitSetValue ⊤ = Set.univ := by
  sorry

theorem successor_rules_leave_top_free (s : Set ℕ) :
    ∃ F : WithTop ℕ → Set ℕ, F 0 = ∅ ∧
      (∀ n : ℕ, F ((n + 1 : ℕ) : WithTop ℕ) = F (n : WithTop ℕ) ∪ {n}) ∧ F ⊤ = s := by
  sorry

end Lemmatheca.Entry.WellOrderedSets
