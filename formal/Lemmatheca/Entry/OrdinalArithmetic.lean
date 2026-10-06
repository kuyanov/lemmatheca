import Lemmatheca.SetTheory.OrdinalArithmetic
import Lemmatheca.SetTheory.Ordinals

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.OrdinalArithmetic
open Lemmatheca.SetTheory.OrdinalArithmetic
open Ordinal Order
open scoped Ordinal

/-- The extra first point goes to zero; the following naturals shift by one. -/
def firstPointEnumeration : Unit ⊕ ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr n => n + 1

theorem firstPointEnumeration_order_iso :
    Function.Bijective firstPointEnumeration ∧
    ∀ x y, Sum.Lex (@emptyRelation Unit) ((· < ·) : ℕ → ℕ → Prop) x y ↔
      firstPointEnumeration x < firstPointEnumeration y := by
  constructor
  · constructor
    · intro x y h
      cases x with
      | inl a =>
        cases y with
        | inl b => cases a; cases b; rfl
        | inr b => exact Nat.noConfusion h
      | inr a =>
        cases y with
        | inl b => exact Nat.noConfusion h
        | inr b => exact congrArg Sum.inr (Nat.succ_inj.mp h)
    · intro n
      cases n with
      | zero => exact ⟨Sum.inl (), rfl⟩
      | succ n => exact ⟨Sum.inr n, rfl⟩
  · intro x y
    cases x <;> cases y <;>
      simp only [Sum.lex_inl_inl, Sum.lex_inr_inl, Sum.lex_inr_inr,
        firstPointEnumeration, emptyRelation, Nat.not_lt_zero, Nat.zero_lt_succ,
        Nat.succ_lt_succ_iff]
    exact ⟨fun _ => trivial, fun _ => Sum.Lex.sep _ _⟩

def twoPointBlocks (p : ℕ × Fin 2) : ℕ := 2 * p.1 + p.2.val

theorem twoPointBlocks_order_iso :
    Function.Bijective twoPointBlocks ∧
    ∀ x y, Prod.Lex ((· < ·) : ℕ → ℕ → Prop) ((· < ·) : Fin 2 → Fin 2 → Prop) x y ↔
      twoPointBlocks x < twoPointBlocks y := by
  constructor
  · constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ h
      have ha := a.isLt
      have hb := b.isLt
      simp only [twoPointBlocks] at h
      have hij : i = j := by omega
      have hab : a = b := Fin.ext (by omega)
      simp [hij, hab]
    · intro n
      refine ⟨(n / 2, ⟨n % 2, Nat.mod_lt n (by decide)⟩), ?_⟩
      simp only [twoPointBlocks]
      omega
  · rintro ⟨i, a⟩ ⟨j, b⟩
    have ha := a.isLt
    have hb := b.isLt
    simp only [Prod.lex_iff, twoPointBlocks, Fin.lt_def]
    constructor
    · rintro (h | ⟨h, h'⟩) <;> omega
    · intro h
      rcases Nat.lt_trichotomy i j with hij | hij | hij
      · exact Or.inl hij
      · exact Or.inr ⟨hij, by omega⟩
      · omega

end Lemmatheca.Entry.OrdinalArithmetic
