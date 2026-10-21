import Lemmatheca.FirstOrderStructures.BasicStructures
import Lemmatheca.FirstOrderLanguages.Examples
import Lean.Elab.Tactic.Omega

/-! Particular finite and natural-number structures for the opening semantics entry. -/

namespace Lemmatheca.Entry.FirstOrderStructures

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.MathematicalLogic.BasicStructures
open Lemmatheca.Entry.FirstOrderLanguages

local instance twoStrictStructure : binaryRelLanguage.Structure (Fin 2) :=
  binaryRelStructure (Fin 2) (· < ·)

theorem nat_parameterHasSuccessor (a : ℕ → ℕ) :
    (parameterHasSuccessor strictRel).Realize a := by
  simp only [parameterHasSuccessor, Formula.Realize, BoundedFormula.realize_ex]
  change ∃ x : ℕ, a 0 < x
  exact ⟨a 0 + 1, Nat.lt_succ_self _⟩

theorem nat_successor_witness (a : ℕ → ℕ) :
    (strictRel.boundedFormula₂ (.var (.inl 0)) (.var (.inr 0)) :
      binaryRelLanguage.BoundedFormula ℕ 1).Realize a ![a 0 + 1] := by
  change a 0 < a 0 + 1
  exact Nat.lt_succ_self _

theorem nat_everyHasSuccessor : ℕ ⊨ everyHasSuccessor strictRel := by
  simp only [Sentence.Realize, Formula.Realize, everyHasSuccessor,
    BoundedFormula.realize_all, BoundedFormula.realize_ex]
  change ∀ x : ℕ, ∃ y : ℕ, x < y
  intro x
  exact ⟨x + 1, Nat.lt_succ_self _⟩

theorem two_parameterHasSuccessor_iff (a : ℕ → Fin 2) :
    (parameterHasSuccessor strictRel).Realize a ↔ a 0 = 0 := by
  simp only [parameterHasSuccessor, Formula.Realize, BoundedFormula.realize_ex]
  change (∃ x : Fin 2, a 0 < x) ↔ a 0 = 0
  constructor
  · rintro ⟨x, hx⟩
    apply Fin.ext
    have hx' := x.isLt
    change (a 0).val < x.val at hx
    change (a 0).val = 0
    omega
  · intro h
    exact ⟨1, by simp [h]⟩

theorem two_successor_witness (a : ℕ → Fin 2) (h : a 0 = 0) :
    (strictRel.boundedFormula₂ (.var (.inl 0)) (.var (.inr 0)) :
      binaryRelLanguage.BoundedFormula ℕ 1).Realize a ![1] := by
  change a 0 < 1
  simp [h]

theorem two_not_everyHasSuccessor : ¬ Fin 2 ⊨ everyHasSuccessor strictRel := by
  simp only [Sentence.Realize, Formula.Realize, everyHasSuccessor,
    BoundedFormula.realize_all, BoundedFormula.realize_ex]
  change ¬ ∀ x : Fin 2, ∃ y : Fin 2, x < y
  intro h
  obtain ⟨x, hx⟩ := h 1
  have hx' := x.isLt
  change 1 < x.val at hx
  omega

theorem nat_capturedSelfRelation_false (a : ℕ → ℕ) :
    ¬ (capturedSelfRelation strictRel).Realize a := by
  simp only [capturedSelfRelation, Formula.Realize, BoundedFormula.realize_ex]
  change ¬ ∃ x : ℕ, x < x
  simp

theorem two_capturedSelfRelation_false (a : ℕ → Fin 2) :
    ¬ (capturedSelfRelation strictRel).Realize a := by
  simp only [capturedSelfRelation, Formula.Realize, BoundedFormula.realize_ex]
  change ¬ ∃ x : Fin 2, x < x
  simp

theorem doubleUnary_realize {L : Language} {M : Type*} [L.Structure M]
    (s : L.Functions 1) (a : ℕ → M) :
    (s.apply₁ (s.apply₁ (.var 0 : L.Term ℕ))).realize a =
      Structure.funMap s ![Structure.funMap s ![a 0] ] := by
  simp

theorem empty_existsSelfEqual_false : ¬ Empty ⊨ existsSelfEqual Language.empty := by
  rw [existsSelfEqual_realize]
  exact not_nonempty_iff.mpr inferInstance

theorem empty_allSelfEqual_true : Empty ⊨ allSelfEqual Language.empty := by
  exact allSelfEqual_realize

end Lemmatheca.Entry.FirstOrderStructures
