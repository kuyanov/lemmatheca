import Lemmatheca.MathematicalLogic.QuantifierElimination
import Lemmatheca.MathematicalLogic.QuantifierEliminationShared
import Mathlib.Tactic.FinCases

/-! Particular equality and discrete-order examples for quantifier elimination. -/

namespace Lemmatheca.Entry.QuantifierElimination

open Lemmatheca.MathematicalLogic.QuantifierElimination
open Formula

universe u

theorem equality_examples {M : Type u} [Infinite M] (y z : M) :
    (∃ x, x ≠ y ∧ x ≠ z) ∧ ((∃ x, x = y ∧ x ≠ z) ↔ y ≠ z) := by
  classical
  constructor
  · obtain ⟨x, hx⟩ := (insert y ({z} : Finset M)).exists_notMem
    exact ⟨x, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx⟩
  · exact equality_witness_substitution y (fun x => x ≠ z)

theorem finite_equality_obstruction : ¬∃ x : Fin 2, x ≠ 0 ∧ x ≠ 1 := by decide

theorem order_examples {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] (a b c d : M) :
    ((∃ x, a < x ∧ x < b ∧ c < d) ↔ a < b ∧ c < d) ∧
      ((∃ x, a < x ∧ x < b ∧ x = c) ↔ a < c ∧ c < b) := by
  constructor
  · constructor
    · rintro ⟨x, hax, hxb, hcd⟩
      exact ⟨hax.trans hxb, hcd⟩
    · rintro ⟨hab, hcd⟩
      obtain ⟨x, hax, hxb⟩ := exists_between hab
      exact ⟨x, hax, hxb, hcd⟩
  · simp

def betweenFormula : Formula true 2 :=
  (Formula.conj
    (.atom (.inr ((), 0, 2)))
    (.atom (.inr ((), 2, 1))) : Formula true 3).ex

theorem betweenFormula_realize {M : Type u} [LT M] (a b : M) :
    betweenFormula.Realize (fun x y : M => x < y) ![a, b] ↔ ∃ x, a < x ∧ x < b := by
  change (∃ x, (Formula.conj _ _).Realize _ (Fin.snoc ![a, b] x)) ↔ _
  simp [Formula.realize_conj, Formula.Realize, realizeAtom]

theorem integer_pairs_same_pattern :
    Similar (o := true) (fun a b : ℤ => a < b) (fun a b : ℤ => a < b)
      ![0, 1] ![0, 2] := by
  rintro (⟨i, j⟩ | ⟨_, i, j⟩) <;>
    fin_cases i <;> fin_cases j <;> norm_num [realizeAtom]

theorem integer_between_disagrees :
    ¬betweenFormula.Realize (fun a b : ℤ => a < b) ![0, 1] ∧
      betweenFormula.Realize (fun a b : ℤ => a < b) ![0, 2] := by
  rw [betweenFormula_realize, betweenFormula_realize]
  constructor
  · rintro ⟨x, hx, hx'⟩
    omega
  · exact ⟨1, by norm_num, by norm_num⟩

theorem integer_between_no_quantifier_free_equivalent :
    ¬∃ ψ : Formula true 2, ψ.IsQF ∧
      ∀ a : Fin 2 → ℤ, betweenFormula.Realize (fun x y => x < y) a ↔
        ψ.Realize (fun x y => x < y) a := by
  rintro ⟨ψ, hψ, h⟩
  have hψ01 : ¬ψ.Realize (fun x y : ℤ => x < y) ![0, 1] :=
    fun hx => integer_between_disagrees.1 ((h _).mpr hx)
  have hψ02 : ψ.Realize (fun x y : ℤ => x < y) ![0, 2] :=
    (h _).mp integer_between_disagrees.2
  exact hψ01 ((qf_pattern_invariance hψ integer_pairs_same_pattern).mpr hψ02)

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

def sharedBetweenFormula : binaryRelLanguage.BoundedFormula Empty 2 :=
  Shared.toShared betweenFormula

theorem integer_pairs_same_shared_atomic_formulas :
    let : binaryRelLanguage.Structure ℤ := binaryRelStructure ℤ (fun a b => a < b)
    ∀ φ : binaryRelLanguage.BoundedFormula Empty 2, φ.IsAtomic →
      (φ.Realize Empty.elim (![0, 1] : Fin 2 → ℤ) ↔ φ.Realize Empty.elim (![0, 2] : Fin 2 → ℤ)) := by
  let : binaryRelLanguage.Structure ℤ := binaryRelStructure ℤ (fun a b => a < b)
  dsimp only
  intro φ hφ
  have hs := integer_pairs_same_pattern
  change Similar (o := true) (Shared.relation (o := true) (M := ℤ))
    (Shared.relation (o := true) (M := ℤ)) (![0, 1] : Fin 2 → ℤ) (![0, 2] : Fin 2 → ℤ) at hs
  exact Shared.qf_transport (o := true) hφ.isQF hs

theorem integer_between_disagrees_shared :
    let : binaryRelLanguage.Structure ℤ := binaryRelStructure ℤ (fun a b => a < b)
    ¬sharedBetweenFormula.Realize Empty.elim (![0, 1] : Fin 2 → ℤ) ∧
      sharedBetweenFormula.Realize Empty.elim (![0, 2] : Fin 2 → ℤ) ∧
        ((0 : ℤ) < 1 ∧ (1 : ℤ) < 2) := by
  let : binaryRelLanguage.Structure ℤ := binaryRelStructure ℤ (fun a b => a < b)
  have h (a : Fin 2 → ℤ) : sharedBetweenFormula.Realize Empty.elim a ↔
      betweenFormula.Realize (fun x y : ℤ => x < y) a :=
    Shared.toShared_realize (o := true) betweenFormula a
  have hbetween : ¬sharedBetweenFormula.Realize Empty.elim (![0, 1] : Fin 2 → ℤ) ∧
      sharedBetweenFormula.Realize Empty.elim (![0, 2] : Fin 2 → ℤ) := by
    simpa only [h] using integer_between_disagrees
  exact ⟨hbetween.1, hbetween.2, by norm_num⟩

theorem integer_between_no_shared_quantifier_free_equivalent :
    let : binaryRelLanguage.Structure ℤ := binaryRelStructure ℤ (fun a b => a < b)
    ¬∃ ψ : binaryRelLanguage.BoundedFormula Empty 2, ψ.IsQF ∧
      ∀ a : Fin 2 → ℤ, sharedBetweenFormula.Realize Empty.elim a ↔
        ψ.Realize Empty.elim a := by
  let : binaryRelLanguage.Structure ℤ := binaryRelStructure ℤ (fun a b => a < b)
  dsimp only
  rintro ⟨ψ, hψ, he⟩
  apply integer_between_no_quantifier_free_equivalent
  refine ⟨Shared.fromShared (o := true) ψ, Shared.fromShared_isQF hψ, ?_⟩
  intro a
  have hb : sharedBetweenFormula.Realize Empty.elim a ↔
      betweenFormula.Realize (fun x y : ℤ => x < y) a :=
    Shared.toShared_realize (o := true) betweenFormula a
  exact hb.symm.trans ((he a).trans (Shared.fromStrict_realize ψ a).symm)

end Lemmatheca.Entry.QuantifierElimination
