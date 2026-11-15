import Lemmatheca.HeytingArithmeticOrder.Closure

namespace Lemmatheca.Entry.HeytingArithmeticOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.HeytingArithmetic
open Lemmatheca.ProofTheory.HeytingArithmetic.Order
open TheoryCertificate
universe u
variable {α : Type u}
noncomputable section
local instance haoExamplesEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _

/-- Two applications of the exact initial-segment split, at arbitrary terms. -/
def twoSuccessorBound {Γ : Context α} (s t : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula s (succTerm (succTerm t)))
      (.disj (ltFormula s t) (.disj (termEqual s t) (termEqual s (succTerm t))))) := by
  apply conjIntro
  · apply impIntro
    apply disjElim (impElim (conjLeft (ltSuccSplit s (succTerm t))) (assumption (by simp)))
    · apply disjElim (impElim (conjLeft (ltSuccSplit s t)) (assumption (by simp)))
      · exact disjLeft (assumption (by simp))
      · exact disjRight (disjLeft (assumption (by simp)))
    · exact disjRight (disjRight (assumption (by simp)))
  · apply impIntro
    apply disjElim (assumption (A := .disj (ltFormula s t) (.disj (termEqual s t) (termEqual s (succTerm t)))) (by simp))
    · exact impElim (conjRight (ltSuccSplit s (succTerm t)))
        (disjLeft (impElim (conjRight (ltSuccSplit s t)) (disjLeft (assumption (by simp)))))
    · apply disjElim (assumption (A := .disj (termEqual s t) (termEqual s (succTerm t))) (by simp))
      · exact impElim (conjRight (ltSuccSplit s (succTerm t)))
          (disjLeft (impElim (conjRight (ltSuccSplit s t)) (disjRight (assumption (by simp)))))
      · exact impElim (conjRight (ltSuccSplit s (succTerm t))) (disjRight (assumption (by simp)))

/-- The equal-zero instance refutes a comparison with only strict alternatives. -/
def equalEndpointCounterexample : Certificate false (∅ : Context Empty)
    (.neg (.disj (ltFormula zeroTerm zeroTerm) (ltFormula zeroTerm zeroTerm))) := by
  apply negIntro
  apply disjElim (assumption (A := .disj (ltFormula zeroTerm zeroTerm) (ltFormula zeroTerm zeroTerm)) (by simp))
  · exact negElim (assumption (by simp)) (ltIrrefl zeroTerm)
  · exact negElim (assumption (by simp)) (ltIrrefl zeroTerm)

end
end Lemmatheca.Entry.HeytingArithmeticOrder
