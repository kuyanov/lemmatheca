import Lemmatheca.HeytingArithmeticAddition.Statements
import Lemmatheca.HeytingArithmetic.Computations

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Addition
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction (Derivation)
universe u
noncomputable section

/-- Count every node of the actual finite native arithmetic derivation tree. -/
def nodeCount : {α : Type u} → {Γ : Context α} → {A : Formula α} →
    Derivation false true LA Γ A → ℕ
  | _, _, _, .assumption _ => 1
  | _, _, _, .conjIntro p q => 1 + nodeCount p + nodeCount q
  | _, _, _, .conjElimLeft p => 1 + nodeCount p
  | _, _, _, .conjElimRight p => 1 + nodeCount p
  | _, _, _, .disjIntroLeft p => 1 + nodeCount p
  | _, _, _, .disjIntroRight p => 1 + nodeCount p
  | _, _, _, .disjElim p q r => 1 + nodeCount p + nodeCount q + nodeCount r
  | _, _, _, .impIntro p => 1 + nodeCount p
  | _, _, _, .impElim p q => 1 + nodeCount p + nodeCount q
  | _, _, _, .negIntro p => 1 + nodeCount p
  | _, _, _, .negElim p q => 1 + nodeCount p + nodeCount q
  | _, _, _, .falsumElim p => 1 + nodeCount p
  | _, _, _, .classicalContradiction _ p => 1 + nodeCount p
  | _, _, _, .allElim _ p => 1 + nodeCount p
  | _, _, _, .exIntro _ p => 1 + nodeCount p
  | _, _, _, .allIntro p => 1 + nodeCount p
  | _, _, _, .exElim p q => 1 + nodeCount p + nodeCount q
  | _, _, _, .equalIntro _ _ => 1
  | _, _, _, .equalElim _ _ _ _ p q => 1 + nodeCount p + nodeCount q

def certificateNodeCount {α : Type u} {Γ : Context α} {A : Formula α}
    (p : Certificate false Γ A) : ℕ := nodeCount p.derivation

def numeralEquation (n : ℕ) : Sentence :=
  termEqual (addTerm zeroTerm (numeral n)) (numeral n)

/-- Infinitely many distinct numeral conclusions do not fit into a finite premise collection. -/
theorem finite_omits_numeral_equation (S : Finset Sentence) :
    ∃ n : ℕ, numeralEquation n ∉ S := by
  classical
  have realizeNum (n : ℕ) (v : Empty → ℕ) : (numeral n).realize v = n := by
    have hv : v = Empty.elim := Subsingleton.elim _ _
    rw [hv]
    exact Lemmatheca.ModelTheory.ArithmeticTheories.numeral_value_nat n
  have hinj : Function.Injective numeralEquation := by
    intro m n h
    have ht := (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equal.inj h).2
    have hv := congrArg (fun t : LA.Term (Empty ⊕ Fin 0) =>
      t.realize (fun _ => (0 : ℕ))) ht
    simpa only [Term.realize_relabel, realizeNum] using hv
  by_contra! h
  have hsub : Set.range numeralEquation ⊆ (↑S : Set Sentence) := by
    rintro _ ⟨n, rfl⟩
    exact h n
  exact (Set.infinite_range_of_injective hinj) (S.finite_toSet.subset hsub)

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Addition
