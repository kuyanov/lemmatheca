import Lemmatheca.MathematicalLogic.PANumericalOrder

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms LogicalProofs
noncomputable section

def disequalityImplication (reverse : Bool) : language.Formula (Fin 2) :=
  (leFormula (.var 0) (.var 1)).not.imp
    (if reverse then ((Term.var 1).equal (.var 0)).not else ((Term.var 0).equal (.var 1)).not)

theorem disequalityImplication_derives (reverse : Bool) :
    Derives PA (close (disequalityImplication reverse)) := by
  cases reverse <;>
    apply HenkinCompleteness.deductive_completeness <;>
    apply Theory.models_sentence_iff.mpr <;> intro M <;> rw [realize_close] <;> intro v
  all_goals
    simp only [disequalityImplication, Bool.false_eq_true, ↓reduceIte,
      Formula.realize_imp, Formula.realize_not, realize_leFormula, Formula.realize_equal,
      Term.realize_var]
    intro hnot heq
    apply hnot
    simpa only [heq] using le_refl_value (v 0)

def disequalityConclusion {r : ℕ} (reverse : Bool) (a b : Program r) : Program r :=
  negCode (if reverse then equalCode b a else equalCode a b)

def disequalityBranch (reverse : Bool) : Program 2 :=
  ternary modusPonensCertificate
    (instanceTwo (disequalityImplication reverse) (disequalityImplication_derives reverse)
      (num (.proj 0)) (num (.proj 1)))
    numeralNotLeBuilder
    (disequalityConclusion reverse (num (.proj 0)) (num (.proj 1)))

def numeralNotEqualBuilder : Program 2 :=
  ternary select (binary leq (.proj 0) (.proj 1))
    (.comp (disequalityBranch true) ![.proj 1, .proj 0]) (disequalityBranch false)

def numeralEqualBuilder : Program 2 := unary equalityReflexivityCertificate (num (.proj 0))

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

def disequalityValue (reverse : Bool) (a b : M) : M :=
  if reverse then negValue (modelNode 4 [b, a]) else negValue (modelNode 4 [a, b])

theorem disequalityValue_pure (reverse : Bool) {a b : M} (ha : PureTerm a) (hb : PureTerm b) :
    PureFormula (disequalityValue reverse a b) := by
  cases reverse
  · exact pure_negation (PureFormula.equal ha hb)
  · exact pure_negation (PureFormula.equal hb ha)

theorem disequalityConclusion_value {r : ℕ} (reverse : Bool) (a b : Program r) (x : Fin r → M) :
    (disequalityConclusion reverse a b).value x = disequalityValue reverse (a.value x) (b.value x) := by
  cases reverse <;>
    simp only [disequalityConclusion, Bool.false_eq_true, ↓reduceIte,
      negCode_value, equalCode_value, disequalityValue]

theorem disequalityImplication_model (reverse : Bool) (a b : M) :
    modelFormulaCodeAt (![a, b] : Fin 2 → M) 0 (disequalityImplication reverse) =
      implication.value ![negValue (orderValue a b), disequalityValue reverse a b] := by
  cases reverse <;>
    simp only [disequalityImplication, Bool.false_eq_true, ↓reduceIte, modelFormulaCodeAt,
      disequalityValue]
  all_goals
    rw [modelFormulaCodeAt_le]
    simp only [modelFormulaCodeAt_equal, modelTermCode, Matrix.cons_val_zero, Matrix.cons_val_one,
      negValue, implication_node]

theorem certified_disequalityBranch (reverse : Bool) (m n : M) (hnot : ¬leValue M m n) :
    Certified axiomVerifier ((disequalityBranch reverse).value ![m, n])
      (disequalityValue reverse (numeralSyntax m) (numeralSyntax n)) := by
  have hfixed := certified_instanceTwo (disequalityImplication reverse)
    (disequalityImplication_derives reverse) (num (.proj 0)) (num (.proj 1)) ![m, n]
    (num_pure _ _) (num_pure _ _)
  simp only [num_model_value, Program.value_proj, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hfixed
  rw [disequalityImplication_model] at hfixed
  have hneg := certified_numeralNotLeBuilder m n hnot
  have hout := (disequalityValue_pure reverse (PureTerm.numeral m) (PureTerm.numeral n)).sentence
  have h := certified_modusPonens axiomVerifier _ _ _ _ hfixed hneg hout
  simpa only [disequalityBranch, ternary_value, disequalityConclusion_value, num_model_value,
    Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem certified_numeralNotEqualBuilder (m n : M) (hne : m ≠ n) :
    Certified axiomVerifier (numeralNotEqualBuilder.value ![m, n])
      (negValue (modelNode 4 [numeralSyntax m, numeralSyntax n])) := by
  classical
  have hv : numeralNotEqualBuilder.value ![m, n] =
      if leValue M m n then (disequalityBranch true).value ![n, m]
      else (disequalityBranch false).value ![m, n] := by
    simp only [numeralNotEqualBuilder, ternary_value, binary_value, Program.value_proj,
      Matrix.cons_val_zero, Matrix.cons_val_one, leq_value, Program.value_comp_two,
      select_value]
    by_cases hle : leValue M m n <;>
      simp only [hle, ↓reduceIte, numeral_eq_zero_iff_model, Nat.one_ne_zero]
  rw [hv]
  by_cases hle : leValue M m n
  · rw [ite_eq_left hle]
    have hnl : ¬leValue M n m := fun hnm => hne (le_antisymm_value hle hnm)
    exact certified_disequalityBranch true n m hnl
  · rw [ite_eq_right hle]
    exact certified_disequalityBranch false m n hle

theorem certified_numeralEqualBuilder (m n : M) (heq : m = n) :
    Certified axiomVerifier (numeralEqualBuilder.value ![m, n])
      (modelNode 4 [numeralSyntax m, numeralSyntax n]) := by
  subst n
  have hn : PureTerm (numeralSyntax m) := PureTerm.numeral m
  have h := certified_equalityReflexivity axiomVerifier (numeralSyntax m) hn.namedTerm
    (hn.equal_sentence hn)
  simpa only [numeralEqualBuilder, unary_value, num_model_value, Program.value_proj,
    Matrix.cons_val_zero] using h

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
