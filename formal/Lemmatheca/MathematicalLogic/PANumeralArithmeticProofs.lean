import Lemmatheca.MathematicalLogic.PANumericalAxiomInstances

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
variable {M : Type} [language.Structure M] [M ⊨ PA]

def addZeroFormula : language.Formula (Fin 1) :=
  (addTerm (.var 0) zeroTerm).equal (.var 0)
def addSuccFormula : language.Formula (Fin 2) :=
  (addTerm (.var 0) (succTerm (.var 1))).equal (succTerm (addTerm (.var 0) (.var 1)))
def mulZeroFormula : language.Formula (Fin 1) :=
  (mulTerm (.var 0) zeroTerm).equal zeroTerm
def mulSuccFormula : language.Formula (Fin 2) :=
  (mulTerm (.var 0) (succTerm (.var 1))).equal (addTerm (mulTerm (.var 0) (.var 1)) (.var 0))

theorem certified_addZero {r : ℕ} (s : Program r) (x : Fin r → M) (hs : PureTerm (s.value x)) :
    Certified axiomVerifier ((specializeOne (constant qAddZeroProof) s).value x)
      (modelNode 4 [additionSyntax (s.value x) zeroSyntax, s.value x]) := by
  have hA : Derives PA (close addZeroFormula) := by
    change Derives PA qAddZero
    exact derives_assumption (Or.inl (by simp [Q]))
  have h := certified_instanceOne addZeroFormula hA s x hs
  change Certified axiomVerifier ((specializeOne (constant qAddZeroProof) s).value x)
    (modelNode 4 [additionSyntax (s.value x) (modelNode 2 [numeralValue M 0]), s.value x]) at h
  simpa only [numeral_value_zero, zeroSyntax] using h

theorem certified_mulZero {r : ℕ} (s : Program r) (x : Fin r → M) (hs : PureTerm (s.value x)) :
    Certified axiomVerifier ((specializeOne (constant qMulZeroProof) s).value x)
      (modelNode 4 [multiplicationSyntax (s.value x) zeroSyntax, zeroSyntax]) := by
  have hA : Derives PA (close mulZeroFormula) := by
    change Derives PA qMulZero
    exact derives_assumption (Or.inl (by simp [Q]))
  have h := certified_instanceOne mulZeroFormula hA s x hs
  change Certified axiomVerifier ((specializeOne (constant qMulZeroProof) s).value x)
    (modelNode 4 [multiplicationSyntax (s.value x) (modelNode 2 [numeralValue M 0]),
      modelNode 2 [numeralValue M 0] ]) at h
  simpa only [numeral_value_zero, zeroSyntax] using h

theorem certified_addSucc {r : ℕ} (s t : Program r) (x : Fin r → M)
    (hs : PureTerm (s.value x)) (ht : PureTerm (t.value x)) :
    Certified axiomVerifier
      ((specializeOne (specializeOne (constant qAddSuccProof) s) t).value x)
      (modelNode 4 [additionSyntax (s.value x) (successorSyntax (t.value x)),
        successorSyntax (additionSyntax (s.value x) (t.value x))]) := by
  have hA : Derives PA (close addSuccFormula) := by
    change Derives PA qAddSucc
    exact derives_assumption (Or.inl (by simp [Q]))
  exact certified_instanceTwo addSuccFormula hA s t x hs ht

theorem certified_mulSucc {r : ℕ} (s t : Program r) (x : Fin r → M)
    (hs : PureTerm (s.value x)) (ht : PureTerm (t.value x)) :
    Certified axiomVerifier
      ((specializeOne (specializeOne (constant qMulSuccProof) s) t).value x)
      (modelNode 4 [multiplicationSyntax (s.value x) (successorSyntax (t.value x)),
        additionSyntax (multiplicationSyntax (s.value x) (t.value x)) (s.value x)]) := by
  have hA : Derives PA (close mulSuccFormula) := by
    change Derives PA qMulSucc
    exact derives_assumption (Or.inl (by simp [Q]))
  exact certified_instanceTwo mulSuccFormula hA s t x hs ht

theorem composeEquality_model_value {r : ℕ} (p q a b c : Program r) (x : Fin r → M) :
    (composeEquality p q a b c).value x =
      transitivity.value ![p.value x, q.value x, a.value x, b.value x, c.value x] := by
  rw [composeEquality, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> simp

theorem numeralSyntax_zero : numeralSyntax (zeroValue M) = zeroSyntax (M := M) :=
  numeral_zero_modelNode_value

theorem numeralSyntax_succ (n : M) :
    numeralSyntax (succValue M n) = successorSyntax (numeralSyntax n) :=
  numeral_successor_modelNode_value n

theorem num_pure {r : ℕ} (p : Program r) (x : Fin r → M) : PureTerm ((num p).value x) := by
  rw [num_model_value]
  exact PureTerm.numeral _

theorem certified_additionBase (m : M) :
    Certified axiomVerifier (additionBase.value ![m])
      (modelNode 4 [additionSyntax (numeralSyntax m) (numeralSyntax (zeroValue M)), numeralSyntax m]) := by
  have h := certified_addZero (num (.proj 0)) ![m] (num_pure _ _)
  simpa only [additionBase, numeralSyntax_zero, num_model_value, Program.value_proj,
    Matrix.cons_val_zero] using h

theorem certified_multiplicationBase (m : M) :
    Certified axiomVerifier (multiplicationBase.value ![m])
      (modelNode 4 [multiplicationSyntax (numeralSyntax m) (numeralSyntax (zeroValue M)),
        numeralSyntax (zeroValue M)]) := by
  have h := certified_mulZero (num (.proj 0)) ![m] (num_pure _ _)
  simpa only [multiplicationBase, numeralSyntax_zero, num_model_value, Program.value_proj,
    Matrix.cons_val_zero] using h

theorem certified_additionStep (m n p : M)
    (hp : Certified axiomVerifier p
      (modelNode 4 [additionSyntax (numeralSyntax m) (numeralSyntax n),
        numeralSyntax (addValue M m n)])) :
    Certified axiomVerifier (additionStep.value ![m, n, p])
      (modelNode 4 [additionSyntax (numeralSyntax m) (numeralSyntax (succValue M n)),
        numeralSyntax (addValue M m (succValue M n))]) := by
  let a := numeralSyntax m
  let b := numeralSyntax n
  let c := numeralSyntax (addValue M m n)
  let ax : Program 3 := specializeOne (specializeOne (constant qAddSuccProof) (num (.proj 0))) (num (.proj 1))
  have hax := certified_addSucc (num (.proj 0)) (num (.proj 1)) ![m, n, p]
    (num_pure _ _) (num_pure _ _)
  simp only [num_model_value, Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one] at hax
  have ha : PureTerm a := PureTerm.numeral m
  have hb : PureTerm b := PureTerm.numeral n
  have hc : PureTerm c := PureTerm.numeral _
  have hab : PureTerm (additionSyntax a b) := PureTerm.binary 2 (Or.inl rfl) ha hb
  have hcong := certified_succCongruence axiomVerifier p (additionSyntax a b) c hp hab hc
  have htrans := certified_transitivity axiomVerifier (ax.value ![m, n, p])
    ((unaryCongruence succFrame).value ![p, additionSyntax a b, c])
    (additionSyntax a (successorSyntax b)) (successorSyntax (additionSyntax a b))
    (successorSyntax c) hax hcong (PureTerm.binary 2 (Or.inl rfl) ha hb.succ) hab.succ hc.succ
  simpa only [additionStep, composeEquality_model_value, Program.value_comp_three,
    num_model_value, addCode_model_value, succCode_model_value, binary_value,
    addition_value, Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    numeralSyntax_succ, add_successor_value, a, b, c, ax] using htrans

theorem additionBuilder_zero_value (m : M) :
    additionBuilder.value ![m, zeroValue M] = additionBase.value ![m] := by
  have h := Program.value_rec_zero additionBase additionStep ![m]
  have hx : Fin.snoc (![m] : Fin 1 → M) (zeroValue M) = ![m, zeroValue M] := by
    funext i
    fin_cases i <;> rfl
  simpa only [additionBuilder, hx] using h

theorem additionBuilder_succ_value (m n : M) :
    additionBuilder.value ![m, succValue M n] =
      additionStep.value ![m, n, additionBuilder.value ![m, n] ] := by
  have h := Program.value_rec_succ additionBase additionStep ![m] n
  have hx (n : M) : Fin.snoc (![m] : Fin 1 → M) n = ![m, n] := by
    funext i
    fin_cases i <;> rfl
  have hy (n p : M) : Fin.snoc (![m, n] : Fin 2 → M) p = ![m, n, p] := by
    funext i
    fin_cases i <;> rfl
  simpa only [additionBuilder, hx, hy] using h

theorem certified_additionBuilder (m n : M) :
    Certified axiomVerifier (additionBuilder.value ![m, n])
      (modelNode 4 [additionSyntax (numeralSyntax m) (numeralSyntax n),
        numeralSyntax (addValue M m n)]) := by
  apply definable_induction (fun n => Certified axiomVerifier (additionBuilder.value ![m, n])
    (modelNode 4 [additionSyntax (numeralSyntax m) (numeralSyntax n),
      numeralSyntax (addValue M m n)]))
  · change DPred (fun v : Fin 1 → M => Certified axiomVerifier (additionBuilder.value ![m, v 0])
      (modelNode 4 [additionSyntax (numeralSyntax m) (numeralSyntax (v 0)),
        numeralSyntax (addValue M m (v 0))]))
    unfold Certified additionSyntax numeralSyntax modelNode modelList
    simp only [List.foldr_cons, List.foldr_nil]
    pa_definable
  · rw [additionBuilder_zero_value, add_zero_value]
    exact certified_additionBase m
  · intro k hk
    rw [additionBuilder_succ_value]
    exact certified_additionStep m k _ hk

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
