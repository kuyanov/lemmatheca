import Lemmatheca.MathematicalLogic.PANumeralArithmeticProofs

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem compFour_model_value {r : ℕ} (p : Program 4) (a b c d : Program r) (x : Fin r → M) :
    (Program.comp p ![a, b, c, d]).value x = p.value ![a.value x, b.value x, c.value x, d.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> simp

theorem certified_multiplicationStep (m n p : M)
    (hp : Certified axiomVerifier p
      (modelNode 4 [multiplicationSyntax (numeralSyntax m) (numeralSyntax n),
        numeralSyntax (mulValue M m n)])) :
    Certified axiomVerifier (multiplicationStep.value ![m, n, p])
      (modelNode 4 [multiplicationSyntax (numeralSyntax m) (numeralSyntax (succValue M n)),
        numeralSyntax (mulValue M m (succValue M n))]) := by
  let a := numeralSyntax m
  let b := numeralSyntax n
  let c := numeralSyntax (mulValue M m n)
  let ax : Program 3 := specializeOne (specializeOne (constant qMulSuccProof) (num (.proj 0))) (num (.proj 1))
  have hax := certified_mulSucc (num (.proj 0)) (num (.proj 1)) ![m, n, p]
    (num_pure _ _) (num_pure _ _)
  simp only [num_model_value, Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one] at hax
  have ha : PureTerm a := PureTerm.numeral m
  have hb : PureTerm b := PureTerm.numeral n
  have hc : PureTerm c := PureTerm.numeral _
  have hab : PureTerm (multiplicationSyntax a b) := PureTerm.binary 3 (Or.inr rfl) ha hb
  have hcong := certified_binaryCongruence axiomVerifier 2 (Or.inl rfl) true p
    (multiplicationSyntax a b) c a hp hab hc ha
  simp only [binaryFrame_value, ↓reduceIte] at hcong
  have htrans := certified_transitivity axiomVerifier (ax.value ![m, n, p])
    ((parametricCongruence addLeftFrame).value ![p, multiplicationSyntax a b, c, a])
    (multiplicationSyntax a (successorSyntax b)) (additionSyntax (multiplicationSyntax a b) a)
    (additionSyntax c a) hax hcong (PureTerm.binary 3 (Or.inr rfl) ha hb.succ)
    (PureTerm.binary 2 (Or.inl rfl) hab ha) (PureTerm.binary 2 (Or.inl rfl) hc ha)
  have hadd := certified_additionBuilder (mulValue M m n) m
  have hfinal := certified_transitivity axiomVerifier
    (transitivity.value ![ax.value ![m, n, p],
      (parametricCongruence addLeftFrame).value ![p, multiplicationSyntax a b, c, a],
      multiplicationSyntax a (successorSyntax b), additionSyntax (multiplicationSyntax a b) a,
      additionSyntax c a])
    (additionBuilder.value ![mulValue M m n, m])
    (multiplicationSyntax a (successorSyntax b)) (additionSyntax c a)
    (numeralSyntax (addValue M (mulValue M m n) m)) htrans hadd
    (PureTerm.binary 3 (Or.inr rfl) ha hb.succ) (PureTerm.binary 2 (Or.inl rfl) hc ha)
    (PureTerm.numeral _)
  simpa only [multiplicationStep, composeEquality_model_value, compFour_model_value,
    num_model_value, mulCode_model_value, addCode_model_value, succCode_model_value,
    binary_value, addition_value, multiplication_value, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, numeralSyntax_succ, mul_successor_value, a, b, c, ax] using hfinal

theorem multiplicationBuilder_zero_value (m : M) :
    multiplicationBuilder.value ![m, zeroValue M] = multiplicationBase.value ![m] := by
  have h := Program.value_rec_zero multiplicationBase multiplicationStep ![m]
  have hx : Fin.snoc (![m] : Fin 1 → M) (zeroValue M) = ![m, zeroValue M] := by
    funext i
    fin_cases i <;> rfl
  simpa only [multiplicationBuilder, hx] using h

theorem multiplicationBuilder_succ_value (m n : M) :
    multiplicationBuilder.value ![m, succValue M n] =
      multiplicationStep.value ![m, n, multiplicationBuilder.value ![m, n] ] := by
  have h := Program.value_rec_succ multiplicationBase multiplicationStep ![m] n
  have hx (n : M) : Fin.snoc (![m] : Fin 1 → M) n = ![m, n] := by
    funext i
    fin_cases i <;> rfl
  have hy (n p : M) : Fin.snoc (![m, n] : Fin 2 → M) p = ![m, n, p] := by
    funext i
    fin_cases i <;> rfl
  simpa only [multiplicationBuilder, hx, hy] using h

theorem certified_multiplicationBuilder (m n : M) :
    Certified axiomVerifier (multiplicationBuilder.value ![m, n])
      (modelNode 4 [multiplicationSyntax (numeralSyntax m) (numeralSyntax n),
        numeralSyntax (mulValue M m n)]) := by
  apply definable_induction (fun n => Certified axiomVerifier (multiplicationBuilder.value ![m, n])
    (modelNode 4 [multiplicationSyntax (numeralSyntax m) (numeralSyntax n),
      numeralSyntax (mulValue M m n)]))
  · change DPred (fun v : Fin 1 → M => Certified axiomVerifier (multiplicationBuilder.value ![m, v 0])
      (modelNode 4 [multiplicationSyntax (numeralSyntax m) (numeralSyntax (v 0)),
        numeralSyntax (mulValue M m (v 0))]))
    unfold Certified multiplicationSyntax numeralSyntax modelNode modelList
    simp only [List.foldr_cons, List.foldr_nil]
    pa_definable
  · rw [multiplicationBuilder_zero_value, mul_zero_value]
    exact certified_multiplicationBase m
  · intro k hk
    rw [multiplicationBuilder_succ_value]
    exact certified_multiplicationStep m k _ hk

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
