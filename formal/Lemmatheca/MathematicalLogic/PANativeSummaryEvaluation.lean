import Lemmatheca.MathematicalLogic.PANativeSyntaxEvalHelpers

namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
open Lemmatheca.MathematicalLogic
noncomputable section

theorem projection_eval {n : ℕ} (i : Fin n) (x : Fin n → ℕ) :
    (Program.proj i).eval x = x i := rfl

theorem coordinate0 (s : CodingFormalProofs.Stats) : coordinate 0 s = s.1 := rfl
theorem coordinate1 (s : CodingFormalProofs.Stats) : coordinate 1 s = s.2.1 := rfl
theorem coordinate2 (s : CodingFormalProofs.Stats) : coordinate 2 s = s.2.2.1 := rfl
theorem coordinate3 (s : CodingFormalProofs.Stats) : coordinate 3 s = s.2.2.2 := rfl

set_option maxHeartbeats 1600000 in
set_option backward.dsimp.instances true in
theorem summaryStep_eval (x : Fin 2 → ℕ) :
    summaryStep.eval x = CodingFormalProofs.summaryStep CodingFormalProofs.arithmeticSignature
      (x 0) (x 1) := by
  by_cases he : x 0 = 0
  · change (ternary select (.proj 0) _ (constant 0)).eval x = _
    rw [ternary_eval, select_eval]
    change (if x 0 = 0 then 0 else _) = _
    rw [ite_eq_left he]
    simp [CodingFormalProofs.summaryStep, he, Encodable.encode_prod_val, Encodable.encode_nat,
      Nat.pair]
  · rcases ht : CodingFormalProofs.tag (x 0) with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
      cases ha : CodingFormalProofs.args (x 0) <;>
      simp only [summaryStep, ternary_eval, binary_eval, unary_eval, projection_eval,
        select_eval_values, equalTest_eval_values, tag_eval, args_eval, listLength_eval, head_eval,
        multiplication_eval, sign_eval_values, predecessor_eval, addition_eval, maximum_eval,
        functionTest_eval_values, foldSummary_max_eval, goodTerm_eval, goodForm_eval,
        quad_eval, constant_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
        CodingFormalProofs.summaryStep, CodingFormalProofs.arg,
        FiniteSequenceCoding.length, FiniteSequenceCoding.decode_code,
        FiniteSequenceCoding.head_code, coordinate0, coordinate1, coordinate2, coordinate3, he, ht, flag_mul, flag_eq_zero, ite_not,
        ha, List.length_nil, List.length_cons, List.headD_nil, List.headD_cons,
        List.getElem?_nil, List.getElem?_cons_zero, Option.getD_none, Option.getD_some,
        arithmetic_relation_false] <;>
        (try rw [encode_conditional]) <;>
        simp [Encodable.encode_prod_val, Encodable.encode_nat,
          pair_zero_zero, Nat.pos_iff_ne_zero] <;>
        (rw [encode_conditional]; rfl)


end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
