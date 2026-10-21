import Lemmatheca.PaListsAndSyntax.PANativeSyntaxEvalHelpers

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Standard evaluation of the explicit course-of-values syntax rewrite. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
open Lemmatheca.MathematicalLogic
noncomputable section

private theorem projection_eval {n : ℕ} (i : Fin n) (x : Fin n → ℕ) :
    (Program.proj i).eval x = x i := rfl

private theorem disjoin_flag_values (P Q : Prop) [Decidable P] [Decidable Q] :
    disjoin.eval ![flag P, flag Q] = flag (P ∨ Q) := by
  rw [disjoin_eval]
  by_cases hp : P <;> by_cases hq : Q <;> simp [flag, hp, hq]

set_option maxHeartbeats 1600000 in
set_option backward.dsimp.instances true in
theorem rewriteStep_eval (x : Fin 5 → ℕ) :
    rewriteStep.eval x = CodingFormalProofs.rewriteStep
      (x 0) (x 1) (x 2) (x 3) (x 4) := by
  by_cases he : x 3 = 0
  · change (ternary select (.proj 3) _ (constant 0)).eval x = _
    rw [ternary_eval, select_eval]
    change (if x 3 = 0 then 0 else _) = _
    rw [ite_eq_left he]
    simp only [CodingFormalProofs.rewriteStep, he, ↓reduceIte]
  · rcases ht : CodingFormalProofs.tag (x 3) with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;>
      cases ha : CodingFormalProofs.args (x 3) <;>
      simp only [rewriteStep, ternary_eval, binary_eval, unary_eval, projection_eval,
        select_eval_values, equalTest_eval_values, disjoin_flag_values,
        multiplication_eval, flag_mul, flag_eq_zero, ite_not, constant_eval,
        tag_eval, args_eval, head_eval, tail_eval, listMap_eval, listEntry_eval,
        listCons_eval, predecessor_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
        FiniteSequenceCoding.decode_code, FiniteSequenceCoding.head_code,
        FiniteSequenceCoding.tail_code, CodingFormalProofs.rewriteStep,
        CodingFormalProofs.arg, ha, he, ht, List.headD_nil, List.headD_cons,
        List.getElem?_nil, List.getElem?_cons_zero, Option.getD_none, Option.getD_some] <;>
      simp [CodingFormalProofs.node, CodingFormalProofs.boundName, FiniteSequenceCoding.cons, Nat.add_comm] <;>
      (split_ifs <;> simp_all [Nat.add_comm])

theorem rewrite_eval (x : Fin 4 → ℕ) :
    rewrite.eval x = CodingFormalProofs.rewrite (x 0) (x 1) (x 2) (x 3) := by
  let p : Fin 3 → ℕ := ![x 0, x 1, x 2]
  have hx : Fin.snoc p (x 3) = x := by
    funext i
    fin_cases i <;> rfl
  have hs : (fun i hist => rewriteStep.eval (Fin.snoc (Fin.snoc p i) hist)) =
      CodingFormalProofs.rewriteStep (x 0) (x 1) (x 2) := by
    funext i hist
    rw [rewriteStep_eval]
    rfl
  have h := courseValue_eval rewriteStep p (x 3)
  rw [hx, hs] at h
  exact h

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.SyntaxPrograms
