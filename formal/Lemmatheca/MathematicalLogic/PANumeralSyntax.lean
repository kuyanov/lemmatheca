import Lemmatheca.MathematicalLogic.PANativeSyntaxRecurrences

/-! Formation of numeral syntax at arbitrary internal values of a PA model. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem numeral_zero_modelNode_value :
    ProofPrograms.numeral.value ![zeroValue M] = modelNode 2 [zeroValue M] := by
  have hz := Program.value_rec_zero (syntaxNode 2 [constant 0] : Program 0)
    (syntaxNode 2 [constant 1, Program.proj (1 : Fin 2)]) (Fin.elim0 : Fin 0 → M)
  have hx : Fin.snoc (Fin.elim0 : Fin 0 → M) (zeroValue M) = ![zeroValue M] := by
    funext i
    fin_cases i
    rfl
  rw [hx] at hz
  simpa only [ProofPrograms.numeral, syntaxNode_value, list_cons_value, list_nil_value,
    constant_value, numeral_value_zero, modelNode, modelList, List.foldr_cons,
    List.foldr_nil] using hz

theorem numeral_successor_modelNode_value (n : M) :
    ProofPrograms.numeral.value ![succValue M n] =
      modelNode 2 [numeralValue M 1, ProofPrograms.numeral.value ![n] ] :=
  numeral_successor_value n

theorem numeral_stats_value (n : M) :
    stats.value ![ProofPrograms.numeral.value ![n] ] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (zeroValue M) := by
  let := modelLinearOrder M
  apply definable_induction
    (fun n => stats.value ![ProofPrograms.numeral.value ![n] ] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (zeroValue M))
  · change DPred (fun v : Fin 1 → M => stats.value ![ProofPrograms.numeral.value ![v 0] ] =
      modelSummary (numeralValue M 1) (zeroValue M) (zeroValue M) (zeroValue M))
    pa_definable
  · rw [numeral_zero_modelNode_value]
    simpa only [numeral_value_zero] using stats_zero_modelNode_value (M := M)
  · intro k hk
    have hc (i : Fin 4) : statsPart i (ProofPrograms.numeral.value ![k]) =
        ![numeralValue M 1, zeroValue M, zeroValue M, zeroValue M] i := by
      simp only [statsPart, hk, modelSummary_part_value]
    have hc0 : statsPart 0 (ProofPrograms.numeral.value ![k]) = numeralValue M 1 := hc 0
    have hc2 : statsPart 2 (ProofPrograms.numeral.value ![k]) = zeroValue M := hc 2
    have hc3 : statsPart 3 (ProofPrograms.numeral.value ![k]) = zeroValue M := hc 3
    rw [numeral_successor_modelNode_value, stats_succ_modelNode_value]
    simp only [hc0, hc2, hc3, numeral_eq_zero_iff_model, Nat.one_ne_zero,
      ↓reduceIte, maximum_value, max_self]

theorem numeral_wellformed (n : M) :
    isTerm.value ![zeroValue M, ProofPrograms.numeral.value ![n] ] = numeralValue M 1 := by
  apply (isTerm_closed_iff _).mpr
  simp only [termDepth, numeral_stats_value, modelSummary_part_value]
  rfl

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.SyntaxPrograms
