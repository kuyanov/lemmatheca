import Lemmatheca.ArithmeticProofPredicates.ArithmeticProofPredicates
import Lemmatheca.BoundedArithmeticProofs.PAExtendedBoundedProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Formalized completeness for the full bounded grammar and the chosen PA predicate. -/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open PAComputations ProofPrograms ProofPrograms.SyntaxPrograms ProofPrograms.FixedSyntaxPrograms
open ProofPrograms.CheckerPrograms
noncomputable section

theorem parameterized_box_value {r : ℕ} (A : language.Formula (Fin r))
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin r → M) :
    (boxWithGraph proofFormula (substitutionGraph A)).Realize x ↔
      ∃ p : M, Certified axiomVerifier p ((substitution A).value x) := by
  rw [realize_boxWithGraph]
  constructor
  · rintro ⟨a, ha, p, hp⟩
    change (substitution A).sigmaGraph.Realize (extend x a) at ha
    have he := (program_sigma_value (substitution A) M x a).mp ha
    subst a
    exact ⟨p, (realize_proofFormula_value M _ _).mp hp⟩
  · rintro ⟨p, hp⟩
    refine ⟨(substitution A).value x, ?_, p, (realize_proofFormula_value M _ _).mpr hp⟩
    exact (program_sigma_value (substitution A) M x _).mpr rfl

/-- Internal quotation respects a proved equivalence, via actual specialization
and implication-elimination certificates. Standard agreement alone is not used. -/
theorem parameterized_completeness_transfer {r : ℕ} (A B : language.Formula (Fin r))
    (heq : ModelEquivalent A B)
    (hA : ParameterizedCompleteness proofFormula A (substitutionGraph A)) :
    ParameterizedCompleteness proofFormula B (substitutionGraph B) := by
  have himp : Derives PA (close (A.imp B)) := by
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [realize_close]
    intro x
    exact Formula.realize_imp.mpr (heq M x).mp
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  apply Formula.realize_imp.mpr
  intro hB
  have hs := (realize_close M _).mp (pa_sound hA M) x
  have hb := Formula.realize_imp.mp hs ((heq M x).mpr hB)
  obtain ⟨p, hp⟩ := (parameterized_box_value A M x).mp hb
  have hf := certified_specializeFixed (A.imp B) himp x
  rw [substitution_imp_value] at hf
  have hc := certified_modusPonens axiomVerifier _ _ _ _ hf hp (substitution_pure B x).sentence
  exact (parameterized_box_value B M x).mpr ⟨_, hc⟩

/-- Formalized completeness covers the full bounded grammar, including literal
strict quantified matrices, and quotes the original existential formula. -/
theorem formalized_completeness_full {r k : ℕ}
    (D : language.Formula (Fin r ⊕ Fin k)) (hD : BoundedArithmetic D) :
    ParameterizedCompleteness proofFormula (D.iExs (Fin k))
      (substitutionGraph (D.iExs (Fin k))) := by
  apply parameterized_completeness_transfer (hD.normalForm.iExs (Fin k))
    (D.iExs (Fin k))
  · intro M _ _ x
    simp only [Formula.realize_iExs]
    exact exists_congr fun y => (hD.normalForm_realize M (Sum.elim x y)).symm
  · exact formalized_completeness hD.normalForm hD.normalForm_deltaZero

abbrev FullSigmaOneSentence (A : language.Sentence) : Prop := BoundedSigmaOne A

theorem closed_formalized_completeness_full (A : language.Sentence)
    (hA : FullSigmaOneSentence A) : Derives PA (A.imp (box A)) := by
  obtain ⟨k, D, hD, rfl⟩ := hA
  let B := D.iExs (Fin k)
  let C := hD.normalForm.iExs (Fin k)
  have hC : SigmaOneSentence C := ⟨k, _, hD.normalForm_deltaZero, rfl⟩
  have heq : ∀ (M : Type) [language.Structure M] [Nonempty M] [M ⊨ PA],
      (M ⊨ B ↔ M ⊨ C) := by
    intro M _ _ _
    simp only [B, C, Sentence.Realize, Formula.realize_iExs]
    exact exists_congr fun y => hD.normalForm_realize M (Sum.elim default y)
  have himp : Derives PA (C.imp B) := by
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [Sentence.realize_imp]
    exact (heq M).mpr
  have hbox := derivability_one (C.imp B) himp
  have hmp := derivability_two C B
  have hcomplete := closed_formalized_completeness C hC
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [Sentence.realize_imp]
  intro hb
  have hc := pa_sound hcomplete M
  rw [Sentence.realize_imp] at hc
  have hd := pa_sound hmp M
  rw [Sentence.realize_imp, Sentence.realize_imp] at hd
  exact hd (pa_sound hbox M) (hc ((heq M).mp hb))

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
