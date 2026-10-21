import Lemmatheca.PaProofCheckers.PAProofPredicateEquivalence
import Lemmatheca.BoundedArithmeticProofs.PAExtendedBoundedProofs
import Lemmatheca.PaComputations.PAComputationsSentences

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The parameter-free graph-based box is provably equivalent to the ordinary
box. The graph's existential output witness need not disappear by syntax. -/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open PAComputations ProofPrograms.FixedSyntaxPrograms
noncomputable section

/-- Universal internal equivalence of arbitrary unary arithmetic formulas
specializes to the actual numeral for any sentence code. -/
theorem unary_comparison_instance (P R : language.Formula Unit)
    (h : PAEquivalent P R) (A : language.Sentence) :
    Derives PA ((numeralInstance P (fun _ =>
      CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A)).iff
      (numeralInstance R (fun _ =>
        CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [Sentence.realize_iff, realize_numeralInstance, realize_numeralInstance]
  exact Formula.realize_iff.mp ((realize_allClose _).mp (pa_sound h M)
    (fun _ => numeralValue M
      (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A)))

/-- The same general internal comparison identifies the consistency formulas
obtained by negating the two predicates at the actual code of falsum. -/
theorem unary_comparison_consistency (P R : language.Formula Unit)
    (h : PAEquivalent P R) :
    Derives PA (((numeralInstance P (fun _ =>
      CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature ⊥)).not).iff
      ((numeralInstance R (fun _ =>
        CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature ⊥)).not)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  have hh := pa_sound (unary_comparison_instance P R h ⊥) M
  simpa only [Sentence.Realize, Formula.realize_iff, Formula.realize_not] using
    not_congr (Formula.realize_iff.mp hh)

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
