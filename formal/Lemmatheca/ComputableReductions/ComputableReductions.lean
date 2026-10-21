import Mathlib.Computability.Reduce
import Lemmatheca.FirstIncompleteness.FirstIncompleteness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ProofTheory

/-! Effective translations, finite Robinson axioms, and Church's theorem for
the actual arithmetic language and the corpus's fixed sentence codes. -/
namespace Lemmatheca.ComputabilityTheory.ComputableReductions

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories FirstOrderProofs CodingFormalProofs FirstIncompleteness

noncomputable section

theorem enumerable_preimage {A B : ℕ → Prop} (h : A ≤₀ B) (hB : REPred B) :
    REPred A := by
  obtain ⟨f, hf, he⟩ := h
  exact (UniversalComputation.enumerable_preimage hB hf).of_eq fun x => (he x).symm

theorem complement_reduction {A B : ℕ → Prop} (h : A ≤₀ B) :
    (fun x => ¬ A x) ≤₀ (fun x => ¬ B x) := by
  obtain ⟨f, hf, he⟩ := h
  exact ⟨f, hf, fun x => not_congr (he x)⟩

theorem halting_complete {A : ℕ → Prop} (hA : REPred A) :
    A ≤₀ (fun n => n ∈ UniversalComputation.haltingPairs) := by
  obtain ⟨e, he⟩ := (UniversalComputation.enumerable_iff_index A).mp hA
  refine ⟨fun x => Nat.pair e x, (Primrec₂.natPair.comp (Primrec.const e) Primrec.id).to_comp, ?_⟩
  intro x
  simpa [UniversalComputation.haltingPairs] using he x

def robinsonConjunction : language.Sentence :=
  qSuccNeZero ⊓ (qSuccInjective ⊓ (qPredecessor ⊓ (qAddZero ⊓
    (qAddSucc ⊓ (qMulZero ⊓ qMulSucc)))))

theorem robinsonConjunction_realize {M : Type*} [language.Structure M] :
    M ⊨ robinsonConjunction ↔ M ⊨ Q := by
  simp only [robinsonConjunction, Sentence.realize_inf, Q, Theory.model_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

def ValidCodes (n : ℕ) : Prop :=
  ∃ A : language.Sentence, sentenceCode arithmeticSignature A = n ∧
    (∅ : language.Theory) ⊨ᵇ A

def SatisfiableCodes (n : ℕ) : Prop :=
  ∃ A : language.Sentence, sentenceCode arithmeticSignature A = n ∧
    ({A} : language.Theory).IsSatisfiable

def NonvalidCodes (n : ℕ) : Prop :=
  isSentence arithmeticSignature n = true ∧ ¬ ValidCodes n

theorem valid_code (A : language.Sentence) :
    ValidCodes (sentenceCode arithmeticSignature A) ↔ (∅ : language.Theory) ⊨ᵇ A := by
  constructor
  · rintro ⟨B, hB, h⟩
    exact (sentence_code_injective arithmeticSignature hB) ▸ h
  · exact fun h => ⟨A, rfl, h⟩

theorem satisfiable_code (A : language.Sentence) :
    SatisfiableCodes (sentenceCode arithmeticSignature A) ↔
      ({A} : language.Theory).IsSatisfiable := by
  constructor
  · rintro ⟨B, hB, h⟩
    exact (sentence_code_injective arithmeticSignature hB) ▸ h
  · exact fun h => ⟨A, rfl, h⟩

theorem finite_axiom_reduction (A : language.Sentence) :
    Derives Q A ↔ (∅ : language.Theory) ⊨ᵇ (robinsonConjunction.imp A) := by
  rw [← HenkinCompleteness.consequence_iff_derives]
  constructor
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [Sentence.realize_imp]
    intro hq
    let : M ⊨ Q := robinsonConjunction_realize.mp hq
    exact Theory.models_sentence_iff.mp h (Theory.ModelType.of Q M)
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    let : M ⊨ (∅ : language.Theory) := inferInstance
    have hi := Theory.models_sentence_iff.mp h (Theory.ModelType.of (∅ : language.Theory) M)
    exact (Sentence.realize_imp M).mp hi (robinsonConjunction_realize.mpr inferInstance)

def validityReduction (n : ℕ) : ℕ :=
  if isSentence arithmeticSignature n then
    impCode (sentenceCode arithmeticSignature robinsonConjunction) n else botCode

theorem validityReduction_primitive : Primrec validityReduction := by
  have hi : Primrec (fun n => impCode (sentenceCode arithmeticSignature robinsonConjunction) n) := by
    unfold impCode
    exact primrec_node.comp (Primrec.const _) (Primrec.list_cons.comp (Primrec.const _)
      (Primrec.list_cons.comp Primrec.id (Primrec.const [])))
  exact (Primrec.cond (primrec_isSentence arithmeticSignature) hi (Primrec.const botCode)).of_eq
    fun n => by simp [validityReduction, Bool.cond_eq_ite]

theorem falsum_not_valid : ¬ ValidCodes botCode := by
  change ¬ ValidCodes (sentenceCode arithmeticSignature (⊥ : language.Sentence))
  rw [valid_code]
  intro h
  let : ℕ ⊨ (∅ : language.Theory) := inferInstance
  exact Theory.models_sentence_iff.mp h (Theory.ModelType.of (∅ : language.Theory) ℕ)

theorem validityReduction_correct (n : ℕ) :
    TheoremCodes Q n ↔ ValidCodes (validityReduction n) := by
  by_cases hn : isSentence arithmeticSignature n = true
  · obtain ⟨A, rfl⟩ := (sentence_recognition_iff arithmeticSignature n).mp hn
    rw [theoremCodes_sentenceCode]
    have hc : validityReduction (sentenceCode arithmeticSignature A) =
        sentenceCode arithmeticSignature (robinsonConjunction.imp A) := by
      simp only [validityReduction, hn, ↓reduceIte]
      rfl
    rw [hc, valid_code, finite_axiom_reduction]
  · have hp : ¬ TheoremCodes Q n := by
      rintro ⟨A, rfl, _⟩
      exact hn ((sentence_recognition_iff arithmeticSignature _).mpr ⟨A, rfl⟩)
    simp [validityReduction, hn, hp, falsum_not_valid]

theorem theoremhood_reduces_validity : TheoremCodes Q ≤₀ ValidCodes :=
  ⟨validityReduction, validityReduction_primitive.to_comp, validityReduction_correct⟩

theorem validity_undecidable : ¬ ComputablePred ValidCodes := by
  intro h
  exact essential_undecidability Q (Set.Subset.refl Q) Q_consistent
    (ComputablePred.computable_of_manyOneReducible theoremhood_reduces_validity h)

theorem validity_enumerable : REPred ValidCodes :=
  enumerable_theory_consequences arithmeticSignature ∅ (empty_code_enumerable arithmeticSignature)

theorem complement_validity_not_enumerable : ¬ REPred (fun n => ¬ ValidCodes n) := by
  intro h
  exact validity_undecidable
    (ComputablePred.computable_iff_re_compl_re'.mpr ⟨validity_enumerable, h⟩)

def guardedNegation (n : ℕ) : ℕ :=
  if isSentence arithmeticSignature n then negCode n else negCode botCode

theorem guardedNegation_primitive : Primrec guardedNegation := by
  have hn : Primrec negCode := by unfold negCode impCode; fun_prop
  exact (Primrec.cond (primrec_isSentence arithmeticSignature) hn
    (Primrec.const (negCode botCode))).of_eq fun n => by simp [guardedNegation, Bool.cond_eq_ite]

theorem satisfiable_negation_iff (A : language.Sentence) :
    ({A.not} : language.Theory).IsSatisfiable ↔ ¬ (∅ : language.Theory) ⊨ᵇ A := by
  rw [Theory.models_iff_not_satisfiable]
  simp

theorem guardedNegation_correct (n : ℕ) :
    SatisfiableCodes (guardedNegation n) ↔ ¬ ValidCodes n := by
  by_cases hn : isSentence arithmeticSignature n = true
  · obtain ⟨A, rfl⟩ := (sentence_recognition_iff arithmeticSignature n).mp hn
    simp only [guardedNegation, hn, ↓reduceIte, negation_code, satisfiable_code,
      valid_code, satisfiable_negation_iff]
  · have hv : ¬ ValidCodes n := by
      rintro ⟨A, rfl, _⟩
      exact hn ((sentence_recognition_iff arithmeticSignature _).mpr ⟨A, rfl⟩)
    have ht : SatisfiableCodes (negCode botCode) := by
      change SatisfiableCodes (sentenceCode arithmeticSignature (⊥ : language.Sentence).not)
      rw [satisfiable_code, satisfiable_negation_iff]
      exact fun h => falsum_not_valid ((valid_code _).mpr h)
    simp [guardedNegation, hn, hv, ht]

theorem satisfiability_not_enumerable : ¬ REPred SatisfiableCodes := by
  intro h
  apply complement_validity_not_enumerable
  exact (UniversalComputation.enumerable_preimage h guardedNegation_primitive.to_comp).of_eq
    guardedNegation_correct

theorem satisfiability_undecidable : ¬ ComputablePred SatisfiableCodes :=
  fun h => satisfiability_not_enumerable h.to_re

attribute [local irreducible] isSentence

theorem nonvalidity_not_enumerable : ¬ REPred NonvalidCodes := by
  intro h
  have hi : ComputablePred (fun n => ¬ isSentence arithmeticSignature n = true) :=
    (Primrec.eq.comp (primrec_isSentence arithmeticSignature) (Primrec.const true)).computablePred.not
  apply complement_validity_not_enumerable
  apply (UniversalComputation.enumerable_union h hi.to_re).of_eq
  intro n
  simp only [NonvalidCodes]
  have hv : ValidCodes n → isSentence arithmeticSignature n = true := by
    rintro ⟨A, rfl, _⟩
    exact (sentence_recognition_iff arithmeticSignature _).mpr ⟨A, rfl⟩
  tauto

theorem nonhalting_not_reducible :
    ¬ ((fun n => n ∉ UniversalComputation.haltingPairs) ≤₀
      (fun n => n ∈ UniversalComputation.haltingPairs)) := by
  intro h
  exact UniversalComputation.haltingPairs_complement_not_enumerable
    (enumerable_preimage h UniversalComputation.haltingPairs_enumerable)

end
end Lemmatheca.ComputabilityTheory.ComputableReductions
