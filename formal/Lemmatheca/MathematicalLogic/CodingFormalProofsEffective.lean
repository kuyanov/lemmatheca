import Lemmatheca.MathematicalLogic.CodingFormalProofsCorrectness
import Lemmatheca.MathematicalLogic.CodingFormalProofsComputability
import Lemmatheca.MathematicalLogic.EffectiveTheories
import Lemmatheca.MathematicalLogic.UniversalComputation
import Lemmatheca.MathematicalLogic.HenkinCompleteness

/-! Instantiating numerical proof search with the actual corpus calculus. -/
namespace Lemmatheca.MathematicalLogic.CodingFormalProofs
open FirstOrder FirstOrder.Language
variable {L : Language} (S : EffectiveSignature L)

def proofPresentation (E : ℕ → ℕ → Bool) (hE : Primrec₂ E) : EffectiveTheories.ProofPresentation where
  sentence := isSentence S
  negation := negCode
  check := certificateCheck S E
  sentence_primitive := primrec_isSentence S
  negation_primitive := by
    unfold negCode impCode botCode
    fun_prop
  check_primitive := primrec_certificateCheck S E hE
  negation_sentence := by
    intro e he
    obtain ⟨a,rfl⟩ := (sentence_recognition_iff S e).mp he
    rw [negation_code S]
    exact (sentence_recognition_iff S _).mpr ⟨a.not,rfl⟩
  check_sentence := by
    intro p a h
    simp only [certificateCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1.1.2

private theorem presentation_provable (E : ℕ → ℕ → Bool) (hE : Primrec₂ E) (A : L.Sentence) :
    EffectiveTheories.Provable (proofPresentation S E hE) (sentenceCode S A) ↔
      FirstOrderProofs.Derives (theory S E) A := by
  exact certificate_iff_derives S E A

theorem actual_theorems_enumerable (E : ℕ → ℕ → Bool) (hE : Primrec₂ E) :
    REPred (fun a => ∃ p, certificateCheck S E p a = true) := by
  exact EffectiveTheories.theorem_set_enumerable (proofPresentation S E hE)

attribute [local irreducible] isSentence negCode certificateCheck sentenceCode

theorem actual_complete_theory_decidable (E : ℕ → ℕ → Bool) (hE : Primrec₂ E)
    (hk : FirstOrderProofs.Consistent (theory S E))
    (hc : ∀ A, FirstOrderProofs.Derives (theory S E) A ∨ FirstOrderProofs.Derives (theory S E) A.not) :
    ComputablePred (fun n => ∃ A, sentenceCode S A = n ∧ FirstOrderProofs.Derives (theory S E) A) := by
  apply EffectiveTheories.actual_complete_decidable (theory S E) (proofPresentation S E hE) (sentenceCode S)
  · exact sentence_recognition_iff S
  · exact negation_code S
  · exact presentation_provable S E hE
  · exact hk
  · exact hc

/-- Enumerability is a property of the codes of the actual axiom set. -/
def CodeEnumerable (T : L.Theory) : Prop :=
  REPred (fun n => ∃ A ∈ T, sentenceCode S A = n)

theorem empty_code_enumerable : CodeEnumerable S (∅ : L.Theory) := by
  apply (UniversalComputation.enumerable_iff_primitive_certificate _).mpr
  refine ⟨fun _ _ => False, ⟨inferInstance, Primrec.const false⟩, ?_⟩
  simp

/-- A finite witness certifies membership in the given theory, without changing
its axioms. The certificate relation is primitive recursive even when membership
in the axiom set is only computably enumerable. -/
theorem enumerable_theory_certificates (T : L.Theory) (hT : CodeEnumerable S T) :
    ∃ E : ℕ → ℕ → Bool, Primrec₂ E ∧ theory S E = T := by
  classical
  obtain ⟨R, hR, hspec⟩ :=
    (UniversalComputation.enumerable_iff_primitive_certificate _).mp hT
  refine ⟨fun a s => decide (R a s), hR.decide, ?_⟩
  ext A
  change (∃ s, decide (R (sentenceCode S A) s) = true) ↔ A ∈ T
  simp only [decide_eq_true_eq]
  rw [← hspec]
  constructor
  · rintro ⟨B, hB, hcode⟩
    exact (sentence_code_injective S hcode) ▸ hB
  · intro hA
    exact ⟨A, hA, rfl⟩

theorem enumerable_theory_theorems (T : L.Theory) (hT : CodeEnumerable S T) :
    REPred (fun n => ∃ A, sentenceCode S A = n ∧ FirstOrderProofs.Derives T A) := by
  obtain ⟨E, hE, rfl⟩ := enumerable_theory_certificates S T hT
  apply (actual_theorems_enumerable S E hE).of_eq
  intro n
  constructor
  · rintro ⟨p, hp⟩
    have hs : isSentence S n = true := (proofPresentation S E hE).check_sentence p n hp
    obtain ⟨A, rfl⟩ := (sentence_recognition_iff S n).mp hs
    exact ⟨A, rfl, (certificate_iff_derives S E A).mp ⟨p, hp⟩⟩
  · rintro ⟨A, rfl, hA⟩
    exact (certificate_iff_derives S E A).mpr hA

include S in
theorem effective_symbols_countable : Countable L.Symbols := by
  have : ∀ n, Countable (L.Functions n) := fun n => (S.function_injective n).countable
  have : ∀ n, Countable (L.Relations n) := fun n => (S.relation_injective n).countable
  infer_instance

theorem enumerable_theory_consequences (T : L.Theory) (hT : CodeEnumerable S T) :
    REPred (fun n => ∃ A, sentenceCode S A = n ∧ T ⊨ᵇ A) := by
  have := effective_symbols_countable S
  apply (enumerable_theory_theorems S T hT).of_eq
  intro n
  simp only [HenkinCompleteness.consequence_iff_derives]

theorem enumerable_complete_theory_decidable (T : L.Theory) (hT : CodeEnumerable S T)
    (hk : FirstOrderProofs.Consistent T)
    (hc : ∀ A, FirstOrderProofs.Derives T A ∨ FirstOrderProofs.Derives T A.not) :
    ComputablePred (fun n => ∃ A, sentenceCode S A = n ∧ FirstOrderProofs.Derives T A) := by
  obtain ⟨E, hE, rfl⟩ := enumerable_theory_certificates S T hT
  exact actual_complete_theory_decidable S E hE hk hc
end Lemmatheca.MathematicalLogic.CodingFormalProofs
