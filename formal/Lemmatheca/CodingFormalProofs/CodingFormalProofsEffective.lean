import Lemmatheca.CodingFormalProofs.CodingFormalProofsCorrectness
import Lemmatheca.UniversalComputation.UniversalComputation

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Code-enumerable axiom sets and primitive-recursive certificates for the actual syntax. -/
namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
variable {L : Language} (S : EffectiveSignature L)
noncomputable section

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

end
end Lemmatheca.ProofTheory.CodingFormalProofs
