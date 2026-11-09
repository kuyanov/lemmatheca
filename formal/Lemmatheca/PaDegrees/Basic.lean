import Lemmatheca.TheoriesAndAxiomatization.Theories
import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesPA
import Lemmatheca.EffectivelyClosedClassesAndDnc.Diagonal
import Lemmatheca.BusyBeaverFunctions.FunctionOracles

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ProofTheory
open ArithmeticTheories FirstOrderProofs CodingFormalProofs Theories
open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc

noncomputable section

/-- A completion in the shared arithmetic syntax and proof calculus. -/
def PACompletion (T : language.Theory) : Prop :=
  PA ⊆ T ∧ Consistent T ∧ T.IsComplete ∧ IsDeductivelyClosed T

/-- Only codes of actual sentences are admitted. -/
def completionCodes (T : language.Theory) : Set ℕ :=
  {n | ∃ A ∈ T, sentenceCode arithmeticSignature A = n}

def IsPAOracle (A : Set ℕ) : Prop :=
  ∃ T : language.Theory, PACompletion T ∧ Reducible (completionCodes T) A

def PADegree (d : Degree) : Prop := ∃ A : Set ℕ, degree A = d ∧ IsPAOracle A

def ComputesDNC (A : Set ℕ) : Prop :=
  ∃ D : Set ℕ, D ∈ binaryDNCClass ∧ Reducible D A

def PathProperty (A : Set ℕ) : Prop :=
  ∀ T : Set ℕ, ComputableTreesAndPaths.IsBinaryTree T →
    ComputablePred (fun u => u ∈ T) → (∃ X, ComputableTreesAndPaths.Path T X) →
    ∃ X, ComputableTreesAndPaths.Path T X ∧ Reducible X A

theorem completion_codes_sentence (T : language.Theory) (A : language.Sentence) :
    sentenceCode arithmeticSignature A ∈ completionCodes T ↔ A ∈ T := by
  constructor
  · rintro ⟨B, hB, hcode⟩
    exact (sentence_code_injective arithmeticSignature hcode) ▸ hB
  · intro hA
    exact ⟨A, hA, rfl⟩

theorem completion_codes_malformed (T : language.Theory) (n : ℕ)
    (hn : isSentence arithmeticSignature n = false) : n ∉ completionCodes T := by
  rintro ⟨A, _, rfl⟩
  have hv := (sentence_recognition_iff arithmeticSignature
    (sentenceCode arithmeticSignature A)).mpr ⟨A, rfl⟩
  rw [hn] at hv
  exact Bool.false_ne_true hv

theorem completion_mem_iff_derives (T : language.Theory) (hT : PACompletion T)
    (A : language.Sentence) : A ∈ T ↔ Derives T A := by
  have h := mem_closure_iff_derives T A
  rw [hT.2.2.2] at h
  exact h

theorem completion_exactly_one (T : language.Theory) (hT : PACompletion T)
    (A : language.Sentence) : (A ∈ T ∨ A.not ∈ T) ∧ ¬ (A ∈ T ∧ A.not ∈ T) := by
  refine ⟨?_, ?_⟩
  · exact ((complete_iff_consistent_decides T).mp hT.2.2.1).2 A |>.imp
      (completion_mem_iff_derives T hT A).mpr
      (completion_mem_iff_derives T hT A.not).mpr
  · rintro ⟨hA, hnA⟩
    let M := hT.2.2.1.1.some
    have hp : M ⊨ A := Theory.realize_sentence_of_mem T hA
    have hn : M ⊨ A.not := Theory.realize_sentence_of_mem T hnA
    exact ((Sentence.realize_not M).mp hn) hp

/-- The one-set bridge for total binary natural-valued functions uses actual programs. -/
theorem binary_function_set_bridge (A : Set ℕ) (f : ℕ → ℕ)
    (hf : ∀ n, f n = 0 ∨ f n = 1) :
    PartialComputable A (fun n => Part.some (f n)) ↔ Reducible {n | f n = 1} A := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    let bit : ℕ → ℕ := fun n => if n = 1 then 1 else 0
    have hb : Computable bit :=
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
        (Primrec.const 1) (Primrec.const 0)).to_comp
    refine ⟨.comp (embed (BusyBeaverFunctions.ordinaryProgram bit hb)) c, ?_⟩
    intro n
    change (eval A c n).bind (eval A (embed (BusyBeaverFunctions.ordinaryProgram bit hb))) = _
    rw [congrFun hc n, Part.bind_some, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval]
    simp [bit, indicator]
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun n => ?_⟩
    rw [hc n]
    rcases hf n with h | h <;> simp [indicator, h]

end
end Lemmatheca.ComputabilityTheory.PaDegrees
