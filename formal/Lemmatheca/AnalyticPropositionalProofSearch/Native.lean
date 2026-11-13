import Lemmatheca.AnalyticPropositionalProofSearch.Search
import Lemmatheca.PropositionalProofs.Deduction

/-! The exact list translation of the existing native classical consequence. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional.AnalyticSearch

open Lemmatheca.MathematicalLogic.Propositional

def nativeInput (H : List (PropFormula ℕ)) (G : PropFormula ℕ) : Input :=
  H.map Nnf.negative ++ [Nnf.positive G]

theorem nativeInput_toFinset (H : List (PropFormula ℕ)) (G : PropFormula ℕ) :
    (nativeInput H G).toFinset = encode H.toFinset {G} := by
  ext A
  simp [nativeInput, encode]

theorem native_search_iff_entails (H : List (PropFormula ℕ)) (G : PropFormula ℕ) :
    (search ∅ (nativeInput H G)).succeeds = true ↔ Entails H.toFinset G := by
  rw [search_succeeds_iff_valid, nativeInput_toFinset, encode_singleton_valid_iff]

theorem native_search_iff_derives (H : List (PropFormula ℕ)) (G : PropFormula ℕ) :
    (search ∅ (nativeInput H G)).succeeds = true ↔
      Lemmatheca.MathematicalLogic.Propositional.Derives H.toFinset G := by
  rw [native_search_iff_entails, derives_iff_entails]

theorem native_search_countervaluation (H : List (PropFormula ℕ)) (G : PropFormula ℕ)
    (v : ℕ → Bool) (h : search ∅ (nativeInput H G) = .counter v) :
    Countervaluation v H.toFinset G := by
  have hc := search_correct ∅ (nativeInput H G) (by simp [LiteralContext])
  rw [h] at hc
  have hf : ∀ A ∈ encode H.toFinset {G}, Nnf.eval v A = false := by
    simpa [Result.Correct, context, nativeInput_toFinset] using hc
  constructor
  · intro F hF
    have hn := hf (Nnf.negative F)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨F, hF, rfl⟩))
    simpa [Nnf.negative, Nnf.normalize_eval, Satisfies] using hn
  · have hp := hf (Nnf.positive G) (by simp [encode])
    simpa [Nnf.positive, Nnf.normalize_eval] using hp

end Lemmatheca.ProofTheory.ClassicalPropositional.AnalyticSearch
