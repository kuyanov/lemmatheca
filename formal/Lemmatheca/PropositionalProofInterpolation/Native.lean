import Lemmatheca.PropositionalProofInterpolation.Extraction
import Lemmatheca.AnalyticPropositionalProofSearch.Native

/-! Exact ordinary-language factors and the specified numbered-atom search output. -/
namespace Lemmatheca.ProofTheory.ClassicalPropositional.Interpolation

open Lemmatheca.MathematicalLogic.Propositional

universe u
variable {α : Type u} [DecidableEq α]

/-- The same actual formula read into the existing native calculus, with exact support. -/
theorem native_factors (A B : PropFormula α)
    (w : Witness {Nnf.negative A} {Nnf.positive B}) :
    Lemmatheca.MathematicalLogic.Propositional.Derives {A} w.formula.read ∧
      Lemmatheca.MathematicalLogic.Propositional.Derives {w.formula.read} B ∧
      atoms w.formula.read ⊆ atoms A ∩ atoms B := by
  refine ⟨?_, ?_, ?_⟩
  · apply Lemmatheca.MathematicalLogic.Propositional.derives_complete
    apply encoded_proof_entails
    refine ⟨?_⟩
    have hc : encode {A} {w.formula.read} = insert w.formula {Nnf.negative A} := by
      ext F
      simp [encode, Nnf.positive_read, or_comm]
    exact hc.symm ▸ w.leftProof
  · apply Lemmatheca.MathematicalLogic.Propositional.derives_complete
    apply encoded_proof_entails
    refine ⟨?_⟩
    simpa [encode, Nnf.negative_eq_dual, Nnf.positive_read, Finset.insert_comm] using w.rightProof
  · simpa [Nnf.atoms_read, vocabulary, Nnf.negative, Nnf.positive, Nnf.atoms_normalize]
      using w.common

/-- The specified Nat-language procedure searches the exact ordered encoding, then extracts. -/
def fromClassical (A B : PropFormula ℕ)
    (h : Lemmatheca.MathematicalLogic.Propositional.Derives {A} B) :
    Witness {Nnf.negative A} {Nnf.positive B} := by
  have hs : (AnalyticSearch.search ∅ (AnalyticSearch.nativeInput [A] B)).succeeds = true :=
    (AnalyticSearch.native_search_iff_derives [A] B).mpr (by simpa using h)
  cases hr : AnalyticSearch.search ∅ (AnalyticSearch.nativeInput [A] B) with
  | proved p =>
      exact extract p {Nnf.negative A} {Nnf.positive B} (by
        intro F hF
        simpa [Covers, AnalyticSearch.context, AnalyticSearch.nativeInput] using hF)
  | counter v => simp [hr, AnalyticSearch.Result.succeeds] at hs

/-- The factors identify the precise formula returned by the declared search/extraction program. -/
theorem fromClassical_factors (A B : PropFormula ℕ)
    (h : Lemmatheca.MathematicalLogic.Propositional.Derives {A} B) :
    Lemmatheca.MathematicalLogic.Propositional.Derives {A}
        (fromClassical A B h).formula.read ∧
      Lemmatheca.MathematicalLogic.Propositional.Derives
        {(fromClassical A B h).formula.read} B ∧
      atoms (fromClassical A B h).formula.read ⊆ atoms A ∩ atoms B := by
  exact native_factors A B (fromClassical A B h)

end Lemmatheca.ProofTheory.ClassicalPropositional.Interpolation
