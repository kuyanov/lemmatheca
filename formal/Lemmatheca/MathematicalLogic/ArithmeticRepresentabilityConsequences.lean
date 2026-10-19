import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityBasic

namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
noncomputable section

/-- Existence and uniqueness with the input tuple replaced by numerals. -/
def numeralOutputExistsUnique {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit))
    (x : Fin n → ℕ) : language.Sentence :=
  ((specializeInputs φ x).relabel (Sum.inr : Unit → Empty ⊕ Unit)).iExsUnique Unit

/-- Each numerical input has its own proof of existence and uniqueness. -/
theorem stronglyRepresents_existsUnique {n : ℕ} {f : (Fin n → ℕ) → ℕ}
    {φ : language.Formula (Fin n ⊕ Unit)} (h : StronglyRepresents f φ)
    (x : Fin n → ℕ) : Derives Q (numeralOutputExistsUnique φ x) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  change (((specializeInputs φ x).relabel
    (Sum.inr : Unit → Empty ⊕ Unit)).iExsUnique Unit).Realize _
  rw [Formula.realize_iExsUnique]
  refine ⟨fun _ => numeralValue M (f x), ?_, ?_⟩
  · simp only [Formula.realize_relabel, Function.comp_def, Sum.elim_inr,
      realize_specializeInputs]
    exact (stronglyRepresents_modelwise h x _).mpr rfl
  · intro y hy
    funext i
    have hy' : φ.Realize (extend (fun j => numeralValue M (x j)) (y ())) := by
      simpa only [Formula.realize_relabel, Function.comp_def, Sum.elim_inr,
        realize_specializeInputs] using hy
    have heq := (stronglyRepresents_modelwise h x (y ())).mp hy'
    cases i
    exact heq

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
