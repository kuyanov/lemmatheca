import Lemmatheca.PaProofCheckers.PAProofPredicateDefinitions
import Lemmatheca.PaComputations.PAComputationsSentences

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The graph-based parameter-free box agrees provably with the ordinary PA box. -/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open PAComputations ProofPrograms.FixedSyntaxPrograms
noncomputable section

/-- Empty parameter substitution has a unique fixed sentence-code value,
so retaining its graph yields a PA-equivalent, not necessarily identical, box. -/
theorem zero_parameter_box_equivalent (A : language.Sentence) :
    PAEquivalent (formulaBox (A.relabel (Empty.elim : Empty → Fin 0)))
      ((box A).relabel (Empty.elim : Empty → Fin 0)) := by
  let A₀ : language.Formula (Fin 0) := A.relabel Empty.elim
  have hcode : numeralInstance A₀ (Fin.elim0 : Fin 0 → ℕ) = A := by
    dsimp only [A₀, numeralInstance]
    rw [formula_relabel_subst]
    have he : (fun i : Empty => numeral ((Fin.elim0 : Fin 0 → ℕ) (Empty.elim i))) =
        (Term.var : Empty → language.Term Empty) := by
      funext i
      exact i.elim
    rw [he, formula_subst_var]
  apply derives_allClose_of_models
  intro M x
  have hsub (a : M) : (substitutionGraph A₀).Realize (extend x a) ↔
      a = numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A) := by
    change (substitution A₀).sigmaGraph.Realize (extend x a) ↔ _
    have hx : x = (fun i : Fin 0 => numeralValue M ((Fin.elim0 : Fin 0 → ℕ) i)) := by
      funext i
      exact i.elim0
    rw [hx, program_sigma_numerals, substitution_eval, hcode]
  have hbox : ((box A).relabel (Empty.elim : Empty → Fin 0)).Realize x ↔
      ∃ p : M, proofFormula.Realize ![p, numeralValue M
        (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A)] := by
    rw [Formula.realize_relabel]
    have hx : x ∘ (Empty.elim : Empty → Fin 0) = (default : Empty → M) := by
      funext i
      exact i.elim
    rw [hx]
    change (M ⊨ box A) ↔ _
    rw [box, provabilitySentence, realize_numeralInstance, realize_provabilityFormula]
  rw [Formula.realize_iff, formulaBox, realize_boxWithGraph, hbox]
  change (∃ a : M, (substitutionGraph A₀).Realize (extend x a) ∧
    ∃ p : M, proofFormula.Realize ![p, a]) ↔ _
  constructor
  · rintro ⟨a, ha, p, hp⟩
    exact ⟨p, (hsub a).mp ha ▸ hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨_, (hsub _).mpr rfl, p, hp⟩

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
