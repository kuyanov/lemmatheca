import Lemmatheca.PaInductionAndHistories.PAClosureSentences
import Lemmatheca.PaInductionAndHistories.PAInduction

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Closed PA consequences of modelwise induction and least witnesses. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

theorem derives_allClose_of_models {α : Type} [Fintype α]
    (φ : language.Formula α)
    (h : ∀ (M : Theory.ModelType.{0,0,0} PA) (v : α → M), φ.Realize v) :
    Derives PA (allClose φ) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  exact (realize_allClose _).mpr (h M)

def leastWitnessSentence {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) : language.Sentence :=
  let smaller : language.Formula ((Fin k ⊕ Unit) ⊕ Unit) :=
    (ltFormula (.var (.inr ())) (.var (.inl (.inr ())))).imp
      (φ.relabel (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr ()))).not
  allClose ((φ.iExs Unit).imp ((φ ⊓ smaller.iAlls Unit).iExs Unit))

theorem least_witness_derives {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) :
    Derives PA (leastWitnessSentence φ) := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_not, Formula.realize_relabel,
    ltFormula, realize_leFormula, realize_succTerm, Term.realize_var,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rintro ⟨a, ha⟩
  obtain ⟨y, hy, hmin⟩ := least_witness_model φ v ⟨a (), ha⟩
  refine ⟨fun _ => y, hy, ?_⟩
  intro z hz
  have he : (fun x => Sum.elim (Sum.elim v (fun _ : Unit => y)) z
      (Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ()) x)) =
      extend v (z ()) := by
    funext i
    cases i <;> rfl
  simpa only [he] using hmin (z ()) hz

end
end Lemmatheca.ProofTheory.PAComputations
