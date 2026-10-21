import Lemmatheca.CodingFormalProofs.CodingFormalProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

theorem termCode_relabel {α β : Type*} (name : β → ℕ) (f : α → β) (t : L.Term α) :
    termCode S name (t.relabel f) = termCode S (name ∘ f) t := by
  induction t with
  | var x => rfl
  | func g ts ih =>
    simp only [Term.relabel, termCode, ih]

theorem formulaCode_relabel {α β : Type*} (name : β → ℕ) (f : α → β)
    {n : ℕ} (a : L.BoundedFormula α n) :
    formulaCode S name (a.relabel (fun x => (Sum.inl (f x) : β ⊕ Fin 0))) =
      formulaCode S (name ∘ f) a := by
  have hn (k : ℕ) :
      (Sum.elim name (fun i : Fin (0 + k) => boundName i.val)) ∘
          BoundedFormula.relabelAux (fun x => (Sum.inl (f x) : β ⊕ Fin 0)) k =
        Sum.elim (name ∘ f) (fun i : Fin k => boundName i.val) := by
    funext x
    cases x <;> simp [Function.comp_def, BoundedFormula.relabelAux]
  induction a with
  | falsum => rfl
  | equal s t =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, formulaCode,
      termCode_relabel, hn]
  | rel r ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, formulaCode,
      termCode_relabel, hn, id_eq]
  | imp a b iha ihb => simp only [BoundedFormula.relabel_imp, formulaCode, iha, ihb]
  | all a ih => simp only [BoundedFormula.relabel_all, formulaCode, ih]

@[simp] theorem sentence_as_named_code (a : L.Sentence) :
    namedCode S (a.relabel (Empty.elim : Empty → ℕ)) = sentenceCode S a := by
  unfold namedCode sentenceCode Formula.relabel
  have h := formulaCode_relabel S auxName (Empty.elim : Empty → ℕ) a
  have hn : auxName ∘ (Empty.elim : Empty → ℕ) = Empty.elim := by
    funext x
    cases x
  rw [hn] at h
  exact h

end Lemmatheca.ProofTheory.CodingFormalProofs
