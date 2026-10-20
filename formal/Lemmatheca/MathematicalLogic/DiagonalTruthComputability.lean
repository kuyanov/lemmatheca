import Lemmatheca.MathematicalLogic.DiagonalLemma
import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityEquivalence

/-! Truth is a set of actual sentence codes. Its undecidability follows from
numeralwise representation of recursive relations and semantic undefinability. -/
namespace Lemmatheca.MathematicalLogic.DiagonalLemma

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs CodingFormalProofs

/-- The set of codes of sentences true in the standard arithmetic structure. -/
def TruthCodes (n : ℕ) : Prop :=
  ∃ σ : language.Sentence, sentenceCode arithmeticSignature σ = n ∧ ℕ ⊨ σ

/-- At every genuine sentence code, code truth is exactly sentence truth. -/
theorem truthCodes_sentenceCode (σ : language.Sentence) :
    TruthCodes (sentenceCode arithmeticSignature σ) ↔ ℕ ⊨ σ := by
  constructor
  · rintro ⟨τ, hτ, ht⟩
    exact (sentence_code_injective arithmeticSignature hτ) ▸ ht
  · intro hσ
    exact ⟨σ, rfl, hσ⟩

/-- No recursive predicate decides standard arithmetic truth on sentence codes. -/
theorem truthCodes_not_computable : ¬ ComputablePred TruthCodes := by
  classical
  intro hc
  let R : (Fin 1 → ℕ) → Prop := fun x => TruthCodes (x 0)
  have hR : ComputablePred R := by
    obtain ⟨d, hd⟩ := hc
    let _ := d
    exact ⟨fun x => d (x 0),
      hd.comp ((Primrec.fin_app.comp Primrec.id (Primrec.const 0)).to_comp)⟩
  obtain ⟨A, hA⟩ := (recursive_relation_iff R).mp hR
  have hsound {C : language.Sentence} (hC : Derives Q C) : ℕ ⊨ C := by
    have : ℕ ⊨ Q := nat_models_Q
    unfold Sentence.Realize
    apply derives_sound hC
    intro B hB
    exact Theory.realize_sentence_of_mem Q hB
  have hnat (n : ℕ) : A.Realize (fun _ => n) ↔ TruthCodes n := by
    let x : Fin 1 → ℕ := fun _ => n
    constructor
    · intro ha
      by_contra hn
      have hp := hsound ((hA x).2 hn)
      have hnot := (Sentence.realize_not ℕ).mp hp
      apply hnot
      apply (realize_numeralInstance A x).mpr
      simpa only [numeral_value_nat] using ha
    · intro hn
      have hp := hsound ((hA x).1 hn)
      simpa only [numeral_value_nat] using (realize_numeralInstance A x).mp hp
  let B : language.Formula Unit := A.relabel (fun _ => ())
  apply truth_undefinable B
  intro σ
  simpa only [B, Formula.realize_relabel, Function.comp_def] using
    (hnat (sentenceCode arithmeticSignature σ)).trans (truthCodes_sentenceCode σ)

end Lemmatheca.MathematicalLogic.DiagonalLemma
