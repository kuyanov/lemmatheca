import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityEquivalence
import Lemmatheca.DiagonalLemma.DiagonalLemma
import Lemmatheca.TheoriesAndAxiomatization.Theories

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Consistency distinctions and essential undecidability concern the actual
arithmetic language and the corpus's finite natural-deduction calculus. -/
namespace Lemmatheca.ProofTheory.FirstIncompleteness

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs CodingFormalProofs
open DiagonalLemma

noncomputable section

/-- Existentially close the one free numerical name. -/
def existentialClosure (A : language.Formula Unit) : language.Sentence :=
  (A.relabel (Sum.inr : Unit → Empty ⊕ Unit)).iExs Unit

theorem realize_existentialClosure {M : Type*} [language.Structure M]
    (A : language.Formula Unit) :
    M ⊨ existentialClosure A ↔ ∃ a : M, A.Realize (fun _ => a) := by
  simp only [existentialClosure, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
    Function.comp_def, Sum.elim_inr]
  constructor
  · rintro ⟨a, ha⟩
    have he : (fun _ : Unit => a ()) = a := by funext i; congr 1
    exact ⟨a (), by simpa only [he] using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, ha⟩

/-- Full omega-consistency forbids proving an existential sentence while
refuting every standard numeral instance of the same formula. -/
def OmegaConsistent (T : language.Theory) : Prop :=
  ∀ A : language.Formula Unit,
    (∀ n : ℕ, Derives T (numeralSubstitution A n).not) →
      ¬ Derives T (existentialClosure A)

theorem omegaConsistent_consistent {T : language.Theory} (h : OmegaConsistent T) :
    Consistent T := by
  intro hf
  exact h ⊥ (fun _ => derives_explosion hf) (derives_explosion hf)

/-- Standard-model soundness implies full omega-consistency. -/
theorem omegaConsistent_of_nat_model {T : language.Theory} (hT : ℕ ⊨ T) :
    OmegaConsistent T := by
  intro A hneg hpos
  have hs : ℕ ⊨ existentialClosure A := by
    simpa only [Sentence.Realize, Unique.eq_default] using
      derives_sound hpos (default : Empty → ℕ)
        (fun B hB => by simpa only [Sentence.Realize, Unique.eq_default] using hT.realize_of_mem B hB)
  obtain ⟨n, hn⟩ := (realize_existentialClosure A).mp hs
  have hn' : ℕ ⊨ (numeralSubstitution A n).not := by
    simpa only [Sentence.Realize, Unique.eq_default] using
      derives_sound (hneg n) (default : Empty → ℕ)
        (fun B hB => by simpa only [Sentence.Realize, Unique.eq_default] using hT.realize_of_mem B hB)
  apply (Sentence.realize_not ℕ).mp hn'
  rw [realize_numeralSubstitution]
  simpa only [numeral_value_nat] using hn

/-- The set of codes of actual theorems; non-sentence codes are excluded. -/
def TheoremCodes (T : language.Theory) (n : ℕ) : Prop :=
  ∃ σ : language.Sentence, sentenceCode arithmeticSignature σ = n ∧ Derives T σ

theorem theoremCodes_sentenceCode (T : language.Theory) (σ : language.Sentence) :
    TheoremCodes T (sentenceCode arithmeticSignature σ) ↔ Derives T σ := by
  constructor
  · rintro ⟨τ, ht, hτ⟩
    exact (sentence_code_injective arithmeticSignature ht) ▸ hτ
  · intro h
    exact ⟨σ, rfl, h⟩

private theorem signed_numerals {n : ℕ} {R : (Fin n → ℕ) → Prop}
    {A : language.Formula (Fin n)} (h : SignedRepresents R A)
    (M : Theory.ModelType.{0, 0, 0} Q) (x : Fin n → ℕ) :
    A.Realize (fun i => numeralValue M (x i)) ↔ R x := by
  constructor
  · intro ha
    by_contra hn
    have hp : M ⊨ (numeralInstance A x).not :=
      derives_sound ((h x).2 hn) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact ((Sentence.realize_not M).mp hp)
      ((realize_numeralInstance A x).mpr ha)
  · intro hr
    have hp : M ⊨ numeralInstance A x :=
      derives_sound ((h x).1 hr) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact (realize_numeralInstance A x).mp hp

/-- Every consistent extension of Q has an undecidable theorem set, even when
its axiom set is not computably enumerable. -/
theorem essential_undecidability (T : language.Theory) (hQ : Q ⊆ T)
    (hcon : Consistent T) : ¬ ComputablePred (TheoremCodes T) := by
  intro hc
  have hr : ComputablePred (fun x : Fin 1 → ℕ => TheoremCodes T (x 0)) := by
    let := hc.choose
    have hx : Computable (fun x : Fin 1 → ℕ => x 0) :=
      Computable.fin_app.comp Computable.id (Computable.const 0)
    exact ⟨inferInstance, hc.choose_spec.comp hx⟩
  obtain ⟨F, hF⟩ := (recursive_relation_iff _).mp hr
  let A : language.Formula Unit := F.relabel (fun _ => ())
  let G := fixedPoint A.not
  have hA (M : Theory.ModelType.{0, 0, 0} Q) :
      A.Realize (fun _ => numeralValue M (sentenceCode arithmeticSignature G)) ↔
        Derives T G := by
    simpa only [A, Formula.realize_relabel, Function.comp_def,
      theoremCodes_sentenceCode] using
      signed_numerals hF M (fun _ => sentenceCode arithmeticSignature G)
  have hfix (M : Theory.ModelType.{0, 0, 0} Q) :
      M ⊨ G ↔ ¬ Derives T G := by
    have hf := fixedPoint_modelwise (M := M) A.not
    rw [realize_numeralSubstitution, Formula.realize_not, hA M] at hf
    exact hf
  have hnp : ¬ Derives T G := by
    intro hp
    obtain ⟨M, hM, hne, _, hmodel⟩ := HenkinCompleteness.countable_model_existence hcon
    let := hM
    let := hne
    let _ : M ⊨ Q := hmodel.mono hQ
    let Mq := Theory.ModelType.of Q M
    have hg : Mq ⊨ G :=
      derives_sound hp (default : Empty → Mq)
        (fun B hB => hmodel.realize_of_mem B hB)
    exact (hfix Mq).mp hg hp
  apply hnp
  apply derives_mono (T := Q) (hTU := hQ)
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  exact (hfix M).mpr hnp

/-- True arithmetic cannot have a computably enumerable axiom set. -/
theorem trueArithmetic_not_enumerable :
    ¬ CodeEnumerable arithmeticSignature trueArithmetic := by
  intro he
  have hnat : ℕ ⊨ trueArithmetic := by
    change ℕ ⊨ language.completeTheory ℕ
    infer_instance
  have hcon := theory_consistent_of_model hnat
  have hQ : Q ⊆ trueArithmetic :=
    Set.Subset.trans Set.subset_union_left PA_subset_true_arithmetic
  apply essential_undecidability trueArithmetic hQ hcon
  apply enumerable_complete_theory_decidable arithmeticSignature trueArithmetic he hcon
  intro σ
  by_cases hσ : ℕ ⊨ σ
  · exact Or.inl (derives_assumption hσ)
  · exact Or.inr (derives_assumption ((Sentence.realize_not ℕ).mpr hσ))

end
end Lemmatheca.ProofTheory.FirstIncompleteness
