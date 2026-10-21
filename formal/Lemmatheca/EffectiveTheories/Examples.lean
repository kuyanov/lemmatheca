import Lemmatheca.EffectiveTheories.EffectiveQuantifierElimination
import Lemmatheca.EffectiveTheories.EffectiveTheories
import Lemmatheca.TheoriesAndAxiomatization.Theories
import Lemmatheca.EffectiveTheories.CertifiedProofSearch
import Lemmatheca.EffectiveTheories.EffectiveLanguageCoding

open Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory Lemmatheca.ProofTheory

set_option backward.isDefEq.respectTransparency false

namespace Lemmatheca.Entry.EffectiveTheories

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.ModelTheory.QuantifierElimination

/-- The specific undecided equality sentence used in the search example. -/
def atLeastTwo : Language.empty.Sentence :=
  (BoundedFormula.equal (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2)))).not.ex.ex

theorem empty_equality_undecided :
    ¬ FirstOrderProofs.Derives (∅ : Language.empty.Theory) atLeastTwo ∧
    ¬ FirstOrderProofs.Derives (∅ : Language.empty.Theory) atLeastTwo.not  := by
  let : Language.empty.Structure Unit := Language.emptyStructure
  let : Language.empty.Structure Bool := Language.emptyStructure
  constructor
  · intro h
    have hh := FirstOrderProofs.derives_sound (M := Unit) h Empty.elim (by simp)
    simp [atLeastTwo, Language.Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.Realize, Term.realize, Fin.snoc] at hh
  · intro h
    have hh := FirstOrderProofs.derives_sound (M := Bool) h Empty.elim (by simp)
    simp [atLeastTwo, Language.Formula.Realize, BoundedFormula.realize_ex,
      BoundedFormula.Realize, Term.realize, Fin.snoc] at hh

open CodingFormalProofs EffectiveLanguageCoding

/-- The actual numerical proof checker for the empty equality theory. -/
def emptyEqualityPresentation : EffectiveTheories.ProofPresentation :=
  proofPresentation emptySignature (fun _ _ => false) (Primrec.const false)

private theorem false_certificate_theory {L : Language} (S : EffectiveSignature L) :
    theory S (fun _ _ => false) = ∅ := by
  ext A
  simp [theory]

attribute [local irreducible] isSentence negCode certificateCheck sentenceCode

/-- The two proof searches in the example really diverge, using the shared
sentence code and the actual certified natural-deduction checker. -/
theorem empty_equality_search_stalls :
    EffectiveTheories.search emptyEqualityPresentation (sentenceCode emptySignature atLeastTwo) =
      Part.none := by
  apply EffectiveTheories.search_stalls
  · exact (sentence_recognition_iff emptySignature _).mpr ⟨atLeastTwo, rfl⟩
  · intro h
    have hd := (certificate_iff_derives emptySignature (fun _ _ => false) atLeastTwo).mp h
    rw [false_certificate_theory] at hd
    exact empty_equality_undecided.1 hd
  · intro h
    change (∃ p, certificateCheck emptySignature (fun _ _ => false) p
      (negCode (sentenceCode emptySignature atLeastTwo)) = true) at h
    rw [negation_code] at h
    have hd := (certificate_iff_derives emptySignature (fun _ _ => false) atLeastTwo.not).mp h
    rw [false_certificate_theory] at hd
    exact empty_equality_undecided.2 hd

theorem equality_validity_search_enumerable :
    REPred (fun n => ∃ A : Language.empty.Sentence,
      sentenceCode emptySignature A = n ∧ (∅ : Language.empty.Theory) ⊨ᵇ A) :=
  enumerable_theory_consequences emptySignature ∅ (empty_code_enumerable emptySignature)

theorem order_validity_search_enumerable :
    REPred (fun n => ∃ A : binaryRelLanguage.Sentence,
      sentenceCode orderSignature A = n ∧ (∅ : binaryRelLanguage.Theory) ⊨ᵇ A) :=
  enumerable_theory_consequences orderSignature ∅ (empty_code_enumerable orderSignature)


def differentElement : Language.empty.Sentence :=
  (BoundedFormula.equal (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2)))).not.ex.all

def belowEveryElement : binaryRelLanguage.Sentence :=
  (Shared.ltAtom (n := 2) 0 1).all.ex

theorem algorithm_examples :
    EffectiveQuantifierElimination.decideSentence (o := false) differentElement = true ∧
    EffectiveQuantifierElimination.decideSentence (o := true) Shared.strictDense = true ∧
    EffectiveQuantifierElimination.decideSentence (o := true) belowEveryElement = false  := by
  refine ⟨?_,?_,?_⟩
  · apply (EffectiveQuantifierElimination.equality_sentence_decision differentElement).mpr
    intro M v xs
    have : Infinite M := Language.empty.model_infiniteTheory_iff.mp M.is_model
    simp only [differentElement, BoundedFormula.realize_all, BoundedFormula.realize_ex,
      BoundedFormula.realize_not]
    intro a
    obtain ⟨b,hb⟩ := exists_ne a
    refine ⟨b,?_⟩
    simpa [BoundedFormula.Realize, Term.realize, Fin.snoc] using Ne.symm hb
  · apply (EffectiveQuantifierElimination.order_sentence_decision Shared.strictDense).mpr
    exact Theory.models_sentence_of_mem (by simp [Shared.strictDloTheory])
  · apply Bool.eq_false_iff.mpr
    intro h
    have h' := (EffectiveQuantifierElimination.order_sentence_decision belowEveryElement).mp h
    let : binaryRelLanguage.Structure ℚ := FirstOrderSemantics.binaryRelStructure ℚ (fun a b => a < b)
    let : ℚ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
    have hh := h'.realize_sentence ℚ
    simp only [belowEveryElement, Sentence.Realize, Language.Formula.Realize,
      BoundedFormula.realize_ex, BoundedFormula.realize_all, Shared.ltAtom_realize] at hh
    obtain ⟨a,ha⟩ := hh
    have hx := ha a
    change a < a at hx
    exact lt_irrefl a hx


end Lemmatheca.Entry.EffectiveTheories
