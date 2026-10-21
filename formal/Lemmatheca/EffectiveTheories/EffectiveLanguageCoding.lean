import Lemmatheca.EffectiveTheories.EffectiveQuantifierElimination
import Lemmatheca.CodingFormalProofs.CodingFormalProofsSyntax

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ProofTheory

/-! The relational decision procedures and certified proof search use exactly
the same numerical coding, not merely two equivalent encodings. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveLanguageCoding
open FirstOrder FirstOrder.Language
open Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrderSyntax QuantifierElimination

def emptySignature : EffectiveSignature Language.empty where
  functionCode := Empty.elim
  relationCode := Empty.elim
  functionTest := fun _ _ => false
  relationTest := fun _ _ => false
  function_iff := by simp
  relation_iff := by simp
  function_injective := by
    intro n a b h
    exact a.elim
  relation_injective := by
    intro n a b h
    exact a.elim
  function_primrec := Primrec.const false
  relation_primrec := Primrec.const false

def orderSignature : EffectiveSignature binaryRelLanguage where
  functionCode := Empty.elim
  relationCode := fun _ => 0
  functionTest := fun _ _ => false
  relationTest := fun a n => decide (a = 0 ∧ n = 2)
  function_iff := by simp [binaryRelLanguage]
  relation_iff := by
    intro a n
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨.rel, rfl⟩
    · rintro ⟨r, rfl⟩
      cases r
      simp
  function_injective := by
    intro n a b h
    exact a.elim
  relation_injective := by
    intro n a b _
    cases a
    cases b
    rfl
  function_primrec := Primrec.const false
  relation_primrec := by
    exact ((Primrec.eq.comp Primrec.fst (Primrec.const 0)).and
      (Primrec.eq.comp Primrec.snd (Primrec.const 2))).decide

def relationalSignature : (o : Bool) → EffectiveSignature (Shared.Lang o)
  | false => emptySignature
  | true => orderSignature

theorem relational_term_code {o n} (t : (Shared.Lang o).Term (Empty ⊕ Fin n)) :
    EffectiveQuantifierElimination.termCode t =
      termCode (relationalSignature o) (Sum.elim Empty.elim (fun i => boundName i.val)) t := by
  cases t with
  | var i => cases i with
    | inl e => exact e.elim
    | inr i => rfl
  | func f ts => cases o <;> exact f.elim

theorem relational_syntax_code {o n} (φ : (Shared.Lang o).BoundedFormula Empty n) :
    EffectiveQuantifierElimination.syntaxCode φ = formulaCode (relationalSignature o) Empty.elim φ := by
  induction φ with
  | falsum => rfl
  | equal t u => simp only [EffectiveQuantifierElimination.syntaxCode, formulaCode,
      equalCode, relational_term_code]; rfl
  | @rel n k r ts =>
    cases o with
    | false => exact r.elim
    | true =>
      cases r
      simp [EffectiveQuantifierElimination.syntaxCode, formulaCode, relationalSignature,
        orderSignature, List.ofFn_succ, relational_term_code,
        EffectiveQuantifierPrograms.node, node]
  | imp φ ψ ihφ ihψ =>
    simp only [EffectiveQuantifierElimination.syntaxCode, formulaCode, ihφ, ihψ]
    rfl
  | all φ ih =>
    simp only [EffectiveQuantifierElimination.syntaxCode, formulaCode, ih]
    rfl

theorem relational_sentence_code {o} (φ : (Shared.Lang o).Sentence) :
    EffectiveQuantifierElimination.syntaxCode φ = sentenceCode (relationalSignature o) φ :=
  relational_syntax_code φ

end Lemmatheca.ComputabilityTheory.EffectiveLanguageCoding
