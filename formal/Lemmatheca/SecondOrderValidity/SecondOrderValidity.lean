import Lemmatheca.SecondOrderArithmetic.SecondOrderArithmetic
import Lemmatheca.ComputableReductions.ComputableReductions

namespace Lemmatheca.MathematicalLogic.SecondOrderValidity
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.ArithmeticTheories
open Lemmatheca.ComputabilityTheory
open Lemmatheca.ProofTheory
noncomputable section
open CodingFormalProofs


/-- Full validity of a closed formula over nonempty arithmetic structures. -/
def FullValid (φ : SecondOrderLogic.Formula language) : Prop :=
  SecondOrderLogic.IsSentence φ ∧ ∀ (M : Type) [language.Structure M] [Nonempty M],
    ∀ (a : ℕ → M) (r : SecondOrderLogic.RelationAssignment M), SecondOrderLogic.fullRealize a r φ

/-- The fixed finite Peano theory written as one actual second-order sentence. -/
def peanoConjunction : SecondOrderLogic.Formula language :=
  (SecondOrderLogic.ofSentence ComputableReductions.robinsonConjunction).and
    (SecondOrderLogic.inductionSentence FunctionSymbol.zero FunctionSymbol.succ)

theorem peanoConjunction_isSentence : SecondOrderLogic.IsSentence peanoConjunction := by
  have hq := SecondOrderLogic.ofSentence_isSentence ComputableReductions.robinsonConjunction
  have hi := SecondOrderLogic.inductionSentence_isSentence
    (L := language) FunctionSymbol.zero FunctionSymbol.succ
  simp [peanoConjunction, SecondOrderLogic.IsSentence, SecondOrderLogic.Formula.and,
    SecondOrderLogic.Formula.not, SecondOrderLogic.freeIndividual,
    SecondOrderLogic.freeRelation, hq.1, hq.2, hi.1, hi.2]

theorem peanoConjunction_realize {M : Type*} [language.Structure M]
    (a : ℕ → M) (r : SecondOrderLogic.RelationAssignment M) :
    SecondOrderLogic.fullRealize a r peanoConjunction ↔ SecondOrderArithmetic.FullModels M SecondOrderArithmetic.peanoTheory := by
  change SecondOrderLogic.realize _ a r
    ((SecondOrderLogic.ofSentence ComputableReductions.robinsonConjunction).and
      (SecondOrderLogic.inductionSentence FunctionSymbol.zero FunctionSymbol.succ)) ↔ _
  rw [SecondOrderLogic.realize_and, SecondOrderLogic.realize_ofSentence,
    ComputableReductions.robinsonConjunction_realize]
  constructor
  · rintro ⟨hQ, hi⟩ φ (⟨ψ, hψ, rfl⟩ | hφ) b t
    · exact (SecondOrderLogic.fullRealize_ofSentence b t ψ).mpr (hQ.realize_of_mem ψ hψ)
    · obtain rfl := Set.mem_singleton_iff.mp hφ
      exact (SecondOrderLogic.sentence_assignment_independent _ _
        (SecondOrderLogic.inductionSentence_isSentence _ _) a b r t).mp hi
  · intro h
    exact ⟨((SecondOrderArithmetic.models_peano_iff M).mp h).1,
      h _ (Or.inr rfl) a r⟩

theorem nat_peanoConjunction (a : ℕ → ℕ) (r : SecondOrderLogic.RelationAssignment ℕ) :
    SecondOrderLogic.fullRealize a r peanoConjunction := by
  exact (peanoConjunction_realize a r).mpr SecondOrderArithmetic.nat_models_peano

/-- The same antecedent works uniformly for every arithmetic sentence. -/
def translate (σ : language.Sentence) : SecondOrderLogic.Formula language :=
  .imp peanoConjunction (SecondOrderLogic.ofSentence σ)

theorem translate_isSentence (σ : language.Sentence) : SecondOrderLogic.IsSentence (translate σ) := by
  have hp := peanoConjunction_isSentence
  have hs := SecondOrderLogic.ofSentence_isSentence σ
  simp [translate, SecondOrderLogic.IsSentence, SecondOrderLogic.freeIndividual,
    SecondOrderLogic.freeRelation, hp.1, hp.2, hs.1, hs.2]

theorem truth_to_validity (σ : language.Sentence) :
    (ℕ ⊨ σ) ↔ FullValid (translate σ) := by
  constructor
  · intro ht
    refine ⟨translate_isSentence σ, ?_⟩
    intro M _ _ a r
    change SecondOrderLogic.fullRealize a r peanoConjunction →
      SecondOrderLogic.fullRealize a r (SecondOrderLogic.ofSentence σ)
    intro hp
    obtain ⟨e, _⟩ := SecondOrderArithmetic.canonical_isomorphism M
      ((peanoConjunction_realize a r).mp hp)
    exact (SecondOrderLogic.fullRealize_ofSentence a r σ).mpr
      ((StrongHomClass.realize_sentence e σ).mp ht)
  · intro h
    have hv := h.2 ℕ (fun _ => 0) (fun _ _ _ => False)
    exact (SecondOrderLogic.fullRealize_ofSentence _ _ σ).mp
      (hv (nat_peanoConjunction _ _))

/-- Explicit tags on the actual six second-order constructors. -/
def formulaCode : SecondOrderLogic.Formula language → ℕ
  | .firstOrder φ => CodingFormalProofs.node 20 [CodingFormalProofs.namedCode CodingFormalProofs.arithmeticSignature φ]
  | @SecondOrderLogic.Formula.relation _ n X ts =>
      CodingFormalProofs.node 21 (n :: X :: List.ofFn
        (fun i : Fin n => CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature CodingFormalProofs.freeName (ts i)))
  | .falsum => CodingFormalProofs.node 22 []
  | .imp φ ψ => CodingFormalProofs.node 23 [formulaCode φ, formulaCode ψ]
  | .allIndividual x φ => CodingFormalProofs.node 24 [x, formulaCode φ]
  | .allRelation n X φ => CodingFormalProofs.node 25 [n, X, formulaCode φ]

private theorem freeTermCode_injective : Function.Injective
    (termCode arithmeticSignature freeName : language.Term ℕ → ℕ) := by
  intro t q h
  have hc :
      termCode arithmeticSignature (Sum.elim freeName (fun i : Fin 0 => boundName i.val))
        (t.relabel Sum.inl) =
      termCode arithmeticSignature (Sum.elim freeName (fun i : Fin 0 => boundName i.val))
        (q.relabel Sum.inl) := by
    simpa only [termCode_relabel, Function.comp_def, Sum.elim_inl] using h
  have he := term_code_injective arithmeticSignature hc
  have hr := congrArg (Term.relabel (Sum.elim id Fin.elim0)) he
  simpa only [Term.relabel_relabel, Function.comp_def, Sum.elim_inl, Term.relabel_id] using hr

theorem formulaCode_injective : Function.Injective formulaCode := by
  intro φ ψ h
  induction φ generalizing ψ with
  | firstOrder φ =>
    cases ψ <;> try
      (have ht := congrArg tag h; norm_num [formulaCode, node_tag] at ht)
    rename_i χ
    have ha := congrArg args h
    simp only [formulaCode, node_args, List.cons.injEq, and_true] at ha
    exact congrArg SecondOrderLogic.Formula.firstOrder (named_code_injective arithmeticSignature ha)
  | @relation n X ts =>
    cases ψ <;> try
      (have ht := congrArg tag h; norm_num [formulaCode, node_tag] at ht)
    rename_i m Y us
    have ha := congrArg args h
    simp only [formulaCode, node_args, List.cons.injEq] at ha
    rcases ha with ⟨hn, hX, ht⟩
    subst m
    subst Y
    have hts : ts = us := by
      funext i
      apply freeTermCode_injective
      have hh := congrArg (fun l : List ℕ => l[i.val]?) ht
      simpa using hh
    cases hts
    rfl
  | falsum =>
    cases ψ <;> try
      (have ht := congrArg tag h; norm_num [formulaCode, node_tag] at ht)
    rfl
  | imp φ χ ihφ ihχ =>
    cases ψ <;> try
      (have ht := congrArg tag h; norm_num [formulaCode, node_tag] at ht)
    rename_i φ' χ'
    have ha := congrArg args h
    simp only [formulaCode, node_args, List.cons.injEq, and_true] at ha
    exact congrArg₂ SecondOrderLogic.Formula.imp (ihφ ha.1) (ihχ ha.2)
  | allIndividual x φ ih =>
    cases ψ <;> try
      (have ht := congrArg tag h; norm_num [formulaCode, node_tag] at ht)
    rename_i y ψ
    have ha := congrArg args h
    simp only [formulaCode, node_args, List.cons.injEq, and_true] at ha
    rcases ha with ⟨rfl, hb⟩
    exact congrArg (SecondOrderLogic.Formula.allIndividual x) (ih hb)
  | allRelation n X φ ih =>
    cases ψ <;> try
      (have ht := congrArg tag h; norm_num [formulaCode, node_tag] at ht)
    rename_i m Y ψ
    have ha := congrArg args h
    simp only [formulaCode, node_args, List.cons.injEq, and_true] at ha
    rcases ha with ⟨rfl, rfl, hb⟩
    exact congrArg (SecondOrderLogic.Formula.allRelation n X) (ih hb)


def ValidCodes (n : ℕ) : Prop :=
  ∃ φ : SecondOrderLogic.Formula language, formulaCode φ = n ∧ FullValid φ

theorem valid_code (φ : SecondOrderLogic.Formula language) :
    ValidCodes (formulaCode φ) ↔ FullValid φ := by
  constructor
  · rintro ⟨ψ, he, hv⟩
    exact (formulaCode_injective he) ▸ hv
  · exact fun hv => ⟨φ, rfl, hv⟩

/-- Invalid arithmetic codes go to the actual second-order falsity code. -/
def validityReduction (n : ℕ) : ℕ :=
  if CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature n then
    CodingFormalProofs.node 23 [formulaCode peanoConjunction, (CodingFormalProofs.node 20 [n])]
  else formulaCode .falsum

theorem validityReduction_primitive : Primrec validityReduction := by
  have hf : Primrec (fun n : ℕ => node 20 [n]) :=
    primrec_node.comp (Primrec.const 20)
      (Primrec.list_cons.comp Primrec.id (Primrec.const []))
  have hi : Primrec (fun n : ℕ => node 23 [formulaCode peanoConjunction, (node 20 [n])]) :=
    primrec_node.comp (Primrec.const 23)
      (Primrec.list_cons.comp (Primrec.const _)
        (Primrec.list_cons.comp hf (Primrec.const [])))
  exact (Primrec.cond (primrec_isSentence arithmeticSignature) hi
    (Primrec.const (formulaCode .falsum))).of_eq
      fun n => by simp [validityReduction, Bool.cond_eq_ite]

theorem translate_code (σ : language.Sentence) :
    validityReduction (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature σ) =
      formulaCode (translate σ) := by
  have hs := (sentence_recognition_iff arithmeticSignature _).mpr ⟨σ, rfl⟩
  simp [validityReduction, hs, translate, formulaCode, SecondOrderLogic.ofSentence]

theorem invalid_input {n : ℕ} (hn : CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature n ≠ true) :
    validityReduction n = formulaCode .falsum := by
  simp [validityReduction, hn]

theorem falsum_not_valid : ¬ ValidCodes (formulaCode .falsum) := by
  rw [valid_code]
  intro h
  exact h.2 ℕ (fun _ => 0) (fun _ _ _ => False)

def TrueArithmeticCodes (n : ℕ) : Prop :=
  ∃ σ ∈ trueArithmetic, CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature σ = n

theorem true_arithmetic_code (σ : language.Sentence) :
    TrueArithmeticCodes (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature σ) ↔ (ℕ ⊨ σ) := by
  constructor
  · rintro ⟨τ, ht, hc⟩
    exact sentence_code_injective arithmeticSignature hc ▸ ht
  · intro h
    exact ⟨σ, h, rfl⟩

theorem validityReduction_correct (n : ℕ) :
    TrueArithmeticCodes n ↔ ValidCodes (validityReduction n) := by
  by_cases hn : isSentence arithmeticSignature n = true
  · obtain ⟨σ, rfl⟩ := (sentence_recognition_iff arithmeticSignature n).mp hn
    rw [true_arithmetic_code, translate_code, valid_code, truth_to_validity]
  · have ht : ¬ TrueArithmeticCodes n := by
      rintro ⟨σ, _, rfl⟩
      exact hn ((sentence_recognition_iff arithmeticSignature _).mpr ⟨σ, rfl⟩)
    simp [validityReduction, hn, ht, falsum_not_valid]

theorem true_arithmetic_reduces_validity : TrueArithmeticCodes ≤₀ ValidCodes := by
  exact ⟨validityReduction, validityReduction_primitive.to_comp, validityReduction_correct⟩

theorem validity_not_enumerable : ¬ REPred ValidCodes := by
  intro h
  apply FirstIncompleteness.trueArithmetic_not_enumerable
  change REPred TrueArithmeticCodes
  exact (UniversalComputation.enumerable_preimage h validityReduction_primitive.to_comp).of_eq
    (fun n => (validityReduction_correct n).symm)

theorem validity_undecidable : ¬ ComputablePred ValidCodes := by
  exact fun h => validity_not_enumerable h.to_re

def Sound (P : ℕ → Prop) : Prop := ∀ n, P n → ValidCodes n

def WeaklyComplete (P : ℕ → Prop) : Prop := ∀ n, ValidCodes n → P n

theorem no_effective_completeness (P : ℕ → Prop) (hP : REPred P) :
    ¬ (Sound P ∧ WeaklyComplete P) := by
  rintro ⟨hS, hC⟩
  apply validity_not_enumerable
  exact hP.of_eq (fun n => ⟨hS n, hC n⟩)

theorem sound_effective_incomplete (P : ℕ → Prop) (hP : REPred P) (hS : Sound P) :
    ∃ φ : SecondOrderLogic.Formula language, FullValid φ ∧ ¬ P (formulaCode φ) := by
  by_contra h
  apply no_effective_completeness P hP
  refine ⟨hS, ?_⟩
  rintro n ⟨φ, rfl, hv⟩
  by_contra hp
  exact h ⟨φ, hv, hp⟩

theorem sound_no_falsum (P : ℕ → Prop) (hS : Sound P) :
    ¬ P (formulaCode .falsum) := by
  exact fun hp => falsum_not_valid (hS _ hp)

def Certified (check : ℕ → ℕ → Bool) (n : ℕ) : Prop := ∃ p, check p n = true

theorem certified_enumerable (check : ℕ → ℕ → Bool) (hc : Computable₂ check) :
    REPred (Certified check) := by
  have hR : ComputablePred (fun q : ℕ × ℕ => check q.2 q.1 = true) :=
    ComputablePred.computable_iff.mpr
      ⟨_, hc.comp Computable.snd Computable.fst, rfl⟩
  exact UniversalComputation.enumerable_exists hR.to_re

theorem no_complete_checker (check : ℕ → ℕ → Bool) (hc : Computable₂ check)
    (hS : Sound (Certified check)) : ¬ WeaklyComplete (Certified check) := by
  exact fun hW => no_effective_completeness _ (certified_enumerable check hc) ⟨hS, hW⟩

theorem semantic_theorem_set : Sound ValidCodes ∧ WeaklyComplete ValidCodes := by
  exact ⟨fun _ h => h, fun _ h => h⟩

end
end Lemmatheca.MathematicalLogic.SecondOrderValidity
