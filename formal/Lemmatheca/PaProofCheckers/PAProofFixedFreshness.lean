import Lemmatheca.PaListsAndSyntax.PANumeralCodes
import Lemmatheca.PaProofCheckers.PAProofFixedCertificates
import Lemmatheca.PaListsAndSyntax.PAProofOccurrence
import Lemmatheca.PaListsAndSyntax.PANativeSyntaxEvaluation

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Original-language finite certificates have no auxiliary names, uniformly
for every (possibly nonstandard) auxiliary name in a PA model. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem occursAux_original_leaf_zero (j : M) (k : ℕ) (xs : List M)
    (hk : k = 0 ∨ k = 1) : occursAux.value ![j, modelNode k xs] = zeroValue M := by
  rw [occurs_equation_value, occursStep_modelNode_value]
  have h8 : k ≠ 8 := by rcases hk with rfl | rfl <;> decide
  simp only [h8, hk, ↓reduceIte, sign_zero_value]

theorem termCode_occursAux_zero {α : Type*} (j : M) (name : α → ℕ)
    (t : language.Term α)
    (hn : ∀ i, occursAux.value ![j, numeralValue M (name i)] = zeroValue M) :
    occursAux.value ![j, numeralValue M
      (CodingFormalProofs.termCode CodingFormalProofs.arithmeticSignature name t)] = zeroValue M := by
  induction t with
  | var i => exact hn i
  | @func n f ts ih =>
    rw [CodingFormalProofs.termCode, ← modelNode_numerals]
    apply occursAux_modelNode_zero j 2 _ (by decide)
    intro a ha
    simp only [List.map_cons, Nat.reduceEqDiff, true_or, ↓reduceIte, List.tail_cons,
      List.mem_map, List.mem_ofFn] at ha
    obtain ⟨b, ⟨i, rfl⟩, rfl⟩ := ha
    exact ih i

theorem boundName_occursAux_zero (j : M) (n : ℕ) :
    occursAux.value ![j, numeralValue M (CodingFormalProofs.boundName n)] = zeroValue M := by
  change occursAux.value ![j, numeralValue M (CodingFormalProofs.node 1 [n])] = zeroValue M
  rw [← modelNode_numerals]
  exact occursAux_original_leaf_zero j 1 _ (Or.inr rfl)

theorem formulaCode_occursAux_zero {α : Type*} {k : ℕ} (j : M) (name : α → ℕ)
    (A : language.BoundedFormula α k)
    (hn : ∀ i, occursAux.value ![j, numeralValue M (name i)] = zeroValue M) :
    occursAux.value ![j, numeralValue M
      (CodingFormalProofs.formulaCode CodingFormalProofs.arithmeticSignature name A)] = zeroValue M := by
  have hnames (k : ℕ) (i : α ⊕ Fin k) : occursAux.value
      ![j, numeralValue M ((Sum.elim name (fun i => CodingFormalProofs.boundName i.val)) i)] =
        zeroValue M := by
    cases i with
    | inl i => exact hn i
    | inr i => exact boundName_occursAux_zero j i.val
  induction A with
  | falsum =>
    change occursAux.value ![j, numeralValue M (CodingFormalProofs.node 3 [])] = _
    rw [← modelNode_numerals]
    apply occursAux_modelNode_zero j 3 _ (by decide)
    simp
  | equal s t =>
    rw [CodingFormalProofs.formulaCode]
    change occursAux.value ![j, numeralValue M (CodingFormalProofs.node 4 [_ , _])] = _
    rw [← modelNode_numerals]
    apply occursAux_modelNode_zero j 4 _ (by decide)
    intro a ha
    simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact termCode_occursAux_zero j _ s (hnames _)
    · exact termCode_occursAux_zero j _ t (hnames _)
  | rel e _ => exact e.elim
  | imp a b ha hb =>
    rw [CodingFormalProofs.formulaCode]
    change occursAux.value ![j, numeralValue M (CodingFormalProofs.node 6 [_ , _])] = _
    rw [← modelNode_numerals]
    apply occursAux_modelNode_zero j 6 _ (by decide)
    intro x hx
    simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  | all a ha =>
    rw [CodingFormalProofs.formulaCode]
    change occursAux.value ![j, numeralValue M (CodingFormalProofs.node 7 [_])] = _
    rw [← modelNode_numerals]
    apply occursAux_modelNode_zero j 7 _ (by decide)
    intro x hx
    simp only [Nat.reduceEqDiff, or_self, ↓reduceIte, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx ▸ ha

theorem sentenceCode_occursAux_zero (j : M) (A : language.Sentence) :
    occursAux.value ![j, numeralValue M
      (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A)] = zeroValue M :=
  formulaCode_occursAux_zero j Empty.elim A (fun i => i.elim)

theorem sentenceContext_fresh (j : M) (gamma : List language.Sentence) :
    contextFresh.value ![j, numeralValue M (FiniteSequenceCoding.code
      (gamma.map (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature)))] =
        numeralValue M 1 := by
  rw [← modelList_numerals]
  induction gamma with
  | nil => exact contextFresh_zero_value j
  | cons a gamma ih =>
    rw [List.map_cons, List.map_cons, modelList_cons, contextFresh_cons_one_iff]
    exact ⟨sentenceCode_occursAux_zero j a, ih⟩

private theorem certified_context_sentences (E : ℕ → ℕ → Bool) (es ws : List ℕ)
    (hlen : es.length = ws.length)
    (hall : (es.zip ws).all (fun aw =>
      CodingFormalProofs.isSentence CodingFormalProofs.arithmeticSignature aw.1 && E aw.1 aw.2) = true) :
    ∃ gamma : List language.Sentence,
      gamma.map (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature) = es := by
  induction es generalizing ws with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨A, hA⟩ := (CodingFormalProofs.sentence_recognition_iff
        CodingFormalProofs.arithmeticSignature e).mp hall.1.1
      obtain ⟨gamma, hgamma⟩ := ih ws (Nat.succ.inj hlen) hall.2
      exact ⟨A :: gamma, by simp [hA, hgamma]⟩

theorem certified_numeral_context_fresh (E : ℕ → ℕ → Bool) (p a : ℕ)
    (hp : CodingFormalProofs.certificateCheck CodingFormalProofs.arithmeticSignature E p a = true)
    (j : M) :
    contextFresh.value ![j, contextValue (rootValue (numeralValue M p))] = numeralValue M 1 := by
  dsimp only [CodingFormalProofs.certificateCheck] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨gamma, hgamma⟩ := certified_context_sentences E _ _ hp.1.2 hp.2
  have hroot : rootValue (numeralValue M p) =
      numeralValue M (FiniteSequenceCoding.entry p 0) := by
    have h := listEntry.value_numerals (M := M) ![p, 0]
    simpa only [rootValue, numeral_pair_vector, numeral_value_zero,
      listEntry_eval, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hctx : contextValue (numeralValue M (FiniteSequenceCoding.entry p 0)) =
      numeralValue M (CodingFormalProofs.proofContext (FiniteSequenceCoding.entry p 0)) := by
    have h := (argument 0).value_numerals (M := M) ![FiniteSequenceCoding.entry p 0]
    have hv : (fun i : Fin 1 => numeralValue M (![FiniteSequenceCoding.entry p 0] i)) =
        ![numeralValue M (FiniteSequenceCoding.entry p 0)] := by
      funext i
      fin_cases i
      rfl
    simpa only [contextValue, hv, argument_eval, Matrix.cons_val_zero,
      CodingFormalProofs.proofContext] using h
  rw [hroot, hctx]
  have hcode := congrArg FiniteSequenceCoding.code hgamma
  rw [FiniteSequenceCoding.code_decode] at hcode
  change FiniteSequenceCoding.code
    (gamma.map (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature)) =
    CodingFormalProofs.proofContext (FiniteSequenceCoding.entry p 0) at hcode
  rw [← hcode]
  exact sentenceContext_fresh j gamma

theorem fixedProof_context_fresh {n : ℕ} (A : language.Sentence) (hA : Derives PA A)
    (j : M) (x : Fin n → M) :
    contextFresh.value ![j, contextValue (rootValue ((fixedProof A hA).value x))] =
      numeralValue M 1 := by
  rw [fixedProof, constant_value]
  exact certified_numeral_context_fresh _ _ _ (fixedCertificate_correct A hA) j

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
