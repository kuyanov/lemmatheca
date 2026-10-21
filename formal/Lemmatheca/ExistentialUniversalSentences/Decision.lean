import Lemmatheca.ExistentialUniversalSentences.FiniteModels

/-! A total, executable decision procedure on the corpus's numerical matrix codes. -/
namespace Lemmatheca.MathematicalLogic.ExistentialUniversalSentences
open FirstOrder FirstOrder.Language
open Lemmatheca.ProofTheory.CodingFormalProofs

variable (c : ℕ) (arities : List ℕ)

/-- Invalid matrices are rejected. Valid inputs are searched through the explicit finite tables. -/
def decideCode (m n e : ℕ) : Bool :=
  match readMatrix c arities (m+n) e with
  | none => false
  | some φ => (List.range (max 1 (m+c))).any fun d =>
      (tables c arities d).any fun T => accepts c arities T φ

/-- The code of the full prefix can also be produced directly from the input presentation. -/
def prefixCode (m n e : ℕ) : ℕ :=
  (exCode^[m]) ((allCode^[n]) e)

private theorem allBlock_code (n : ℕ) {m : ℕ}
    (φ : (lang c arities).BoundedFormula Empty (m+n)) :
    formulaCode (signature c arities) Empty.elim (allBlock c arities n φ) =
      (allCode^[n]) (formulaCode (signature c arities) Empty.elim φ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [allBlock,Function.iterate_succ_apply,formulaCode] using ih φ.all

private theorem exBlock_code (m : ℕ) (φ : (lang c arities).BoundedFormula Empty m) :
    sentenceCode (signature c arities) (exBlock c arities m φ) =
      (exCode^[m]) (formulaCode (signature c arities) Empty.elim φ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simpa only [exBlock,Function.iterate_succ_apply,BoundedFormula.ex,formulaCode,
      sentenceCode,exCode,negCode] using ih φ.ex

theorem sentence_code {m n : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n)) :
    sentenceCode (signature c arities) (sentence c arities φ) =
      prefixCode m n (formulaCode (signature c arities) Empty.elim φ) := by
  rw [sentence,exBlock_code,allBlock_code]
  rfl

theorem decideCode_invalid (m n e : ℕ)
    (h : readMatrix c arities (m+n) e = none) : decideCode c arities m n e = false := by
  simp [decideCode,h]

theorem decideCode_sound (m n e : ℕ) (h : decideCode c arities m n e = true) :
    ∃ (φ : (lang c arities).BoundedFormula Empty (m+n)),
      φ.IsQF ∧ formulaCode (signature c arities) Empty.elim φ = e ∧
      ∃ d < max 1 (m+c), ∃ T : Table c arities d,
        letI := tableStructure c arities T
        (Fin (d+1)) ⊨ sentence c arities φ := by
  cases hr : readMatrix c arities (m+n) e with
  | none => simp [decideCode,hr] at h
  | some φ =>
    obtain ⟨hq,hcode⟩ := readMatrix_spec c arities hr
    simp only [decideCode,hr,List.any_eq_true,List.mem_range] at h
    obtain ⟨d,hd,T,_,hacc⟩ := h
    exact ⟨φ,hq,hcode,d,hd,T,(accepts_correct c arities T φ).mp hacc⟩

theorem decideCode_complete {M : Type*} [(lang c arities).Structure M] [Nonempty M]
    {m n : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n)) (hq : φ.IsQF)
    (hφ : M ⊨ sentence c arities φ) :
    decideCode c arities m n (formulaCode (signature c arities) Empty.elim φ) = true := by
  obtain ⟨d,hd,T,hT⟩ := bounded_table_model c arities φ hq hφ
  simp only [decideCode,readMatrix_complete c arities φ hq,List.any_eq_true,List.mem_range]
  exact ⟨d,hd,T,tables_complete c arities T,hT⟩

theorem decideCode_correct {m n : ℕ} (φ : (lang c arities).BoundedFormula Empty (m+n))
    (hq : φ.IsQF) :
    decideCode c arities m n (formulaCode (signature c arities) Empty.elim φ) = true ↔
      ∃ (M : Type) (_ : (lang c arities).Structure M) (_ : Nonempty M),
        M ⊨ sentence c arities φ := by
  constructor
  · intro h
    obtain ⟨ψ,hψ,hcode,d,_,T,hT⟩ := decideCode_sound c arities m n _ h
    have he : ψ = φ := by
      apply Option.some.inj
      rw [← readMatrix_complete c arities ψ hψ,hcode,readMatrix_complete c arities φ hq]
    subst ψ
    exact ⟨Fin (d+1),tableStructure c arities T,⟨0⟩,hT⟩
  · rintro ⟨M,hM,hn,hφ⟩
    exact @decideCode_complete c arities M hM hn m n φ hq hφ

end Lemmatheca.MathematicalLogic.ExistentialUniversalSentences
