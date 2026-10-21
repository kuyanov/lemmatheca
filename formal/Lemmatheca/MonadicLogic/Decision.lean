import Lemmatheca.MonadicLogic.FiniteModels

namespace Lemmatheca.MathematicalLogic.MonadicLogic
open FirstOrder FirstOrder.Language

/-- A total finite syntax procedure; its computation uses only recursive syntax and finite tables. -/
def decideSentence {k : ℕ} (φ : (lang k).Sentence) : Bool :=
  (List.range (bound φ)).any fun d =>
    (ExistentialUniversalSentences.tables 0 (arities k) d).any fun T => ExistentialUniversalSentences.evaluate 0 (arities k) T φ Fin.elim0

/-- Validity is the complement of satisfiability of the syntactic negation. -/
def decideValidity {k : ℕ} (φ : (lang k).Sentence) : Bool := !decideSentence φ.not

theorem decideSentence_sound {k : ℕ} (φ : (lang k).Sentence) (h : decideSentence φ = true) :
    ∃ d < bound φ, ∃ T : ExistentialUniversalSentences.Table 0 (arities k) d,
      letI := ExistentialUniversalSentences.tableStructure 0 (arities k) T
      (Fin (d+1)) ⊨ φ := by
  simp only [decideSentence, List.any_eq_true, List.mem_range] at h
  obtain ⟨d, hd, T, _, hT⟩ := h
  refine ⟨d, hd, T, ?_⟩
  let := ExistentialUniversalSentences.tableStructure 0 (arities k) T
  have hφ := (ExistentialUniversalSentences.evaluate_correct 0 (arities k) T φ Fin.elim0).mp hT
  change BoundedFormula.Realize φ _ _
  convert hφ using 1

theorem decideSentence_complete {k : ℕ} {M : Type*} [(lang k).Structure M] [Nonempty M]
    (φ : (lang k).Sentence) (hφ : M ⊨ φ) : decideSentence φ = true := by
  obtain ⟨d, hd, T, hT⟩ := bounded_table_model φ hφ
  simp only [decideSentence, List.any_eq_true, List.mem_range]
  exact ⟨d, hd, T, ExistentialUniversalSentences.tables_complete 0 (arities k) T, hT⟩

theorem decideSentence_correct {k : ℕ} (φ : (lang k).Sentence) :
    decideSentence φ = true ↔
      ∃ (M : Type) (_ : (lang k).Structure M) (_ : Nonempty M), M ⊨ φ := by
  constructor
  · intro h
    obtain ⟨d, _, T, hT⟩ := decideSentence_sound φ h
    exact ⟨Fin (d+1), ExistentialUniversalSentences.tableStructure 0 (arities k) T, ⟨0⟩, hT⟩
  · rintro ⟨M, hM, hN, hφ⟩
    exact @decideSentence_complete k M hM hN φ hφ

theorem decideValidity_correct {k : ℕ} (φ : (lang k).Sentence) :
    decideValidity φ = true ↔
      ∀ (M : Type) (_ : (lang k).Structure M) (_ : Nonempty M), M ⊨ φ := by
  constructor
  · intro h M hM hN
    by_contra hφ
    have hSat := @decideSentence_complete k M hM hN φ.not
      ((Sentence.realize_not M).mpr hφ)
    simp [decideValidity, hSat] at h
  · intro h
    cases he : decideSentence φ.not with
    | false => simp [decideValidity, he]
    | true =>
      obtain ⟨M, hM, hN, hφ⟩ := (decideSentence_correct φ.not).mp he
      exact False.elim ((Sentence.realize_not M).mp hφ (h M hM hN))

end Lemmatheca.MathematicalLogic.MonadicLogic
