import Lemmatheca.PaDegrees.Basic
import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityEquivalence
import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityCuts

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ProofTheory
open ArithmeticTheories FirstOrderProofs CodingFormalProofs ArithmeticRepresentability Theories
open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc
open ComputableSeparation BusyBeaverFunctions

noncomputable section

def outputCertificate (i : ℕ) (x : Fin 2 → ℕ) : Prop :=
  boundedValue (x 1) (x 0) (x 0) = i + 1

theorem output_certificate_primitive (i : ℕ) : PrimrecPred (outputCertificate i) := by
  have he : Primrec (fun x : Fin 2 → ℕ => x 0) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const 0)
  have hs : Primrec (fun x : Fin 2 → ℕ => x 1) :=
    Primrec.fin_app.comp Primrec.id (Primrec.const 1)
  exact Primrec.eq.comp (boundedValue_primitive.comp ((hs.pair he).pair he))
    (Primrec.const (i + 1))

private theorem output_certificate_computable (i : ℕ) : ComputablePred (outputCertificate i) := by
  classical
  exact (output_certificate_primitive i).decide.to_comp.computablePred

def certificateFormula (i : ℕ) : language.Formula (Fin 2) :=
  Classical.choose ((recursive_relation_iff (outputCertificate i)).mp
    (output_certificate_computable i))

theorem certificate_formula_signed (i : ℕ) :
    SignedRepresents (outputCertificate i) (certificateFormula i) := by
  exact Classical.choose_spec ((recursive_relation_iff (outputCertificate i)).mp
    (output_certificate_computable i))

def binaryFormulaAt {α : Type*} (R : language.Formula (Fin 2))
    (a b : language.Term α) : language.Formula α :=
  R.subst (fun i => if i = 0 then a else b)

/-- The parameter is the outer Unit name; each quantified Unit name is distinct. -/
def comparisonFormula : language.Formula Unit :=
  ((binaryFormulaAt (certificateFormula 0) (.var (.inl ())) (.var (.inr ()))) ⊓
    boundedAll (.var (.inr ()))
      (binaryFormulaAt (certificateFormula 1)
        (.var (.inl (.inl ()))) (.var (.inr ()))).not).iExs Unit

def comparisonSentence (e : ℕ) : language.Sentence :=
  numeralInstance comparisonFormula (fun _ => e)

def comparisonCode (e : ℕ) : ℕ :=
  sentenceCode arithmeticSignature (comparisonSentence e)

private theorem binary_formula_at_realize {α M : Type*} [language.Structure M]
    (R : language.Formula (Fin 2)) (a b : language.Term α) (v : α → M) :
    (binaryFormulaAt R a b).Realize v ↔ R.Realize ![a.realize v, b.realize v] := by
  simp only [binaryFormulaAt, Formula.Realize, BoundedFormula.realize_subst]
  have he : (fun i : Fin 2 => (if i = 0 then a else b).realize v) =
      ![a.realize v, b.realize v] := by
    funext i
    fin_cases i <;> simp
  rw [he]

theorem comparison_formula_realize (M : Type*) [language.Structure M] (e : M) :
    comparisonFormula.Realize (fun _ => e) ↔
      ∃ s : M, (certificateFormula 0).Realize ![e, s] ∧
        ∀ t : M, leValue M t s → ¬ (certificateFormula 1).Realize ![e, t] := by
  simp only [comparisonFormula, Formula.realize_iExs, Formula.realize_inf,
    binary_formula_at_realize, realize_boundedAll, Formula.realize_not,
    Term.realize_var, Sum.elim_inl, Sum.elim_inr, extend]
  constructor
  · rintro ⟨s, h0, h1⟩
    exact ⟨s (), h0, h1⟩
  · rintro ⟨s, h0, h1⟩
    exact ⟨fun _ => s, h0, h1⟩

theorem certificate_formula_numerals (i : ℕ) (M : Type*) [language.Structure M]
    [Nonempty M] [M ⊨ Q] (e s : ℕ) :
    (certificateFormula i).Realize ![numeralValue M e, numeralValue M s] ↔
      boundedValue s e e = i + 1 := by
  have htuple : (fun j : Fin 2 => numeralValue M (![e, s] j)) =
      ![numeralValue M e, numeralValue M s] := by
    funext j
    fin_cases j <;> rfl
  rw [← htuple, ← realize_numeralInstance]
  constructor
  · intro h
    by_contra hn
    have hp := (certificate_formula_signed i ![e, s]).2 hn
    have hm : M ⊨ (numeralInstance (certificateFormula i) ![e, s]).not :=
      derives_sound hp (default : Empty → M) (fun B hB => Theory.realize_sentence_of_mem (M := M) Q hB)
    exact ((Sentence.realize_not M).mp hm) h
  · intro h
    exact derives_sound ((certificate_formula_signed i ![e, s]).1 h) (default : Empty → M)
      (fun B hB => Theory.realize_sentence_of_mem (M := M) Q hB)

theorem comparison_code_primitive : Primrec comparisonCode := by
  exact numeralInstance_code_primrec comparisonFormula (fun e _ => e) (fun _ => Primrec.id)

theorem comparison_positive (e : ℕ) (he : e ∈ diagonalOutput 0) :
    Derives Q (comparisonSentence e) := by
  obtain ⟨s, hs⟩ := (phi_output e e 0).mp he
  apply Lemmatheca.MathematicalLogic.HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [comparisonSentence, realize_numeralInstance, comparison_formula_realize]
  refine ⟨numeralValue M s, (certificate_formula_numerals 0 M e s).mpr hs, ?_⟩
  intro t ht
  obtain ⟨j, _, rfl⟩ := (finite_bound t s).mp ht
  rw [certificate_formula_numerals 1 M e j]
  intro hj
  have h1 : 1 ∈ phi e e := (phi_output e e 1).mpr ⟨j, hj⟩
  exact Nat.zero_ne_one (Part.mem_unique he h1)

theorem comparison_negative (e : ℕ) (he : e ∈ diagonalOutput 1) :
    Derives Q (comparisonSentence e).not := by
  obtain ⟨t, ht⟩ := (phi_output e e 1).mp he
  apply Lemmatheca.MathematicalLogic.HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  apply (Sentence.realize_not M).mpr
  rw [comparisonSentence, realize_numeralInstance, comparison_formula_realize]
  rintro ⟨s, h0, h1⟩
  have hneg (j : ℕ) : ¬ (certificateFormula 0).Realize
      ![numeralValue M e, numeralValue M j] := by
    rw [certificate_formula_numerals 0 M e j]
    intro hj
    have h0' : 0 ∈ phi e e := (phi_output e e 0).mpr ⟨j, hj⟩
    exact Nat.zero_ne_one (Part.mem_unique h0' he)
  have hpos := (certificate_formula_numerals 1 M e t).mpr ht
  cases t with
  | zero =>
    have hle : leValue M (numeralValue M 0) s :=
      ⟨s, by rw [numeral_value_zero]; exact ((model_Q_iff M).mp inferInstance).2.2.2.1 s⟩
    exact h1 (numeralValue M 0) hle hpos
  | succ k =>
    rcases numeral_cut s k with ⟨j, _, rfl⟩ | hle
    · exact hneg j h0
    · exact h1 (numeralValue M (k + 1)) hle hpos

def completionDNC (T : language.Theory) : Set ℕ :=
  {e | comparisonCode e ∈ completionCodes T}

def completionDNCCode : OracleComputation.Code :=
  .comp .query (embed (ordinaryProgram comparisonCode comparison_code_primitive.to_comp))

theorem completion_dnc_code_eval (T : language.Theory) (e : ℕ) :
    eval (completionCodes T) completionDNCCode e =
      Part.some (indicator (fun n => n ∈ completionDNC T) e) := by
  classical
  simp only [completionDNCCode, eval, eval_embed, ordinaryProgram_eval, Part.bind_some]
  rfl

/-- Completeness is unnecessary for the separator argument, including the question. -/
theorem consistent_Q_extension_dnc (T : language.Theory) (hQ : Q ⊆ T)
    (hcon : Consistent T) (hclosed : IsDeductivelyClosed T) :
    completionDNC T ∈ binaryDNCClass := by
  classical
  apply (dnc_iff_separator (completionDNC T)).mpr
  constructor
  · intro e he
    change comparisonCode e ∈ completionCodes T
    rw [comparisonCode, completion_codes_sentence, ← hclosed]
    exact (mem_closure_iff_derives T _).mpr (derives_mono (comparison_positive e he) hQ)
  · apply Set.disjoint_left.mpr
    intro e hD he
    have hp : Derives T (comparisonSentence e) :=
      derives_assumption ((completion_codes_sentence T _).mp hD)
    have hn : Derives T (comparisonSentence e).not := derives_mono (comparison_negative e he) hQ
    rcases hp with ⟨Γ, hΓ, hp⟩
    rcases hn with ⟨Δ, hΔ, hn⟩
    apply hcon
    refine ⟨Γ ∪ Δ, ?_, .negElim (.weakening hp Finset.subset_union_left)
      (.weakening hn Finset.subset_union_right)⟩
    intro A hA
    exact (Finset.mem_union.mp hA).elim (fun h => hΓ h) (fun h => hΔ h)

end
end Lemmatheca.ComputabilityTheory.PaDegrees
