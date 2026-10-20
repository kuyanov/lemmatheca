import Lemmatheca.MathematicalLogic.FirstIncompletenessBasic
import Lemmatheca.MathematicalLogic.FormalizedProvabilityBasic

/-! Gödel and Rosser sentences are constructed from the same shared arithmetic
syntax, actual proof certificates, and numeralwise Q representations. -/
namespace Lemmatheca.MathematicalLogic.FirstIncompleteness

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs CodingFormalProofs
open DiagonalLemma FormalizedProvability

noncomputable section

/-- Every enumerable actual axiom set has a primitive-recursive certificate
checker and a numeralwise representative in the fixed arithmetic language. -/
theorem exists_proofRepresentation (T : language.Theory)
    (hT : CodeEnumerable arithmeticSignature T) : Nonempty (ProofRepresentation T) := by
  obtain ⟨E, hE, rfl⟩ := enumerable_theory_certificates arithmeticSignature T hT
  exact ⟨certificateRepresentation E hE⟩

/-- Fix an axiom-certificate relation from the effective presentation theorem. -/
def axiomCertificates (T : language.Theory)
    (hT : CodeEnumerable arithmeticSignature T) : ℕ → ℕ → Bool :=
  Classical.choose (enumerable_theory_certificates arithmeticSignature T hT)

theorem axiomCertificates_primitive (T : language.Theory)
    (hT : CodeEnumerable arithmeticSignature T) : Primrec₂ (axiomCertificates T hT) :=
  (Classical.choose_spec (enumerable_theory_certificates arithmeticSignature T hT)).1

theorem axiomCertificates_theory (T : language.Theory)
    (hT : CodeEnumerable arithmeticSignature T) :
    theory arithmeticSignature (axiomCertificates T hT) = T :=
  (Classical.choose_spec (enumerable_theory_certificates arithmeticSignature T hT)).2

/-- Fix the actual certificate checker, retaining its numerical identity. -/
def proofRepresentation (T : language.Theory)
    (hT : CodeEnumerable arithmeticSignature T) : ProofRepresentation T :=
  (axiomCertificates_theory T hT) ▸
    certificateRepresentation (axiomCertificates T hT) (axiomCertificates_primitive T hT)

private theorem transport_check {T U : language.Theory} (P : ProofRepresentation T)
    (h : T = U) : (h ▸ P).check = P.check := by
  cases h
  rfl

theorem proofRepresentation_check (T : language.Theory)
    (hT : CodeEnumerable arithmeticSignature T) :
    (proofRepresentation T hT).check =
      certificateCheck arithmeticSignature (axiomCertificates T hT) := by
  unfold proofRepresentation
  rw [transport_check, certificateRepresentation_check]

private theorem sentence_sound {T : language.Theory} {σ : language.Sentence}
    (h : Derives T σ) (M : Theory.ModelType.{0, 0, 0} T) : M ⊨ σ :=
  Theory.models_sentence_iff.mp (HenkinCompleteness.consequence_iff_derives.mpr h) M

private theorem exists_model {T : language.Theory} (h : Consistent T) :
    Nonempty (Theory.ModelType.{0, 0, 0} T) := by
  obtain ⟨M, hM, hne, _, hmodel⟩ := HenkinCompleteness.countable_model_existence h
  let := hM
  let := hne
  let := hmodel
  exact ⟨Theory.ModelType.of T M⟩

/-- The specified Gödel sentence for the selected proof predicate. -/
def godelSentence {T : language.Theory} (P : ProofRepresentation T) : language.Sentence :=
  fixedPoint (provabilityFormula P).not

theorem godel_equivalence {T : language.Theory} (P : ProofRepresentation T) :
    Derives Q ((godelSentence P).iff (provabilitySentence P (godelSentence P)).not) := by
  exact fixedPoint_equivalence (provabilityFormula P).not

theorem godel_modelwise {T : language.Theory} (P : ProofRepresentation T)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ Q] :
    M ⊨ godelSentence P ↔ ¬ M ⊨ provabilitySentence P (godelSentence P) := by
  exact fixedPoint_modelwise (M := M) (provabilityFormula P).not

/-- Consistency alone prevents a proof of this specified Gödel sentence. -/
theorem godel_unprovable {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (hcon : Consistent T) : ¬ Derives T (godelSentence P) := by
  intro hp
  obtain ⟨M⟩ := exists_model hcon
  let : M ⊨ Q := (inferInstance : M ⊨ T).mono hQ
  have hg := sentence_sound hp M
  have hv := sentence_sound (derivability_one P hQ _ hp) M
  exact (godel_modelwise P M).mp hg hv

/-- Its standard truth follows from consistency and the genuine checker bridge. -/
theorem godel_true {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (hcon : Consistent T) : ℕ ⊨ godelSentence P := by
  let : ℕ ⊨ Q := nat_models_Q
  apply (godel_modelwise P ℕ).mpr
  rw [provabilitySentence_standard]
  exact godel_unprovable P hQ hcon

/-- Fix the sentence-code coordinate and retain the proof code as the free name. -/
def proofAt {T : language.Theory} (P : ProofRepresentation T) (n : ℕ) :
    language.Formula Unit :=
  P.formula.subst (fun i => if i = 0 then .var () else numeralTerm n)

theorem realize_proofAt {T : language.Theory} (P : ProofRepresentation T)
    {M : Type*} [language.Structure M] (n : ℕ) (p : M) :
    (proofAt P n).Realize (fun _ => p) ↔
      P.formula.Realize ![p, numeralValue M n] := by
  simp only [proofAt, Formula.Realize, BoundedFormula.realize_subst]
  apply Iff.of_eq
  congr 1
  funext i
  fin_cases i <;> simp [numeralTerm, numeralValue]
  congr 1
  funext i
  exact i.elim

/-- Omega-consistency rules out the negation of the same specified Gödel sentence. -/
theorem godel_unrefutable {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (hω : OmegaConsistent T) :
    ¬ Derives T (godelSentence P).not := by
  intro hn
  have hnp := godel_unprovable P hQ (omegaConsistent_consistent hω)
  let A := proofAt P (sentenceCode arithmeticSignature (godelSentence P))
  apply hω A
  · intro p
    apply derives_mono (T := Q) (hTU := hQ)
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    apply (Sentence.realize_not M).mpr
    rw [realize_numeralSubstitution, realize_proofAt]
    intro hh
    have hc : P.check p (sentenceCode arithmeticSignature (godelSentence P)) = true := by
      apply (proofFormula_numerals P M p _).mp
      convert hh using 1
      funext i
      fin_cases i <;> rfl
    exact hnp ((P.check_correct _).mp ⟨p, hc⟩)
  · apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    let : M ⊨ Q := (inferInstance : M ⊨ T).mono hQ
    have hng : ¬ M ⊨ godelSentence P := (Sentence.realize_not M).mp (sentence_sound hn M)
    have hv : M ⊨ provabilitySentence P (godelSentence P) := by
      have hh := godel_modelwise P M
      tauto
    rw [provabilitySentence, realize_numeralInstance, realize_provabilityFormula] at hv
    rw [realize_existentialClosure]
    obtain ⟨p, hp⟩ := hv
    exact ⟨p, (realize_proofAt P _ p).mpr hp⟩

private theorem negCode_primitive : Primrec negCode := by
  unfold negCode impCode botCode
  fun_prop

private theorem negativeCheck_computable {T : language.Theory} (P : ProofRepresentation T) :
    ComputablePred (fun x : Fin 2 → ℕ => P.check (x 0) (negCode (x 1)) = true) := by
  apply (Primrec.eq.comp ?_ (Primrec.const true)).computablePred
  exact P.check_primitive.comp
    (Primrec.fin_app.comp Primrec.id (Primrec.const 0))
    (negCode_primitive.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 1)))

/-- Numeralwise representation of a proof of the negation of the input sentence.
The numerical negation operation is the existing code operation, not a new symbol. -/
def negativeProofFormula {T : language.Theory} (P : ProofRepresentation T) :
    language.Formula (Fin 2) :=
  Classical.choose ((recursive_relation_iff _).mp (negativeCheck_computable P))

theorem negativeProofFormula_represents {T : language.Theory} (P : ProofRepresentation T) :
    SignedRepresents (fun x : Fin 2 → ℕ => P.check (x 0) (negCode (x 1)) = true)
      (negativeProofFormula P) :=
  Classical.choose_spec ((recursive_relation_iff _).mp (negativeCheck_computable P))

theorem negativeProofFormula_numerals {T : language.Theory} (P : ProofRepresentation T)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ Q] (p n : ℕ) :
    (negativeProofFormula P).Realize (fun i => numeralValue M (proofTuple p n i)) ↔
      P.check p (negCode n) = true := by
  let h := negativeProofFormula_represents P (proofTuple p n)
  constructor
  · intro hf
    by_contra hn
    have hh : M ⊨ (numeralInstance (negativeProofFormula P) (proofTuple p n)).not :=
      derives_sound (h.2 hn) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact ((Sentence.realize_not M).mp hh)
      ((realize_numeralInstance _ _).mpr hf)
  · intro hp
    have hh : M ⊨ numeralInstance (negativeProofFormula P) (proofTuple p n) :=
      derives_sound (h.1 hp) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact (realize_numeralInstance _ _).mp hh

private def binaryNames {α : Type*} (A : language.Formula (Fin 2)) (p n : α) :
    language.Formula α := A.relabel (fun i => if i = 0 then p else n)

private theorem realize_binaryNames {α M : Type*} [language.Structure M]
    (A : language.Formula (Fin 2)) (p n : α) (v : α → M) :
    (binaryNames A p n).Realize v ↔ A.Realize ![v p, v n] := by
  rw [binaryNames, Formula.realize_relabel]
  have he : v ∘ (fun i : Fin 2 => if i = 0 then p else n) = ![v p, v n] := by
    funext i
    fin_cases i <;> rfl
  rw [he]

/-- A proof of the input sentence is answered by a no-larger proof of its negation. -/
def rosserPredicate {T : language.Theory} (P : ProofRepresentation T) :
    language.Formula Unit :=
  let premise : language.Formula (Unit ⊕ Unit) :=
    binaryNames P.formula (Sum.inr ()) (Sum.inl ())
  let answer : language.Formula ((Unit ⊕ Unit) ⊕ Unit) :=
    (leFormula (.var (.inr ())) (.var (.inl (.inr ())))) ⊓
      binaryNames (negativeProofFormula P) (Sum.inr ()) (Sum.inl (.inl ()))
  (premise.imp (answer.iExs Unit)).iAlls Unit

theorem realize_rosserPredicate {T : language.Theory} (P : ProofRepresentation T)
    {M : Type*} [language.Structure M] (n : M) :
    (rosserPredicate P).Realize (fun _ => n) ↔
      ∀ p : M, P.formula.Realize ![p, n] →
        ∃ q : M, leValue M q p ∧ (negativeProofFormula P).Realize ![q, n] := by
  simp only [rosserPredicate, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_inf, realize_binaryNames,
    realize_leFormula, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h p hp
    obtain ⟨q, hq, hneg⟩ := h (fun _ => p) hp
    exact ⟨q (), hq, hneg⟩
  · intro h p hp
    obtain ⟨q, hq, hneg⟩ := h (p ()) hp
    exact ⟨fun _ => q, hq, hneg⟩

/-- The actual Rosser sentence for this fixed numerical proof ordering. -/
def rosserSentence {T : language.Theory} (P : ProofRepresentation T) : language.Sentence :=
  fixedPoint (rosserPredicate P)

theorem rosser_equivalence {T : language.Theory} (P : ProofRepresentation T) :
    Derives Q ((rosserSentence P).iff
      (numeralSubstitution (rosserPredicate P)
        (sentenceCode arithmeticSignature (rosserSentence P)))) :=
  fixedPoint_equivalence _

theorem rosser_modelwise {T : language.Theory} (P : ProofRepresentation T)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ Q] :
    M ⊨ rosserSentence P ↔
      ∀ p : M, P.formula.Realize ![p, numeralValue M
        (sentenceCode arithmeticSignature (rosserSentence P))] →
        ∃ q : M, leValue M q p ∧ (negativeProofFormula P).Realize
          ![q, numeralValue M (sentenceCode arithmeticSignature (rosserSentence P))] := by
  rw [rosserSentence, fixedPoint_modelwise, realize_numeralSubstitution,
    realize_rosserPredicate]

private theorem no_opposite_proofs {T : language.Theory} (hcon : Consistent T)
    {σ : language.Sentence} (hp : Derives T σ) (hn : Derives T σ.not) : False := by
  obtain ⟨M⟩ := exists_model hcon
  exact (Sentence.realize_not M).mp (sentence_sound hn M) (sentence_sound hp M)

private theorem proof_numeral_pair {T : language.Theory} (P : ProofRepresentation T)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ Q] (p n : ℕ) :
    P.formula.Realize ![numeralValue M p, numeralValue M n] ↔ P.check p n = true := by
  have he : ![numeralValue M p, numeralValue M n] =
      fun i => numeralValue M (proofTuple p n i) := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact proofFormula_numerals P M p n

private theorem negative_numeral_pair {T : language.Theory} (P : ProofRepresentation T)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ Q] (p n : ℕ) :
    (negativeProofFormula P).Realize ![numeralValue M p, numeralValue M n] ↔
      P.check p (negCode n) = true := by
  have he : ![numeralValue M p, numeralValue M n] =
      fun i => numeralValue M (proofTuple p n i) := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact negativeProofFormula_numerals P M p n

/-- The Rosser sentence has no T-proof under consistency alone. -/
theorem rosser_unprovable {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (hcon : Consistent T) : ¬ Derives T (rosserSentence P) := by
  intro hp
  obtain ⟨p, hpc⟩ := (P.check_correct _).mpr hp
  obtain ⟨M⟩ := exists_model hcon
  let : M ⊨ Q := (inferInstance : M ⊨ T).mono hQ
  have hm := (rosser_modelwise P M).mp (sentence_sound hp M)
  obtain ⟨q, hqp, hq⟩ := hm (numeralValue M p)
    ((proof_numeral_pair P M _ _).mpr hpc)
  obtain ⟨k, _, rfl⟩ := (finite_bound q p).mp hqp
  have hqc := (negative_numeral_pair P M k _).mp hq
  rw [negation_code] at hqc
  exact no_opposite_proofs hcon hp ((P.check_correct _).mp ⟨k, hqc⟩)

private theorem succ_add_numeral (M : Type) [language.Structure M] [M ⊨ Q]
    (a : M) (n : ℕ) :
    addValue M (succValue M a) (numeralValue M n) =
      succValue M (addValue M a (numeralValue M n)) := by
  have hQ := (model_Q_iff M).mp ‹M ⊨ Q›
  induction n with
  | zero => simp only [numeral_value_zero, hQ.2.2.2.1]
  | succ n ih => simp only [numeral_value_succ, hQ.2.2.2.2.1, ih]

private theorem numeral_le_of_successor_le (M : Type) [language.Structure M] [M ⊨ Q]
    (a : M) (n : ℕ) (h : leValue M (numeralValue M (n + 1)) a) :
    leValue M (numeralValue M n) a := by
  obtain ⟨z, hz⟩ := h
  have hQ := (model_Q_iff M).mp ‹M ⊨ Q›
  refine ⟨succValue M z, ?_⟩
  rw [succ_add_numeral]
  rw [numeral_value_succ, hQ.2.2.2.2.1] at hz
  exact hz

/-- Its negation also has no T-proof under consistency alone. -/
theorem rosser_unrefutable {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (hcon : Consistent T) : ¬ Derives T (rosserSentence P).not := by
  intro hn
  obtain ⟨q, hqc⟩ := (P.check_correct _).mpr hn
  have hnp := rosser_unprovable P hQ hcon
  have hpQ : Derives Q (rosserSentence P) := by
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    apply (rosser_modelwise P M).mpr
    intro p hp
    rcases numeral_cut p q with ⟨k, _, rfl⟩ | hqp
    · have hpc := (proof_numeral_pair P M k _).mp hp
      exact (hnp ((P.check_correct _).mp ⟨k, hpc⟩)).elim
    · refine ⟨numeralValue M q, numeral_le_of_successor_le M p q hqp, ?_⟩
      apply (negative_numeral_pair P M q _).mpr
      simpa only [negation_code] using hqc
  exact hnp (derives_mono hpQ hQ)

/-- A specified independent sentence for every consistent enumerable extension of Q. -/
theorem first_incompleteness (T : language.Theory) (hQ : Q ⊆ T)
    (he : CodeEnumerable arithmeticSignature T) (hcon : Consistent T) :
    ¬ Derives T (rosserSentence (proofRepresentation T he)) ∧
      ¬ Derives T (rosserSentence (proofRepresentation T he)).not :=
  ⟨rosser_unprovable _ hQ hcon, rosser_unrefutable _ hQ hcon⟩

theorem not_complete (T : language.Theory) (hQ : Q ⊆ T)
    (he : CodeEnumerable arithmeticSignature T) (hcon : Consistent T) :
    ¬ T.IsComplete := by
  intro hc
  have hdec := (Theories.complete_iff_consistent_decides T).mp hc
  have hind := first_incompleteness T hQ he hcon
  exact (hdec.2 _).elim hind.1 hind.2

theorem Q_incomplete :
    ∃ σ : language.Sentence, ¬ Derives Q σ ∧ ¬ Derives Q σ.not :=
  ⟨_, first_incompleteness Q (Set.Subset.refl Q) Q_code_enumerable Q_consistent⟩

end
end Lemmatheca.MathematicalLogic.FirstIncompleteness
