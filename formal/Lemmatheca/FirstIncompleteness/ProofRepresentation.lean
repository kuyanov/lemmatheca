import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentabilityEquivalence
import Lemmatheca.DiagonalLemma.DiagonalLemma

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Arithmetic formulas for genuine finite proof certificates.  The representative
is numeralwise, in the actual seven-axiom theory Q; no uniform internal reflection
or derivability condition is included among the data. -/
namespace Lemmatheca.ProofTheory.FormalizedProvability

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs CodingFormalProofs

noncomputable section

/-- A primitive-recursive checker for the actual theory and a two-sided
numeralwise representative, with proof and sentence coordinates in that order. -/
structure ProofRepresentation (T : language.Theory) where
  check : ℕ → ℕ → Bool
  check_primitive : Primrec₂ check
  check_correct : ∀ σ : language.Sentence,
    (∃ p, check p (sentenceCode arithmeticSignature σ) = true) ↔ Derives T σ
  formula : language.Formula (Fin 2)
  represents : SignedRepresents (fun x => check (x 0) (x 1) = true) formula

/-- Construct a representative for a specified checker, preserving its identity. -/
def representationOfChecker (T : language.Theory) (check : ℕ → ℕ → Bool)
    (hc : Primrec₂ check)
    (hs : ∀ σ : language.Sentence,
      (∃ p, check p (sentenceCode arithmeticSignature σ) = true) ↔ Derives T σ) :
    ProofRepresentation T := by
  have hr : ComputablePred (fun x : Fin 2 → ℕ => check (x 0) (x 1) = true) := by
    apply (Primrec.eq.comp ?_ (Primrec.const true)).computablePred
    exact hc.comp (Primrec.fin_app.comp Primrec.id (Primrec.const 0))
      (Primrec.fin_app.comp Primrec.id (Primrec.const 1))
  let hA := (recursive_relation_iff _).mp hr
  exact ⟨check, hc, hs, Classical.choose hA, Classical.choose_spec hA⟩

@[simp] theorem representationOfChecker_check (T : language.Theory)
    (check : ℕ → ℕ → Bool) (hc : Primrec₂ check)
    (hs : ∀ σ : language.Sentence,
      (∃ p, check p (sentenceCode arithmeticSignature σ) = true) ↔ Derives T σ) :
    (representationOfChecker T check hc hs).check = check := by
  rfl

/-- Use the existing axiom-certificate checker without changing proof codes. -/
def certificateRepresentation (E : ℕ → ℕ → Bool) (hE : Primrec₂ E) :
    ProofRepresentation (theory arithmeticSignature E) :=
  representationOfChecker (theory arithmeticSignature E)
    (certificateCheck arithmeticSignature E)
    (primrec_certificateCheck arithmeticSignature E hE)
    (certificate_iff_derives arithmeticSignature E)

@[simp] theorem certificateRepresentation_check (E : ℕ → ℕ → Bool) (hE : Primrec₂ E) :
    (certificateRepresentation E hE).check = certificateCheck arithmeticSignature E :=
  representationOfChecker_check _ _ _ _

/-- The two numerical coordinates of the proof relation. -/
def proofTuple (p n : ℕ) : Fin 2 → ℕ := ![p, n]

/-- The sentence obtained by substituting a proof code and a sentence code. -/
def proofInstance {T : language.Theory} (P : ProofRepresentation T) (p n : ℕ) :
    language.Sentence := numeralInstance P.formula (proofTuple p n)

/-- Existentially quantify the proof coordinate, leaving the sentence code free. -/
def provabilityFormula {T : language.Theory} (P : ProofRepresentation T) :
    language.Formula Unit :=
  (P.formula.relabel (fun i => if i = 0 then Sum.inr () else Sum.inl ())).iExs Unit

/-- The assertion that the specified sentence has a finite T-proof certificate. -/
def provabilitySentence {T : language.Theory} (P : ProofRepresentation T)
    (σ : language.Sentence) : language.Sentence :=
  numeralInstance (provabilityFormula P) (fun _ => sentenceCode arithmeticSignature σ)

theorem proofInstance_positive {T : language.Theory} (P : ProofRepresentation T)
    (p n : ℕ) (h : P.check p n = true) : Derives Q (proofInstance P p n) := by
  exact (P.represents (proofTuple p n)).1 h

theorem proofInstance_negative {T : language.Theory} (P : ProofRepresentation T)
    (p n : ℕ) (h : P.check p n ≠ true) : Derives Q (proofInstance P p n).not := by
  exact (P.represents (proofTuple p n)).2 h

/-- Every Q-model agrees about the checker at each fixed pair of numerals. -/
theorem proofFormula_numerals {T : language.Theory} (P : ProofRepresentation T)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ Q] (p n : ℕ) :
    P.formula.Realize (fun i => numeralValue M (proofTuple p n i)) ↔
      P.check p n = true := by
  constructor
  · intro hf
    by_contra hn
    have hh : M ⊨ (proofInstance P p n).not :=
      derives_sound (proofInstance_negative P p n hn) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact ((Sentence.realize_not M).mp hh)
      ((realize_numeralInstance P.formula _).mpr hf)
  · intro hp
    have hh : M ⊨ proofInstance P p n :=
      derives_sound (proofInstance_positive P p n hp) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact (realize_numeralInstance P.formula _).mp hh

theorem realize_provabilityFormula {T : language.Theory} (P : ProofRepresentation T)
    {M : Type*} [language.Structure M] (n : M) :
    (provabilityFormula P).Realize (fun _ => n) ↔
      ∃ p : M, P.formula.Realize ![p, n] := by
  simp only [provabilityFormula, Formula.realize_iExs, Formula.realize_relabel,
    Function.comp_def]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p (), ?_⟩
    convert hp using 1
    funext i
    fin_cases i <;> simp
  · rintro ⟨p, hp⟩
    refine ⟨fun _ => p, ?_⟩
    convert hp using 1
    funext i
    fin_cases i <;> simp

/-- Standard-model truth of this predicate is exactly external derivability. -/
theorem provabilitySentence_standard {T : language.Theory} (P : ProofRepresentation T)
    (σ : language.Sentence) :
    ℕ ⊨ provabilitySentence P σ ↔ Derives T σ := by
  let : ℕ ⊨ Q := nat_models_Q
  rw [provabilitySentence, realize_numeralInstance]
  simp only [numeral_value_nat]
  rw [realize_provabilityFormula]
  rw [← P.check_correct σ]
  apply exists_congr
  intro p
  simpa only [numeral_value_nat, proofTuple] using proofFormula_numerals P ℕ p
    (sentenceCode arithmeticSignature σ)

/-- D1: each external proof gives a Q-proof of its own provability instance.
This does not assert a uniform internal implication with a variable proof code. -/
theorem provability_of_derives {T : language.Theory} (P : ProofRepresentation T)
    (σ : language.Sentence) (h : Derives T σ) :
    Derives Q (provabilitySentence P σ) := by
  obtain ⟨p, hp⟩ := (P.check_correct σ).mpr h
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [provabilitySentence, realize_numeralInstance, realize_provabilityFormula]
  refine ⟨numeralValue M p, ?_⟩
  convert (proofFormula_numerals P M p (sentenceCode arithmeticSignature σ)).mpr hp using 1
  funext i
  fin_cases i <;> rfl

theorem derivability_one {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (σ : language.Sentence) (h : Derives T σ) :
    Derives T (provabilitySentence P σ) :=
  derives_mono (provability_of_derives P σ h) hQ

end
end Lemmatheca.ProofTheory.FormalizedProvability
