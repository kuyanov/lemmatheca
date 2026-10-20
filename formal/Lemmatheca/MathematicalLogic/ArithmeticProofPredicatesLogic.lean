import Lemmatheca.MathematicalLogic.FormalizedProvability

/-! Logical operations on arithmetic proof predicates.  The hypotheses of the
generic lemmas here are discharged for the chosen actual PA checker in
`ArithmeticProofPredicates`; this file does not assert internal correctness from
standard-model or numeralwise correctness. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticProofPredicates

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

/-- Quantify the proof coordinate of a specified arithmetic formula. No Q
representability assumption is needed merely to form the formula. -/
def provabilityFormula (P : language.Formula (Fin 2)) : language.Formula Unit :=
  (P.relabel (fun i => if i = 0 then Sum.inr () else Sum.inl ())).iExs Unit

def provabilitySentence (P : language.Formula (Fin 2)) (A : language.Sentence) :
    language.Sentence :=
  numeralInstance (provabilityFormula P) (fun _ =>
    CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A)

def consistencySentence (P : language.Formula (Fin 2)) : language.Sentence :=
  (provabilitySentence P ⊥).not

/-- Substitute two arithmetic terms in the two coordinates of a proof formula. -/
def proofAt {α : Type*} (P : language.Formula (Fin 2))
    (p a : language.Term α) : language.Formula α :=
  P.subst ![p, a]

/-- Apply the fixed provability formula to a term in the original language. -/
def provabilityAt {α : Type*} (P : language.Formula (Fin 2))
    (a : language.Term α) : language.Formula α :=
  (provabilityFormula P).subst (fun _ => a)

/-- Interpret the function abbreviation for a numeral-substitution graph.
The extra existential variable is the code of the resulting closed sentence. -/
def boxWithGraph {r : ℕ} (P : language.Formula (Fin 2))
    (sub : language.Formula (Fin r ⊕ Unit)) : language.Formula (Fin r) :=
  (sub ⊓ provabilityAt P (.var (.inr ()))).iExs Unit

theorem realize_proofAt {α : Type*} (P : language.Formula (Fin 2))
    (p a : language.Term α) {M : Type*} [language.Structure M] (v : α → M) :
    (proofAt P p a).Realize v ↔ P.Realize ![p.realize v, a.realize v] := by
  rw [proofAt, Formula.Realize, BoundedFormula.realize_subst]
  change P.Realize (fun i => (![p, a] i).realize v) ↔ _
  have hv : (fun i => (![p, a] i).realize v) = ![p.realize v, a.realize v] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

theorem realize_provabilityFormula (P : language.Formula (Fin 2))
    {M : Type*} [language.Structure M] (n : M) :
    (provabilityFormula P).Realize (fun _ => n) ↔
      ∃ p : M, P.Realize ![p, n] := by
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

theorem realize_provabilityAt {α : Type*} (P : language.Formula (Fin 2))
    (a : language.Term α) {M : Type*} [language.Structure M] (v : α → M) :
    (provabilityAt P a).Realize v ↔
      ∃ p : M, P.Realize ![p, a.realize v] := by
  rw [provabilityAt, Formula.Realize, BoundedFormula.realize_subst]
  exact realize_provabilityFormula P (a.realize v)

theorem realize_boxWithGraph {r : ℕ} (P : language.Formula (Fin 2))
    (sub : language.Formula (Fin r ⊕ Unit)) {M : Type*} [language.Structure M]
    (v : Fin r → M) :
    (boxWithGraph P sub).Realize v ↔
      ∃ a : M, sub.Realize (extend v a) ∧ ∃ p : M, P.Realize ![p, a] := by
  simp only [boxWithGraph, Formula.realize_iExs, Formula.realize_inf,
    realize_provabilityAt, Term.realize_var, Sum.elim_inr]
  constructor
  · rintro ⟨a, hs, hp⟩
    exact ⟨a (), hs, hp⟩
  · rintro ⟨a, hs, hp⟩
    exact ⟨fun _ => a, hs, hp⟩

/-- A literal finite existential prefix over a bounded arithmetic matrix. -/
def SigmaOneSentence (A : language.Sentence) : Prop :=
  ∃ k : ℕ, ∃ D : language.Formula (Empty ⊕ Fin k),
    DeltaZero D ∧ A = D.iExs (Fin k)

/-- The sentence instances of formalized Sigma-one completeness, for a
specified predicate in the actual PA calculus. -/
def ClosedSigmaOneCompleteness (P : language.Formula (Fin 2)) : Prop :=
  ∀ A : language.Sentence, SigmaOneSentence A →
    Derives PA (A.imp (provabilitySentence P A))

/-- A fixed formula's open version, with the numeral-substitution graph
explicit rather than an uninterpreted quotation operation. -/
def ParameterizedCompleteness {r : ℕ} (P : language.Formula (Fin 2))
    (A : language.Formula (Fin r))
    (sub : language.Formula (Fin r ⊕ Unit)) : Prop :=
  Derives PA (close (A.imp (boxWithGraph P sub)))

/-- The actual arithmetic internal equivalence demanded before changing
provability predicates. -/
def predicateComparison (P R : language.Formula (Fin 2)) : language.Sentence :=
  (((provabilityFormula P).iff (provabilityFormula R)).relabel
    (Sum.inr : Unit → Empty ⊕ Unit)).iAlls Unit

theorem predicateComparison_instance (P R : language.Formula (Fin 2))
    (h : Derives PA (predicateComparison P R)) (A : language.Sentence) :
    Derives PA ((provabilitySentence P A).iff (provabilitySentence R A)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  have hh : M ⊨ predicateComparison P R := derives_sound h default
    (fun B hB => Theory.realize_sentence_of_mem PA hB)
  simp only [predicateComparison, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Formula.realize_iff, Function.comp_def,
    Sum.elim_inr] at hh
  rw [Sentence.realize_iff]
  change (M ⊨ numeralInstance (provabilityFormula P) (fun _ =>
    CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A)) ↔
    (M ⊨ numeralInstance (provabilityFormula R) (fun _ =>
      CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A))
  rw [realize_numeralInstance, realize_numeralInstance]
  exact hh (fun _ => numeralValue M
    (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature A))

theorem predicateComparison_consistency (P R : language.Formula (Fin 2))
    (h : Derives PA (predicateComparison P R)) :
    Derives PA ((consistencySentence P).iff (consistencySentence R)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  have hh : M ⊨ (provabilitySentence P ⊥).iff (provabilitySentence R ⊥) :=
    derives_sound (predicateComparison_instance P R h ⊥) default
      (fun B hB => Theory.realize_sentence_of_mem PA hB)
  simpa only [consistencySentence, Sentence.Realize, Formula.realize_iff,
    Formula.realize_not] using not_congr ((Formula.realize_iff).mp hh)

/-- This logical implication is not used as a substitute for proving either
hypothesis for the concrete PA proof predicate. -/
theorem derivabilityThree_of_closedCompleteness (P : language.Formula (Fin 2))
    (hcomplete : ClosedSigmaOneCompleteness P)
    (hcomplexity : ∀ A : language.Sentence,
      SigmaOneSentence (provabilitySentence P A)) :
    ∀ A : language.Sentence, Derives PA
      ((provabilitySentence P A).imp
        (provabilitySentence P (provabilitySentence P A))) := by
  intro A
  exact hcomplete (provabilitySentence P A) (hcomplexity A)

end
end Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
