import Lemmatheca.MathematicalLogic.ArithmeticRepresentability
import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityConverse

namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
noncomputable section

/-- Both positive and negative numerical instances have proofs in Q. -/
def SignedRepresents {n : ℕ} (R : (Fin n → ℕ) → Prop)
    (A : language.Formula (Fin n)) : Prop :=
  ∀ x, (R x → Derives Q (numeralInstance A x)) ∧
    (¬ R x → Derives Q (numeralInstance A x).not)

private def indicator {n : ℕ} (R : (Fin n → ℕ) → Prop)
    (x : Fin n → ℕ) : ℕ := by
  classical
  exact if R x then 1 else 0

private def relationGraph {n : ℕ} (A : language.Formula (Fin n)) :
    language.Formula (Fin n ⊕ Unit) :=
  ((A.relabel Sum.inl) ⊓ ((Term.var (.inr ())).equal (numeralTerm 1))) ⊔
    ((A.relabel Sum.inl).not ⊓ ((Term.var (.inr ())).equal (numeralTerm 0)))

private def atOne {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit)) :
    language.Formula (Fin n) :=
  φ.subst (Sum.elim Term.var (fun _ => numeralTerm 1))

private theorem signedRepresents_modelwise {n : ℕ} {R : (Fin n → ℕ) → Prop}
    {A : language.Formula (Fin n)} (h : SignedRepresents R A)
    (M : Theory.ModelType.{0, 0, 0} Q) (x : Fin n → ℕ) :
    A.Realize (fun i => numeralValue M (x i)) ↔ R x := by
  constructor
  · intro ha
    by_contra hn
    have hp : M ⊨ (numeralInstance A x).not :=
      derives_sound ((h x).2 hn) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact ((Sentence.realize_not M).mp hp) ((realize_numeralInstance A x).mpr ha)
  · intro hr
    have hp : M ⊨ numeralInstance A x :=
      derives_sound ((h x).1 hr) default
        (fun B hB => Theory.realize_sentence_of_mem Q hB)
    exact (realize_numeralInstance A x).mp hp

private theorem signedRepresents_of_modelwise {n : ℕ} (R : (Fin n → ℕ) → Prop)
    (A : language.Formula (Fin n))
    (h : ∀ (M : Theory.ModelType.{0, 0, 0} Q) (x : Fin n → ℕ),
      A.Realize (fun i => numeralValue M (x i)) ↔ R x) : SignedRepresents R A := by
  intro x
  constructor
  · intro hr
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    exact (realize_numeralInstance A x).mpr ((h M x).mpr hr)
  · intro hr
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    apply (Sentence.realize_not M).mpr
    intro ha
    exact hr ((h M x).mp ((realize_numeralInstance A x).mp ha))

/-- Decidability is equivalent to two-sided representation in the actual Q calculus. -/
theorem recursive_relation_iff {n : ℕ} (R : (Fin n → ℕ) → Prop) :
    ComputablePred R ↔ ∃ A, SignedRepresents R A := by
  classical
  constructor
  · intro hr
    have hc : Computable (indicator R) := by
      exact (hr.decide.cond (Computable.const (1 : ℕ)) (Computable.const 0)).of_eq
        (fun x => by by_cases hx : R x <;> simp [indicator, hx])
    obtain ⟨φ, hφ⟩ := computable_representable (indicator R)
      (hc.comp Primrec.vector_get'.to_comp)
    refine ⟨atOne φ, signedRepresents_of_modelwise R (atOne φ) ?_⟩
    intro M x
    change (graphAt φ Term.var (numeralTerm 1)).Realize
      (fun i => numeralValue M (x i)) ↔ R x
    rw [realize_graphAt]
    simp only [Term.realize_var, realize_numeralTerm]
    rw [stronglyRepresents_modelwise hφ x (numeralValue M 1),
      (numeral_injective M).eq_iff]
    by_cases hx : R x <;> simp [indicator, hx]
  · rintro ⟨A, hA⟩
    have hi : StronglyRepresents (indicator R) (relationGraph A) := by
      apply stronglyRepresents_of_modelwise
      intro M x y
      simp only [relationGraph, Formula.realize_sup, Formula.realize_inf,
        Formula.realize_not, Formula.realize_relabel, Formula.realize_equal,
        Term.realize_var, realize_numeralTerm, Function.comp_def,
        extend, Sum.elim_inl, Sum.elim_inr]
      rw [signedRepresents_modelwise hA M x]
      by_cases hx : R x <;> simp [indicator, hx]
    have hc := computable_of_stronglyRepresents hi
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun x => indicator R x == 1, Primrec.beq.to_comp.comp hc (Computable.const 1), ?_⟩
    funext x
    apply propext
    by_cases hx : R x <;> simp [indicator, hx]

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
