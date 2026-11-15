import Lemmatheca.HeytingArithmeticAddition.Instances

/-! Witness-oriented order formulas in the original native arithmetic language. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.Order
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
universe u v
variable {α : Type u} {β : Type v}

/-- The fresh distinguished name is the additive witness. -/
def leBody (s t : LA.Term α) : Formula (α ⊕ Unit) :=
  termEqual (addTerm (.var (.inr ())) (s.relabel Sum.inl)) (t.relabel Sum.inl)

/-- The orientation matches the established arithmetic additive-witness convention. -/
def leFormula (s t : LA.Term α) : Formula α := exUnit (leBody s t)

/-- Strict order means that the successor has a non-strict witness. -/
def ltFormula (s t : LA.Term α) : Formula α := leFormula (succTerm s) t

/-- Native biconditional notation abbreviates two proved implications. -/
def iffFormula (A B : Formula α) : Formula α := .conj (.impl A B) (.impl B A)

/-- The alternatives have the association displayed in the entry. -/
def comparison (s t : LA.Term α) : Formula α :=
  .disj (ltFormula s t) (.disj (termEqual s t) (ltFormula t s))

/-- One new induction variable, with the comparison input quantified inside. -/
def comparisonInductionBody : Formula (Fin 0 ⊕ Unit) :=
  allUnit (comparison (.var (.inr ())) (.var (.inl (.inr ()))))

/-- Ordered closure: the first original name is y and the second is x. -/
def comparisonSentence : Sentence :=
  close (comparison (.var (1 : Fin 2)) (.var (0 : Fin 2)))

/-- Closing the one new induction variable yields precisely the displayed sentence. -/
theorem comparison_induction_closure :
    (allUnit comparisonInductionBody).rename (Fin.elim0 : Fin 0 → Empty) =
      comparisonSentence := by
  simp [comparisonInductionBody, comparisonSentence, comparison, ltFormula, leFormula,
    leBody, close, allSlots, allUnit, bindUnit, exUnit,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
    rename, subst, map, Lemmatheca.ProofTheory.FirstOrder.liftScope,
    Lemmatheca.ProofTheory.FirstOrder.scopeInclusion, lastCases_one,
    lastCases_two_zero, lastCases_two_one, freeScope, Term.subst, Term.relabel,
    addTerm, succTerm]

@[simp] theorem leFormula_subst (s t : LA.Term α) (σ : α → LA.Term β) :
    (leFormula s t).subst σ = leFormula (s.subst σ) (t.subst σ) := by
  simp only [leFormula, exUnit_subst]
  congr 1
  simp [leBody, termEqual_subst_poly, add_subst, unitSubst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel]

@[simp] theorem ltFormula_subst (s t : LA.Term α) (σ : α → LA.Term β) :
    (ltFormula s t).subst σ = ltFormula (s.subst σ) (t.subst σ) := by
  simp [ltFormula]


@[simp] theorem leFormula_rename (s t : LA.Term α) (f : α → β) :
    (leFormula s t).rename f = leFormula (s.relabel f) (t.relabel f) := by
  change (leFormula s t).subst (fun a => Term.var (f a)) = _
  rw [leFormula_subst]
  simp only [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]


@[simp] theorem ltFormula_rename (s t : LA.Term α) (f : α → β) :
    (ltFormula s t).rename f = ltFormula (s.relabel f) (t.relabel f) := by
  simp [ltFormula]


/-- Exact small-syntax expansion, without importing the later representability entry. -/
theorem leFormula_toClassical (s t : LA.Term α) :
    (leFormula s t).toClassical =
      ((addTerm (.var (.inr ())) (s.relabel Sum.inl)).equal
        (t.relabel Sum.inl)).iExs Unit := by
  rw [leFormula, exUnit_toClassical]
  rfl


theorem ltFormula_toClassical (s t : LA.Term α) :
    (ltFormula s t).toClassical =
      ((addTerm (.var (.inr ())) ((succTerm s).relabel Sum.inl)).equal
        (t.relabel Sum.inl)).iExs Unit := by
  exact leFormula_toClassical (succTerm s) t


end Lemmatheca.ProofTheory.HeytingArithmetic.Order
