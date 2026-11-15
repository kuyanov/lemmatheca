import Lemmatheca.HeytingArithmeticOrder.Syntax

/-! Full native predicates, cumulative histories and finite internal search. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.Lemmatheca.ProofTheory.HeytingArithmetic.Order
universe u v
variable {α : Type u} {β : Type v}

/-- Instantiate the one distinguished predicate input at the specified term. -/
def atTerm (A : Formula (α ⊕ Unit)) (t : LA.Term α) : Formula α :=
  A.subst (Sum.elim Term.var (fun _ => t))

/-- Rename parameters while retaining the separate distinguished predicate input. -/
def parameterRename (A : Formula (α ⊕ Unit)) (f : α → β) : Formula (β ⊕ Unit) :=
  A.rename (Sum.map f id)

/-- The complete positive history strictly below the supplied bound. -/
def history (A : Formula (α ⊕ Unit)) (n : LA.Term α) : Formula α :=
  allUnit (.impl (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A)

/-- The complete negative history strictly below the supplied bound. -/
def negativeHistory (A : Formula (α ⊕ Unit)) (n : LA.Term α) : Formula α :=
  history (.neg A) n

/-- The positive witness together with all strictly smaller negative instances. -/
def minimum (A : Formula (α ⊕ Unit)) (m : LA.Term α) : Formula α :=
  .conj (atTerm A m) (negativeHistory A m)

/-- The actual cumulative body used by ordinary HA induction. -/
def historyInductionBody (A : Formula (α ⊕ Unit)) : Formula (α ⊕ Unit) :=
  history (parameterRename A Sum.inl) (.var (.inr ()))

/-- At every input, its complete positive history implies the original predicate. -/
def completePremise (A : Formula (α ⊕ Unit)) : Formula α :=
  allUnit (.impl (historyInductionBody A) A)

/-- A supplied internal decision at every predicate input. -/
def predicateDecision (A : Formula (α ⊕ Unit)) : Formula α :=
  allUnit (.disj A (.neg A))

/-- The minimum formula with its proposed minimum still a distinguished name. -/
def minimumBody (A : Formula (α ⊕ Unit)) : Formula (α ⊕ Unit) :=
  minimum (parameterRename A Sum.inl) (.var (.inr ()))

/-- Native existence of a least witnessed input. -/
def minimumExists (A : Formula (α ⊕ Unit)) : Formula α := exUnit (minimumBody A)

/-- Either the strict interval is empty of A, or it contains a globally least A. -/
def finiteSearch (A : Formula (α ⊕ Unit)) (n : LA.Term α) : Formula α :=
  .disj (negativeHistory A n)
    (exUnit (.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) (minimumBody A)))

/-- The actual search body for ordinary induction on its bound. -/
def searchInductionBody (A : Formula (α ⊕ Unit)) : Formula (α ⊕ Unit) :=
  finiteSearch (parameterRename A Sum.inl) (.var (.inr ()))

/-- The specified full predicate for the least-number to excluded-middle reduction. -/
def excludedMiddlePredicate (B : Formula α) : Formula (α ⊕ Unit) :=
  .disj (.conj (termEqual (.var (.inr ())) zeroTerm) (B.rename Sum.inl))
    (termEqual (.var (.inr ())) (succTerm zeroTerm))


/-- Repeated parameter renaming is the literal composed name map. -/
theorem parameterRename_comp {γ : Type*} (A : Formula (α ⊕ Unit)) (f : α → β) (g : β → γ) :
    parameterRename (parameterRename A f) g = parameterRename A (g ∘ f) := by
  unfold parameterRename
  rw [rename_comp]
  congr 1
  funext x
  cases x <;> rfl

theorem parameterRename_id (A : Formula (α ⊕ Unit)) : parameterRename A id = A := by
  unfold parameterRename
  have he : Sum.map (id : α → α) (id : Unit → Unit) = id := by
    funext x
    cases x <;> rfl
  rw [he, rename_id]

private theorem parameterRename_as_subst (A : Formula (α ⊕ Unit)) (f : α → β) :
    parameterRename A f = A.subst (unitSubst (fun a => Term.var (f a))) := by
  unfold parameterRename Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr x => cases x; rfl

private theorem parameterRename_subst {γ : Type*} (A : Formula (α ⊕ Unit))
    (f : α → β) (σ : β → LA.Term γ) :
    (parameterRename A f).subst (unitSubst σ) =
      A.subst (unitSubst (fun a => σ (f a))) := by
  unfold parameterRename
  rw [formula_rename_subst_poly]
  congr 1
  funext x
  cases x <;> rfl

private theorem parameterRename_lift_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (parameterRename A (Sum.inl : α → α ⊕ Unit)).subst (unitSubst (unitSubst σ)) =
      parameterRename (A.subst (unitSubst σ)) Sum.inl := by
  rw [parameterRename_subst]
  unfold parameterRename
  rw [formula_subst_rename_poly]
  congr 1
  funext x
  cases x with
  | inl a =>
    simp [unitSubst, Term.relabel_relabel, Function.comp_def]
  | inr x => rfl

private theorem parameterRename_instance_subst (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    (parameterRename A (Sum.inl : α → α ⊕ Unit)).subst
        (unitSubst (Sum.elim Term.var (fun _ => t))) = A := by
  rw [parameterRename_subst]
  have he : unitSubst (fun a : α => Sum.elim Term.var (fun _ : Unit => t) (Sum.inl a)) = Term.var := by
    funext x
    cases x with
    | inl a => rfl
    | inr x => cases x; rfl
  rw [he, subst_id]

/-- Opening the separate input at the protected parameter gives the exact Fin1 renaming. -/
theorem atTerm_parameterRename_open (A : Formula (α ⊕ Unit)) :
    atTerm (parameterRename A (Sum.inl : α → α ⊕ Fin 1)) (.var (.inr (0 : Fin 1))) =
      A.rename (Sum.map id (fun _ => (0 : Fin 1))) := by
  unfold atTerm parameterRename
  rw [formula_rename_subst_poly]
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  congr 1
  funext x
  cases x <;> rfl

/-- Literal capture-free substitution for predicate parameters and its input. -/
theorem atTerm_subst (A : Formula (α ⊕ Unit)) (t : LA.Term α) (σ : α → LA.Term β) :
    (atTerm A t).subst σ = atTerm (A.subst (unitSubst σ)) (t.subst σ) := by
  unfold atTerm
  rw [subst_comp, subst_comp]
  congr 1
  funext x
  cases x with
  | inl a =>
    simp [unitSubst, Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel, Term.subst]
  | inr x => rfl

theorem atTerm_rename (A : Formula (α ⊕ Unit)) (t : LA.Term α) (f : α → β) :
    (atTerm A t).rename f = atTerm (parameterRename A f) (t.relabel f) := by
  change (atTerm A t).subst (fun a => Term.var (f a)) = _
  rw [atTerm_subst, ← parameterRename_as_subst]
  simp only [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]

theorem history_subst (A : Formula (α ⊕ Unit)) (n : LA.Term α) (σ : α → LA.Term β) :
    (history A n).subst σ = history (A.subst (unitSubst σ)) (n.subst σ) := by
  simp [history, allUnit_subst, subst_impl, unitSubst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_relabel_subst, Term.subst]

theorem history_rename (A : Formula (α ⊕ Unit)) (n : LA.Term α) (f : α → β) :
    (history A n).rename f = history (parameterRename A f) (n.relabel f) := by
  change (history A n).subst (fun a => Term.var (f a)) = _
  rw [history_subst, ← parameterRename_as_subst]
  simp only [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]

theorem negativeHistory_subst (A : Formula (α ⊕ Unit)) (n : LA.Term α) (σ : α → LA.Term β) :
    (negativeHistory A n).subst σ = negativeHistory (A.subst (unitSubst σ)) (n.subst σ) := by
  simp only [negativeHistory, history_subst, subst_neg]

theorem negativeHistory_rename (A : Formula (α ⊕ Unit)) (n : LA.Term α) (f : α → β) :
    (negativeHistory A n).rename f = negativeHistory (parameterRename A f) (n.relabel f) := by
  change (negativeHistory A n).subst (fun a => Term.var (f a)) = _
  rw [negativeHistory_subst, ← parameterRename_as_subst]
  simp only [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]

theorem minimum_subst (A : Formula (α ⊕ Unit)) (m : LA.Term α) (σ : α → LA.Term β) :
    (minimum A m).subst σ = minimum (A.subst (unitSubst σ)) (m.subst σ) := by
  simp only [minimum, subst_conj, atTerm_subst, negativeHistory_subst]

theorem minimum_rename (A : Formula (α ⊕ Unit)) (m : LA.Term α) (f : α → β) :
    (minimum A m).rename f = minimum (parameterRename A f) (m.relabel f) := by
  change (minimum A m).subst (fun a => Term.var (f a)) = _
  rw [minimum_subst, ← parameterRename_as_subst]
  simp only [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]

theorem completePremise_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (completePremise A).subst σ = completePremise (A.subst (unitSubst σ)) := by
  unfold completePremise
  rw [allUnit_subst, subst_impl]
  congr 2
  unfold historyInductionBody
  rw [history_subst, parameterRename_lift_subst]
  rfl

theorem completePremise_rename (A : Formula (α ⊕ Unit)) (f : α → β) :
    (completePremise A).rename f = completePremise (parameterRename A f) := by
  change (completePremise A).subst (fun a => Term.var (f a)) = _
  rw [completePremise_subst, ← parameterRename_as_subst]

theorem predicateDecision_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (predicateDecision A).subst σ = predicateDecision (A.subst (unitSubst σ)) := by
  simp only [predicateDecision, allUnit_subst, subst_disj, subst_neg]

theorem predicateDecision_rename (A : Formula (α ⊕ Unit)) (f : α → β) :
    (predicateDecision A).rename f = predicateDecision (parameterRename A f) := by
  change (predicateDecision A).subst (fun a => Term.var (f a)) = _
  rw [predicateDecision_subst, ← parameterRename_as_subst]

theorem minimumExists_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (minimumExists A).subst σ = minimumExists (A.subst (unitSubst σ)) := by
  unfold minimumExists
  rw [exUnit_subst]
  congr 1
  unfold minimumBody
  rw [minimum_subst, parameterRename_lift_subst]
  rfl

theorem minimumExists_rename (A : Formula (α ⊕ Unit)) (f : α → β) :
    (minimumExists A).rename f = minimumExists (parameterRename A f) := by
  change (minimumExists A).subst (fun a => Term.var (f a)) = _
  rw [minimumExists_subst, ← parameterRename_as_subst]

theorem finiteSearch_subst (A : Formula (α ⊕ Unit)) (n : LA.Term α) (σ : α → LA.Term β) :
    (finiteSearch A n).subst σ = finiteSearch (A.subst (unitSubst σ)) (n.subst σ) := by
  unfold finiteSearch
  rw [subst_disj, negativeHistory_subst, exUnit_subst, subst_conj]
  congr 2
  simp only [ltFormula_subst]
  congr 1
  · simp [unitSubst, Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel,
      Lemmatheca.MathematicalLogic.FirstOrderProofs.term_relabel_subst, Term.subst]
  · unfold minimumBody
    rw [minimum_subst, parameterRename_lift_subst]
    rfl

theorem finiteSearch_rename (A : Formula (α ⊕ Unit)) (n : LA.Term α) (f : α → β) :
    (finiteSearch A n).rename f = finiteSearch (parameterRename A f) (n.relabel f) := by
  change (finiteSearch A n).subst (fun a => Term.var (f a)) = _
  rw [finiteSearch_subst, ← parameterRename_as_subst]
  simp only [Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_vars]

/-- The minimum existential's literal body has the stated supplied term instance. -/
theorem minimumBody_instance (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    atTerm (minimumBody A) t = minimum A t := by
  unfold atTerm minimumBody
  rw [minimum_subst, parameterRename_instance_subst]
  rfl

/-- Match the ordinary induction base, successor substitution and protected opening. -/
theorem historyInductionBody_base {k} (A : Formula (Fin k ⊕ Unit)) :
    base (historyInductionBody A) = history A zeroTerm := by
  change atTerm (historyInductionBody A) zeroTerm = _
  unfold atTerm historyInductionBody
  rw [history_subst, parameterRename_instance_subst]
  rfl

theorem historyInductionBody_next {k} (A : Formula (Fin k ⊕ Unit)) :
    next (historyInductionBody A) =
      history (parameterRename A Sum.inl) (succTerm (.var (.inr ()))) := by
  unfold next historyInductionBody
  rw [history_subst, parameterRename_subst]
  simp only [Term.subst, Sum.elim_inl, Sum.elim_inr]
  rw [← parameterRename_as_subst]

theorem historyInductionBody_open (A : Formula (α ⊕ Unit)) :
    (historyInductionBody A).rename (Sum.map id (fun _ => (0 : Fin 1))) =
      history (parameterRename A Sum.inl) (.var (.inr (0 : Fin 1))) := by
  unfold historyInductionBody
  rw [history_rename, parameterRename_comp]
  rfl

theorem historyInductionBody_instance (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    atTerm (historyInductionBody A) t = history A t := by
  unfold atTerm historyInductionBody
  rw [history_subst, parameterRename_instance_subst]
  rfl

theorem searchInductionBody_base {k} (A : Formula (Fin k ⊕ Unit)) :
    base (searchInductionBody A) = finiteSearch A zeroTerm := by
  change atTerm (searchInductionBody A) zeroTerm = _
  unfold atTerm searchInductionBody
  rw [finiteSearch_subst, parameterRename_instance_subst]
  rfl

theorem searchInductionBody_next {k} (A : Formula (Fin k ⊕ Unit)) :
    next (searchInductionBody A) =
      finiteSearch (parameterRename A Sum.inl) (succTerm (.var (.inr ()))) := by
  unfold next searchInductionBody
  rw [finiteSearch_subst, parameterRename_subst]
  simp only [Term.subst, Sum.elim_inl, Sum.elim_inr]
  rw [← parameterRename_as_subst]

theorem searchInductionBody_open (A : Formula (α ⊕ Unit)) :
    (searchInductionBody A).rename (Sum.map id (fun _ => (0 : Fin 1))) =
      finiteSearch (parameterRename A Sum.inl) (.var (.inr (0 : Fin 1))) := by
  unfold searchInductionBody
  rw [finiteSearch_rename, parameterRename_comp]
  rfl

theorem searchInductionBody_instance (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    atTerm (searchInductionBody A) t = finiteSearch A t := by
  unfold atTerm searchInductionBody
  rw [finiteSearch_subst, parameterRename_instance_subst]
  rfl

end Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
