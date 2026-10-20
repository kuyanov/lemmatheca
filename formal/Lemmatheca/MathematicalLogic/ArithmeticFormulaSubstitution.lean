import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityBasic

/-! Exact syntactic substitution laws for bounded arithmetic formulas. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open ArithmeticTheories FirstOrderProofs
noncomputable section

def underSubst {α β γ : Type*} (σ : α → language.Term γ) :
    α ⊕ β → language.Term (γ ⊕ β) :=
  Sum.elim (fun x => (σ x).relabel Sum.inl) (fun y => .var (.inr y))

theorem subst_exs {α β : Type*} {n : ℕ} (φ : language.BoundedFormula α n)
    (σ : α → language.Term β) : φ.exs.subst σ = (φ.subst σ).exs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, formula_subst_ex]

theorem subst_alls {α β : Type*} {n : ℕ} (φ : language.BoundedFormula α n)
    (σ : α → language.Term β) : φ.alls.subst σ = (φ.subst σ).alls := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BoundedFormula.alls, ih, formula_subst_all]

theorem subst_iExs {α β γ : Type*} [Finite β]
    (φ : language.Formula (α ⊕ β)) (σ : α → language.Term γ) :
    (φ.iExs β).subst σ = Formula.iExs β (φ.subst (underSubst σ)) := by
  unfold Formula.iExs
  rw [subst_exs]
  apply congrArg BoundedFormula.exs
  symm
  apply relabel_subst_comm
  intro x
  cases x <;> simp [underSubst, liftSubst,
    Term.relabel_relabel, Function.comp_def]

theorem subst_iAlls {α β γ : Type*} [Finite β]
    (φ : language.Formula (α ⊕ β)) (σ : α → language.Term γ) :
    (φ.iAlls β).subst σ = Formula.iAlls β (φ.subst (underSubst σ)) := by
  unfold Formula.iAlls
  rw [subst_alls]
  apply congrArg BoundedFormula.alls
  symm
  apply relabel_subst_comm
  intro x
  cases x <;> simp [underSubst, liftSubst,
    Term.relabel_relabel, Function.comp_def]

@[simp] theorem subst_zeroTerm {α β : Type*} (σ : α → language.Term β) :
    (zeroTerm : language.Term α).subst σ = zeroTerm := by
  simp only [zeroTerm, Term.subst]
  congr 1
  funext i
  exact i.elim0

@[simp] theorem subst_addTerm {α β : Type*} (σ : α → language.Term β)
    (s t : language.Term α) :
    (addTerm s t).subst σ = addTerm (s.subst σ) (t.subst σ) := by
  simp only [addTerm, Term.subst]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_succTerm {α β : Type*} (σ : α → language.Term β)
    (t : language.Term α) : (succTerm t).subst σ = succTerm (t.subst σ) := rfl

@[simp] theorem subst_leFormula {α β : Type*} (σ : α → language.Term β)
    (s t : language.Term α) :
    (leFormula s t).subst σ = leFormula (s.subst σ) (t.subst σ) := by
  unfold leFormula
  rw [subst_iExs]
  congr 1
  simp only [formula_subst_equal, subst_addTerm, Term.subst, underSubst, Sum.elim_inr,
    term_subst_relabel, Sum.elim_inl, term_relabel_subst]

@[simp] theorem subst_boundedAll {α β : Type*} (σ : α → language.Term β)
    (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (boundedAll t φ).subst σ = boundedAll (t.subst σ) (φ.subst (underSubst σ)) := by
  unfold boundedAll
  rw [subst_iAlls]
  congr 1
  simp only [formula_subst_imp, subst_leFormula, Term.subst, underSubst, Sum.elim_inr,
    term_subst_relabel, Sum.elim_inl, term_relabel_subst]

@[simp] theorem subst_boundedEx {α β : Type*} (σ : α → language.Term β)
    (t : language.Term α) (φ : language.Formula (α ⊕ Unit)) :
    (boundedEx t φ).subst σ = boundedEx (t.subst σ) (φ.subst (underSubst σ)) := by
  unfold boundedEx
  rw [subst_iExs]
  congr 1
  simp only [formula_subst_inf, subst_leFormula, Term.subst, underSubst, Sum.elim_inr,
    term_subst_relabel, Sum.elim_inl, term_relabel_subst]

theorem DeltaZero.subst {α β : Type} {φ : language.Formula α} (h : DeltaZero φ)
    (σ : α → language.Term β) : DeltaZero (φ.subst σ) := by
  induction h generalizing β with
  | falsum => exact .falsum
  | equal s t => simpa only [formula_subst_equal] using DeltaZero.equal (s.subst σ) (t.subst σ)
  | le s t => simpa only [subst_leFormula] using DeltaZero.le (s.subst σ) (t.subst σ)
  | imp hφ hψ ihφ ihψ => exact .imp (ihφ σ) (ihψ σ)
  | all t hφ ih => simpa only [subst_boundedAll] using DeltaZero.all (t.subst σ) (ih (underSubst σ))
  | ex t hφ ih => simpa only [subst_boundedEx] using DeltaZero.ex (t.subst σ) (ih (underSubst σ))

theorem DeltaZero.relabel {α β : Type} {φ : language.Formula α} (h : DeltaZero φ)
    (f : α → β) : DeltaZero (φ.relabel f) := by
  rw [← formula_subst_vars]
  exact h.subst (fun x => .var (f x))

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
