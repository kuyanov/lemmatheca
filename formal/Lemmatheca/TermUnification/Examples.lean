import Lemmatheca.TermUnification.TermUnification

/-! Explicit witnesses and counterexamples for finite-term unification. -/
namespace Lemmatheca.Entry.TermUnification

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.TermUnification

universe u v w
variable {L : Language.{u, v}}

def constant (a : L.Functions 0) : L.Term ℕ := .func a Fin.elim0

def unary (g : L.Functions 1) (t : L.Term ℕ) : L.Term ℕ := .func g fun _ => t

def binary (f : L.Functions 2) (s t : L.Term ℕ) : L.Term ℕ :=
  .func f fun i => if i = 0 then s else t

@[simp] private theorem constant_subst (a : L.Functions 0) {α : Type w}
    (σ : ℕ → L.Term α) : (constant a).subst σ = .func a Fin.elim0 := by
  simp only [constant, Term.subst]
  congr 1
  funext i
  exact Fin.elim0 i

private theorem binary_args {α : Type w} (f : L.Functions 2)
    (ss ts : Fin 2 → L.Term α) (h : Term.func f ss = Term.func f ts) :
    ss 0 = ts 0 ∧ ss 1 = ts 1 := by
  have he := eq_of_heq (Term.func.inj h).2.2
  exact ⟨congrFun he 0, congrFun he 1⟩

theorem composition_order (g : L.Functions 1) (a : L.Functions 0) :
    compose (single 1 (constant a)) (single 0 (unary g (.var 1))) 0 = unary g (constant a) ∧
    compose (single 0 (unary g (.var 1))) (single 1 (constant a)) 0 = unary g (.var 1) := by
  simp [compose, single, unary, Term.subst]

theorem variable_constant_mgu (a : L.Functions 0) :
    MostGeneral.{u, v, w} [(.var 0, constant a)] (single 0 (constant a)) := by
  have hnil : MostGeneral.{u, v, w} ([] : Problem L) Term.var := by
    refine ⟨by simp [Unifies], ?_⟩
    intro α σ _
    exact ⟨σ, fun _ => rfl⟩
  have h := elimination_most_general 0 (constant a) [] (by simp [constant]) Term.var hnil
  rw [(compose_id (single 0 (constant a))).1] at h
  exact h

theorem binary_constants_forced (f : L.Functions 2) (a b : L.Functions 0)
    {α : Type w} (σ : ℕ → L.Term α)
    (h : Unifies σ [(binary f (.var 0) (constant a), binary f (constant b) (.var 1))]) :
    σ 0 = (.func b Fin.elim0) ∧ σ 1 = (.func a Fin.elim0) := by
  have he := h _ (List.mem_singleton_self _)
  simp only [binary, Term.subst] at he
  have hargs := binary_args f _ _ he
  exact ⟨by simpa [Term.subst] using hargs.1, by simpa [Term.subst] using hargs.2.symm⟩

def workedProblem (f : L.Functions 2) (g : L.Functions 1) (a : L.Functions 0) : Problem L :=
  [(binary f (.var 0) (unary g (.var 1)), binary f (unary g (.var 2)) (.var 3)),
    (.var 2, constant a)]

def workedAnswer (g : L.Functions 1) (a : L.Functions 0) : ℕ → L.Term ℕ
  | 0 => unary g (constant a)
  | 2 => constant a
  | 3 => unary g (.var 1)
  | x => .var x

theorem worked_most_general (f : L.Functions 2) (g : L.Functions 1) (a : L.Functions 0) :
    MostGeneral.{u, v, w} (workedProblem f g a) (workedAnswer g a) := by
  constructor
  · intro e he
    simp [workedProblem] at he
    rcases he with rfl | rfl
    · simp only [binary, Term.subst, unary]
      congr 1
      funext i
      fin_cases i <;> simp [Term.subst, workedAnswer, unary]
    · exact (constant_subst a _).symm
  · intro α σ hσ
    have hfirst := hσ _ (List.mem_cons_self)
    have hsecond := hσ _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have h2 : σ 2 = Term.func a Fin.elim0 := by
      simpa only [Term.subst, constant_subst] using hsecond
    simp only [binary, Term.subst] at hfirst
    obtain ⟨h0, h3⟩ := binary_args f _ _ hfirst
    have he0 : σ 0 = Term.func g (fun _ => Term.func a Fin.elim0) := by
      simpa [unary, Term.subst, h2] using h0
    have he3 : σ 3 = Term.func g (fun _ => σ 1) := by
      simpa [unary, Term.subst] using h3.symm
    refine ⟨σ, ?_⟩
    intro x
    unfold workedAnswer
    split <;> simp_all [unary, Term.subst]


theorem worked_identity_outside (g : L.Functions 1) (a : L.Functions 0) (x : ℕ)
    (hx : x ≠ 0 ∧ x ≠ 2 ∧ x ≠ 3) : workedAnswer g a x = .var x := by
  unfold workedAnswer
  split <;> simp_all

theorem cyclic_no_solution (f : L.Functions 1) {α : Type w} (σ : ℕ → L.Term α) :
    ¬ Unifies σ [(.var 0, unary f (.var 1)), (.var 1, unary f (.var 0))] := by
  intro h
  have h0 := h _ (List.mem_cons_self)
  have h1 := h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  apply occurs_obstruction 1 (unary f (unary f (.var 1))) (by simp [unary])
    (by simp [unary]) σ
  simp only [unary, Term.subst] at h0 h1 ⊢
  rw [h0] at h1
  exact h1

theorem matching_counterexample (f : L.Functions 2) (a : L.Functions 0) :
    (∃ σ : ℕ → L.Term ℕ,
      Unifies σ [(binary f (.var 0) (.var 0), binary f (.var 1) (constant a))]) ∧
    ¬ Matches (binary f (.var 0) (.var 0)) (binary f (.var 1) (constant a)) := by
  constructor
  · refine ⟨fun _ => constant a, ?_⟩
    intro e he
    obtain rfl := List.mem_singleton.mp he
    simp only [binary, Term.subst]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact (constant_subst a (fun _ => constant a)).symm
  · rintro ⟨σ, he⟩
    simp only [binary, Term.subst] at he
    obtain ⟨h0, h1⟩ := binary_args f _ _ he
    have he0 : σ 0 = (.var 1 : L.Term ℕ) := by simpa [Term.subst] using h0
    have he1 : σ 0 = constant a := by simpa [Term.subst] using h1
    have hfalse := he0.symm.trans he1
    cases hfalse

theorem distinct_constants_no_unifier (a b : L.Functions 0) (hab : a ≠ b)
    {α : Type w} (σ : ℕ → L.Term α) : ¬ Unifies σ [(constant a, constant b)] := by
  intro h
  have he := h _ (List.mem_singleton_self _)
  simp only [constant_subst] at he
  exact hab (eq_of_heq (Term.func.inj he).2.1)

/-- The actual one-element structure, regardless of the signature. -/
abbrev singletonStructure : L.Structure PUnit where
  funMap := fun _ _ => PUnit.unit
  RelMap := fun _ _ => True

theorem constants_same_value (a b : L.Functions 0) :
    letI : L.Structure PUnit := singletonStructure
    (constant a).realize (fun _ => PUnit.unit) = (constant b).realize (fun _ => PUnit.unit) := by
  rfl

end Lemmatheca.Entry.TermUnification
