import Lemmatheca.FirstOrderProofs.FirstOrderProofSyntax
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! Finite syntactic unification on the corpus's shared first-order terms. -/
namespace Lemmatheca.MathematicalLogic.TermUnification

open FirstOrder FirstOrder.Language
open scoped BigOperators

universe u v w w' w''
variable {L : Language.{u, v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- Apply the second argument first, then the first argument. -/
def compose (τ : β → L.Term γ) (σ : α → L.Term β) : α → L.Term γ :=
  fun x => (σ x).subst τ

/-- Replace one natural-number variable, fixing all other variables. -/
def single (x : ℕ) (t : L.Term ℕ) : ℕ → L.Term ℕ :=
  fun y => if y = x then t else .var y

theorem compose_assoc {δ : Type*} (υ : γ → L.Term δ) (τ : β → L.Term γ)
    (σ : α → L.Term β) : compose υ (compose τ σ) = compose (compose υ τ) σ := by
  funext x
  exact FirstOrderProofs.term_subst_subst (σ x) τ υ

theorem compose_id (σ : α → L.Term β) :
    compose Term.var σ = σ ∧ compose σ Term.var = σ := by
  constructor
  · funext x
    exact FirstOrderProofs.term_subst_var (σ x)
  · rfl

/-- Finite equations between actual shared terms. -/
abbrev Problem (L : Language.{u, v}) := List (L.Term ℕ × L.Term ℕ)

/-- Syntactic equality after simultaneous substitution. -/
def Unifies (σ : ℕ → L.Term α) (P : Problem L) : Prop :=
  ∀ e ∈ P, e.1.subst σ = e.2.subst σ

/-- Exact all-variable factorization; the residual alphabet is arbitrary. -/
def Factors (σ : ℕ → L.Term α) (μ : ℕ → L.Term ℕ) : Prop :=
  ∃ ρ : ℕ → L.Term α, ∀ x, (μ x).subst ρ = σ x

/-- A most general unifier, allowing residual variables in any target alphabet. -/
def MostGeneral (P : Problem L) (μ : ℕ → L.Term ℕ) : Prop :=
  Unifies μ P ∧ ∀ (α : Type w) (σ : ℕ → L.Term α), Unifies σ P → Factors σ μ

/-- Apply a substitution to both sides of every equation. -/
def substProblem (σ : ℕ → L.Term ℕ) (P : Problem L) : Problem L :=
  P.map fun e => (e.1.subst σ, e.2.subst σ)

/-- All variables occurring in a finite problem. -/
def problemVars : Problem L → Finset ℕ
  | [] => ∅
  | (s, t) :: R => s.varFinset ∪ t.varFinset ∪ problemVars R

/-- Number of constructor occurrences, counting each variable as one node. -/
def nodeCount : L.Term α → ℕ
  | .var _ => 1
  | .func _ ts => 1 + ∑ i, nodeCount (ts i)

/-- Total term-node count in the equation list. -/
def problemSize : Problem L → ℕ
  | [] => 0
  | (s, t) :: R => nodeCount s + nodeCount t + problemSize R

/-- An allowed set contains every input variable. -/
def Supported (V : Finset ℕ) (P : Problem L) : Prop := problemVars P ⊆ V

@[simp] private theorem unifies_nil (σ : ℕ → L.Term α) : Unifies σ [] := by
  simp [Unifies]

@[simp] private theorem unifies_cons (σ : ℕ → L.Term α) (s t : L.Term ℕ)
    (R : Problem L) :
    Unifies σ ((s, t) :: R) ↔ s.subst σ = t.subst σ ∧ Unifies σ R := by
  simp [Unifies]

@[simp] private theorem unifies_append (σ : ℕ → L.Term α) (P Q : Problem L) :
    Unifies σ (P ++ Q) ↔ Unifies σ P ∧ Unifies σ Q := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left Q he),
      fun e he => h e (List.mem_append_right P he)⟩
  · rintro ⟨hP, hQ⟩ e he
    exact (List.mem_append.mp he).elim (hP e) (hQ e)

@[simp] private theorem unifies_substProblem (σ : ℕ → L.Term ℕ)
    (τ : ℕ → L.Term α) (P : Problem L) :
    Unifies τ (substProblem σ P) ↔ Unifies (compose τ σ) P := by
  constructor
  · intro h e he
    change e.1.subst (fun x => (σ x).subst τ) = e.2.subst (fun x => (σ x).subst τ)
    rw [← FirstOrderProofs.term_subst_subst, ← FirstOrderProofs.term_subst_subst]
    exact h _ (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro h e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    change (d.1.subst σ).subst τ = (d.2.subst σ).subst τ
    rw [FirstOrderProofs.term_subst_subst, FirstOrderProofs.term_subst_subst]
    exact h d hd

private theorem subst_single_unchanged (x : ℕ) (t s : L.Term ℕ)
    (hx : x ∉ s.varFinset) : s.subst (single x t) = s := by
  induction s with
  | var y =>
      have hy : y ≠ x := by simpa [eq_comm] using hx
      simp [Term.subst, single, hy]
  | @func n f ss ih =>
      simp only [Term.subst]
      congr 1
      funext i
      exact ih i (fun h => hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩))

private theorem count_of_variable (t : L.Term ℕ) (σ : ℕ → L.Term α) (x : ℕ)
    (hx : x ∈ t.varFinset) : nodeCount (σ x) ≤ nodeCount (t.subst σ) := by
  induction t with
  | var y =>
      simp only [Term.varFinset, Finset.mem_singleton] at hx
      subst y
      exact le_rfl
  | @func n f ts ih =>
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      have h₁ := ih i hi
      have h₂ : nodeCount ((ts i).subst σ) ≤ ∑ j : Fin n, nodeCount ((ts j).subst σ) :=
        Finset.single_le_sum (f := fun j : Fin n => nodeCount ((ts j).subst σ))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simp only [Term.subst, nodeCount]
      omega

theorem occurs_obstruction (x : ℕ) (t : L.Term ℕ) (hx : x ∈ t.varFinset)
    (hne : t ≠ .var x) (σ : ℕ → L.Term α) : σ x ≠ t.subst σ := by
  cases t with
  | var y =>
      simp only [Term.varFinset, Finset.mem_singleton] at hx
      exact (hne (congrArg Term.var hx.symm)).elim
  | @func n f ts =>
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
      have h₁ := count_of_variable (ts i) σ x hi
      have h₂ : nodeCount ((ts i).subst σ) ≤ ∑ j : Fin n, nodeCount ((ts j).subst σ) :=
        Finset.single_le_sum (f := fun j : Fin n => nodeCount ((ts j).subst σ))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      intro heq
      have hc := congrArg nodeCount heq
      simp only [Term.subst, nodeCount] at hc
      omega

theorem elimination_sound (x : ℕ) (t : L.Term ℕ) (R : Problem L)
    (hx : x ∉ t.varFinset) (θ : ℕ → L.Term α)
    (hθ : Unifies θ (substProblem (single x t) R)) :
    Unifies (compose θ (single x t)) ((.var x, t) :: R) := by
  rw [unifies_cons]
  constructor
  · change (single x t x).subst θ = t.subst (fun y => (single x t y).subst θ)
    rw [← FirstOrderProofs.term_subst_subst, subst_single_unchanged x t t hx]
    simp [single]
  · exact (unifies_substProblem (single x t) θ R).mp hθ

theorem elimination_factors (x : ℕ) (t : L.Term ℕ) (R : Problem L)
    (σ : ℕ → L.Term α) (hσ : Unifies σ ((.var x, t) :: R)) :
    Unifies σ (substProblem (single x t) R) ∧ compose σ (single x t) = σ := by
  rcases (unifies_cons σ (.var x) t R).mp hσ with ⟨heq, hR⟩
  have hcomp : compose σ (single x t) = σ := by
    funext y
    by_cases hy : y = x
    · subst y
      simpa [compose, single, Term.subst] using heq.symm
    · simp [compose, single, hy, Term.subst]
  exact ⟨(unifies_substProblem (single x t) σ R).mpr (hcomp.symm ▸ hR), hcomp⟩

theorem elimination_most_general (x : ℕ) (t : L.Term ℕ) (R : Problem L)
    (hx : x ∉ t.varFinset) (θ : ℕ → L.Term ℕ)
    (hθ : MostGeneral.{u, v, w} (substProblem (single x t) R) θ) :
    MostGeneral.{u, v, w} ((.var x, t) :: R) (compose θ (single x t)) := by
  refine ⟨elimination_sound x t R hx θ hθ.1, ?_⟩
  intro α σ hσ
  rcases elimination_factors x t R σ hσ with ⟨hQ, hcomp⟩
  rcases hθ.2 α σ hQ with ⟨ρ, hρ⟩
  refine ⟨ρ, ?_⟩
  have hρθ : compose ρ θ = σ := funext hρ
  intro y
  change compose ρ (compose θ (single x t)) y = σ y
  rw [compose_assoc, hρθ, hcomp]

/-- One executable step: no separate recursive orientation step is needed. -/
inductive Action (L : Language.{u, v}) where
  | done
  | failure
  | keep (Q : Problem L)
  | eliminate (x : ℕ) (t : L.Term ℕ) (R : Problem L)

variable [∀ n, DecidableEq (L.Functions n)]

/-- Inspect an equation with a variable on the left. -/
def variableAction (x : ℕ) (t : L.Term ℕ) (R : Problem L) : Action L :=
  if t = .var x then .keep R
  else if x ∈ t.varFinset then .failure
  else .eliminate x t R

/-- Inspect the first equation and select exactly the rule in the human algorithm. -/
def classify : Problem L → Action L
  | [] => .done
  | (.var x, t) :: R => variableAction x t R
  | (s@(.func _ _), .var x) :: R => variableAction x s R
  | (@Term.func _ _ n f ss, @Term.func _ _ m g ts) :: R =>
      if h : n = m then
        if f = h ▸ g then
          .keep (List.ofFn (fun i : Fin n => (ss i, ts (Fin.cast h i))) ++ R)
        else .failure
      else .failure

private theorem variableAction_keep {x : ℕ} {t : L.Term ℕ} {R Q : Problem L}
    (h : variableAction x t R = .keep Q) : t = .var x ∧ Q = R := by
  unfold variableAction at h
  split at h
  · exact ⟨‹t = .var x›, (Action.keep.inj h).symm⟩
  · split at h <;> cases h

private theorem variableAction_eliminate {x y : ℕ} {t s : L.Term ℕ} {R Q : Problem L}
    (h : variableAction y s Q = .eliminate x t R) :
    y = x ∧ s = t ∧ Q = R ∧ x ∉ t.varFinset := by
  unfold variableAction at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl, rfl, ‹x ∉ t.varFinset›⟩

private theorem elimination_shape {P R : Problem L} {x : ℕ} {t : L.Term ℕ}
    (h : classify P = .eliminate x t R) :
    x ∉ t.varFinset ∧ (P = (.var x, t) :: R ∨ P = (t, .var x) :: R) := by
  cases P with
  | nil => cases h
  | cons e Q =>
    rcases e with ⟨s, u⟩
    cases s with
    | var y =>
      obtain ⟨rfl, rfl, rfl, hx⟩ := variableAction_eliminate h
      exact ⟨hx, Or.inl rfl⟩
    | @func n f ss =>
      cases u with
      | var y =>
        obtain ⟨rfl, rfl, rfl, hx⟩ := variableAction_eliminate h
        exact ⟨hx, Or.inr rfl⟩
      | @func m g ts =>
        simp only [classify] at h
        split at h
        · split at h <;> cases h
        · cases h

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem mem_problemVars (x : ℕ) (P : Problem L) :
    x ∈ problemVars P ↔ ∃ e ∈ P, x ∈ e.1.varFinset ∨ x ∈ e.2.varFinset := by
  induction P with
  | nil => simp [problemVars]
  | cons e R ih =>
    rcases e with ⟨s, t⟩
    simp only [problemVars, Finset.mem_union]
    constructor
    · rintro ((hs | ht) | hR)
      · exact ⟨(s, t), List.mem_cons_self, Or.inl hs⟩
      · exact ⟨(s, t), List.mem_cons_self, Or.inr ht⟩
      · obtain ⟨e, he, hx⟩ := ih.mp hR
        exact ⟨e, List.mem_cons_of_mem _ he, hx⟩
    · rintro ⟨e, he, hx⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl hx
      · exact Or.inr (ih.mpr ⟨e, he, hx⟩)

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem decomposed_variables {n : ℕ} (f : L.Functions n)
    (ss ts : Fin n → L.Term ℕ) (R : Problem L) :
    problemVars (List.ofFn (fun i => (ss i, ts i)) ++ R) ⊆
      problemVars ((.func f ss, .func f ts) :: R) := by
  intro x hx
  obtain ⟨e, he, hx⟩ := (mem_problemVars x _).mp hx
  rcases List.mem_append.mp he with hchildren | hR
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hchildren
    apply (mem_problemVars x _).mpr
    refine ⟨(.func f ss, .func f ts), List.mem_cons_self, ?_⟩
    rcases hx with hs | ht
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hs⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ht⟩)
  · exact (mem_problemVars x _).mpr ⟨e, List.mem_cons_of_mem _ hR, hx⟩

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem problemSize_append (P Q : Problem L) :
    problemSize (P ++ Q) = problemSize P + problemSize Q := by
  induction P with
  | nil => simp [problemSize]
  | cons e R ih =>
    rcases e with ⟨s, t⟩
    simp [problemSize, ih, Nat.add_assoc]

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem problemSize_sum (P : Problem L) :
    problemSize P = (P.map fun e => nodeCount e.1 + nodeCount e.2).sum := by
  induction P with
  | nil => rfl
  | cons e R ih =>
    rcases e with ⟨s, t⟩
    simp [problemSize, ih]

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem decomposed_size {n : ℕ} (f : L.Functions n)
    (ss ts : Fin n → L.Term ℕ) (R : Problem L) :
    problemSize (List.ofFn (fun i => (ss i, ts i)) ++ R) <
      problemSize ((.func f ss, .func f ts) :: R) := by
  rw [problemSize_append, problemSize_sum]
  simp only [List.map_ofFn, Function.comp_apply, List.sum_ofFn, Finset.sum_add_distrib,
    problemSize, nodeCount]
  omega

private theorem keep_data {P Q : Problem L} (h : classify P = .keep Q) :
    problemVars Q ⊆ problemVars P ∧ problemSize Q < problemSize P := by
  cases P with
  | nil => cases h
  | cons e R =>
    rcases e with ⟨s, t⟩
    cases s with
    | var x =>
      obtain ⟨rfl, rfl⟩ := variableAction_keep h
      constructor
      · intro y hy
        exact Finset.mem_union_right _ hy
      · simp only [problemSize, nodeCount]
        omega
    | @func n f ss =>
      cases t with
      | var x =>
        obtain ⟨hfalse, _⟩ := variableAction_keep h
        cases hfalse
      | @func m g ts =>
        simp only [classify] at h
        split at h
        · rename_i hnm
          subst m
          split at h
          · rename_i hfg
            change f = g at hfg
            subst g
            cases h
            exact ⟨decomposed_variables f ss ts R, decomposed_size f ss ts R⟩
          · cases h
        · cases h

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem term_subst_single_supported (V : Finset ℕ) (x : ℕ)
    (t s : L.Term ℕ) (ht : t.varFinset ⊆ V) (hs : s.varFinset ⊆ V)
    (hx : x ∉ t.varFinset) : (s.subst (single x t)).varFinset ⊆ V.erase x := by
  induction s with
  | var y =>
    by_cases hy : y = x
    · subst y
      change (single x t x).varFinset ⊆ V.erase x
      have he : single x t x = t := by simp [single]
      rw [he]
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun h => hx (h ▸ hz), ht hz⟩
    · change (single x t y).varFinset ⊆ V.erase x
      have he : single x t y = .var y := by simp [single, hy]
      rw [he]
      exact Finset.singleton_subset_iff.mpr
        (Finset.mem_erase.mpr ⟨hy, hs (Finset.mem_singleton_self y)⟩)
  | @func n f ss ih =>
    intro y hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact ih i (fun z hz => hs (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩)) hi

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem subst_problem_supported (V : Finset ℕ) (x : ℕ) (t : L.Term ℕ)
    (R : Problem L) (ht : t.varFinset ⊆ V) (hR : problemVars R ⊆ V)
    (hx : x ∉ t.varFinset) : problemVars (substProblem (single x t) R) ⊆ V.erase x := by
  intro y hy
  obtain ⟨e, he, hy⟩ := (mem_problemVars y _).mp hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  have hs : d.1.varFinset ⊆ V := fun z hz =>
    hR ((mem_problemVars z R).mpr ⟨d, hd, Or.inl hz⟩)
  have hu : d.2.varFinset ⊆ V := fun z hz =>
    hR ((mem_problemVars z R).mpr ⟨d, hd, Or.inr hz⟩)
  exact hy.elim (fun h => term_subst_single_supported V x t d.1 ht hs hx h)
    (fun h => term_subst_single_supported V x t d.2 ht hu hx h)

private theorem keep_variables {P Q : Problem L} (h : classify P = .keep Q) :
    problemVars Q ⊆ problemVars P := by
  exact (keep_data h).1

private theorem keep_size {P Q : Problem L} (h : classify P = .keep Q) :
    problemSize Q < problemSize P := by
  exact (keep_data h).2

private theorem eliminate_member {P R : Problem L} {x : ℕ} {t : L.Term ℕ}
    (h : classify P = .eliminate x t R) : x ∈ problemVars P := by
  rcases (elimination_shape h).2 with rfl | rfl <;> simp [problemVars]

private theorem eliminate_variables {P R : Problem L} {x : ℕ} {t : L.Term ℕ}
    (h : classify P = .eliminate x t R) :
    problemVars (substProblem (single x t) R) ⊆ (problemVars P).erase x := by
  obtain ⟨hx, hshape⟩ := elimination_shape h
  apply subst_problem_supported (problemVars P) x t R _ _ hx
  · rcases hshape with rfl | rfl
    · exact fun _ hy => Finset.mem_union_left _ (Finset.mem_union_right _ hy)
    · exact fun _ hy => Finset.mem_union_left _ (Finset.mem_union_left _ hy)
  · rcases hshape with rfl | rfl <;> exact fun _ hy => Finset.mem_union_right _ hy

private theorem variableAction_failure {x : ℕ} {t : L.Term ℕ} {R : Problem L}
    (h : variableAction x t R = .failure) : t ≠ .var x ∧ x ∈ t.varFinset := by
  unfold variableAction at h
  split at h
  · cases h
  · rename_i hne
    split at h
    · exact ⟨hne, ‹x ∈ t.varFinset›⟩
    · cases h

private theorem done_shape {P : Problem L} (h : classify P = .done) : P = [] := by
  cases P with
  | nil => rfl
  | cons e R =>
    rcases e with ⟨s, t⟩
    cases s <;> cases t <;> simp only [classify, variableAction] at h
    all_goals split_ifs at h

omit [∀ n, DecidableEq (L.Functions n)] in
private theorem unifies_decomposed {n : ℕ} (f : L.Functions n)
    (ss ts : Fin n → L.Term ℕ) (R : Problem L) (σ : ℕ → L.Term α) :
    Unifies σ (List.ofFn (fun i => (ss i, ts i)) ++ R) ↔
      Unifies σ ((.func f ss, .func f ts) :: R) := by
  rw [unifies_append, unifies_cons]
  apply and_congr_left
  intro _
  constructor
  · intro h
    change Term.func f (fun i => (ss i).subst σ) = Term.func f (fun i => (ts i).subst σ)
    congr 1
    funext i
    exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact congrFun (eq_of_heq (Term.func.inj h).2.2) i

private theorem keep_unifies {P Q : Problem L} (h : classify P = .keep Q)
    (σ : ℕ → L.Term α) : Unifies σ P ↔ Unifies σ Q := by
  cases P with
  | nil => cases h
  | cons e R =>
    rcases e with ⟨s, t⟩
    cases s with
    | var x =>
      obtain ⟨rfl, rfl⟩ := variableAction_keep h
      simp
    | @func n f ss =>
      cases t with
      | var x =>
        obtain ⟨hfalse, _⟩ := variableAction_keep h
        cases hfalse
      | @func m g ts =>
        simp only [classify] at h
        split at h
        · rename_i hnm
          subst m
          split at h
          · rename_i hfg
            change f = g at hfg
            subst g
            cases h
            exact (unifies_decomposed f ss ts R σ).symm
          · cases h
        · cases h

private theorem failure_no_unifier {P : Problem L} (h : classify P = .failure)
    (σ : ℕ → L.Term α) : ¬ Unifies σ P := by
  cases P with
  | nil => cases h
  | cons e R =>
    rcases e with ⟨s, t⟩
    cases s with
    | var x =>
      obtain ⟨hne, hx⟩ := variableAction_failure h
      intro hσ
      exact occurs_obstruction x t hx hne σ ((unifies_cons σ _ _ _).mp hσ).1
    | @func n f ss =>
      cases t with
      | var x =>
        obtain ⟨hne, hx⟩ := variableAction_failure h
        intro hσ
        exact occurs_obstruction x (.func f ss) hx hne σ
          ((unifies_cons σ _ _ _).mp hσ).1.symm
      | @func m g ts =>
        simp only [classify] at h
        split at h
        · rename_i hnm
          subst m
          split at h
          · cases h
          · rename_i hfg
            change f ≠ g at hfg
            intro hσ
            exact hfg (eq_of_heq (Term.func.inj ((unifies_cons σ _ _ _).mp hσ).1).2.1)
        · rename_i hnm
          intro hσ
          exact hnm (Term.func.inj ((unifies_cons σ _ _ _).mp hσ).1).1

private theorem classify_elimination_sound {P R : Problem L} {x : ℕ} {t : L.Term ℕ}
    (h : classify P = .eliminate x t R) (θ : ℕ → L.Term α)
    (hθ : Unifies θ (substProblem (single x t) R)) : Unifies (compose θ (single x t)) P := by
  obtain ⟨hx, hshape⟩ := elimination_shape h
  have hresult := elimination_sound x t R hx θ hθ
  rcases hshape with rfl | rfl
  · exact hresult
  · rw [unifies_cons] at hresult ⊢
    exact ⟨hresult.1.symm, hresult.2⟩

private theorem classify_elimination_factors {P R : Problem L} {x : ℕ} {t : L.Term ℕ}
    (h : classify P = .eliminate x t R) (σ : ℕ → L.Term α) (hσ : Unifies σ P) :
    Unifies σ (substProblem (single x t) R) ∧ compose σ (single x t) = σ := by
  have hnormal : Unifies σ ((.var x, t) :: R) := by
    rcases (elimination_shape h).2 with rfl | rfl
    · exact hσ
    · rw [unifies_cons] at hσ ⊢
      exact ⟨hσ.1.symm, hσ.2⟩
  exact elimination_factors x t R σ hnormal

/-- Executable well-founded recursion; all proof arguments erase at runtime. -/
def solve (V : Finset ℕ) (P : Problem L) (hv : Supported V P) :
    Option (ℕ → L.Term ℕ) :=
  match hs : classify P with
  | .done => some Term.var
  | .failure => none
  | .keep Q => solve V Q (fun _ hy => hv (keep_variables hs hy))
  | .eliminate x t R =>
      let Q := substProblem (single x t) R
      let hQ : Supported (V.erase x) Q := fun y hy =>
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (eliminate_variables hs hy)).1,
          hv (Finset.mem_erase.mp (eliminate_variables hs hy)).2⟩
      (solve (V.erase x) Q hQ).map fun θ => compose θ (single x t)
termination_by (V.card, problemSize P)
decreasing_by
  · exact Prod.Lex.right _ (keep_size hs)
  · exact Prod.Lex.left _ _ (Finset.card_erase_lt_of_mem (hv (eliminate_member hs)))

/-- Initialize the allowed-variable set with the exact finite input support. -/
def unify (P : Problem L) : Option (ℕ → L.Term ℕ) := solve (problemVars P) P (fun _ h => h)

private theorem solve_done_eq (V : Finset ℕ) (P : Problem L) (hv : Supported V P)
    (hs : classify P = .done) : solve V P hv = some Term.var := by
  rw [solve.eq_def]
  split <;> simp_all

private theorem solve_failure_eq (V : Finset ℕ) (P : Problem L) (hv : Supported V P)
    (hs : classify P = .failure) : solve V P hv = none := by
  rw [solve.eq_def]
  split <;> simp_all

private theorem solve_keep_eq (V : Finset ℕ) (P : Problem L) (hv : Supported V P)
    (Q : Problem L) (hs : classify P = .keep Q) (hQ : Supported V Q) :
    solve V P hv = solve V Q hQ := by
  rw [solve.eq_def]
  split <;> simp_all

private theorem solve_eliminate_eq (V : Finset ℕ) (P : Problem L) (hv : Supported V P)
    (x : ℕ) (t : L.Term ℕ) (R : Problem L) (hs : classify P = .eliminate x t R)
    (hQ : Supported (V.erase x) (substProblem (single x t) R)) :
    solve V P hv = (solve (V.erase x) (substProblem (single x t) R) hQ).map
      (fun θ => compose θ (single x t)) := by
  rw [solve.eq_def]
  split <;> simp_all

private theorem solve_sound (V : Finset ℕ) (P : Problem L) (hv : Supported V P) :
    ∀ μ, solve V P hv = some μ → Unifies μ P := by
  induction V, P, hv using solve.induct with
  | case1 V P hv hs =>
    intro μ hμ
    rw [solve_done_eq V P hv hs, Option.some.injEq] at hμ
    subst μ
    rw [done_shape hs]
    exact unifies_nil _
  | case2 V P hv hs =>
    intro μ hμ
    rw [solve_failure_eq V P hv hs] at hμ
    cases hμ
  | case3 V P hv Q hs ih =>
    intro μ hμ
    rw [solve_keep_eq V P hv Q hs (fun _ hy => hv (keep_variables hs hy))] at hμ
    exact (keep_unifies hs μ).mpr (ih μ hμ)
  | case4 V P hv x t R hs Q hQ ih =>
    intro μ hμ
    rw [solve_eliminate_eq V P hv x t R hs hQ] at hμ
    cases hrec : solve (V.erase x) (substProblem (single x t) R) hQ with
    | none => simp only [hrec, Option.map_none] at hμ; cases hμ
    | some θ =>
      simp only [hrec, Option.map_some, Option.some.injEq] at hμ
      subst μ
      exact classify_elimination_sound hs θ (ih θ hrec)

private theorem solve_complete_factor (V : Finset ℕ) (P : Problem L) (hv : Supported V P) :
    ∀ σ : ℕ → L.Term α, Unifies σ P →
      ∃ μ ρ, solve V P hv = some μ ∧ ∀ x, (μ x).subst ρ = σ x := by
  induction V, P, hv using solve.induct with
  | case1 V P hv hs =>
    intro σ _
    refine ⟨Term.var, σ, ?_, fun _ => rfl⟩
    exact solve_done_eq V P hv hs
  | case2 V P hv hs =>
    intro σ hσ
    exact (failure_no_unifier hs σ hσ).elim
  | case3 V P hv Q hs ih =>
    intro σ hσ
    obtain ⟨μ, ρ, hμ, hρ⟩ := ih σ ((keep_unifies hs σ).mp hσ)
    refine ⟨μ, ρ, ?_, hρ⟩
    exact (solve_keep_eq V P hv Q hs (fun _ hy => hv (keep_variables hs hy))).trans hμ
  | case4 V P hv x t R hs Q hQ ih =>
    intro σ hσ
    obtain ⟨hσQ, hcomp⟩ := classify_elimination_factors hs σ hσ
    obtain ⟨θ, ρ, hθ, hρ⟩ := ih σ hσQ
    refine ⟨compose θ (single x t), ρ, ?_, ?_⟩
    · rw [solve_eliminate_eq V P hv x t R hs hQ, hθ]
      rfl
    · have hρθ : compose ρ θ = σ := funext hρ
      intro y
      change compose ρ (compose θ (single x t)) y = σ y
      rw [compose_assoc, hρθ, hcomp]

private theorem solve_fixes_outside (V : Finset ℕ) (P : Problem L) (hv : Supported V P) :
    ∀ μ, solve V P hv = some μ → ∀ y, y ∉ V → μ y = .var y := by
  induction V, P, hv using solve.induct with
  | case1 V P hv hs =>
    intro μ hμ y _
    rw [solve_done_eq V P hv hs, Option.some.injEq] at hμ
    subst μ
    rfl
  | case2 V P hv hs =>
    intro μ hμ
    rw [solve_failure_eq V P hv hs] at hμ
    cases hμ
  | case3 V P hv Q hs ih =>
    intro μ hμ y hy
    rw [solve_keep_eq V P hv Q hs (fun _ hy => hv (keep_variables hs hy))] at hμ
    exact ih μ hμ y hy
  | case4 V P hv x t R hs Q hQ ih =>
    intro μ hμ y hy
    rw [solve_eliminate_eq V P hv x t R hs hQ] at hμ
    cases hrec : solve (V.erase x) (substProblem (single x t) R) hQ with
    | none => simp only [hrec, Option.map_none] at hμ; cases hμ
    | some θ =>
      simp only [hrec, Option.map_some, Option.some.injEq] at hμ
      subst μ
      have hyx : y ≠ x := fun h => hy (h ▸ hv (eliminate_member hs))
      have hyV : y ∉ V.erase x := fun h => hy (Finset.mem_of_mem_erase h)
      simpa [compose, single, hyx, Term.subst] using ih θ hrec y hyV

/-- Support invariance and strict progress for the two recursive rules. -/
theorem recursive_progress (V : Finset ℕ) (P : Problem L) (hv : Supported V P) :
    (∀ Q, classify P = .keep Q → Supported V Q ∧ problemSize Q < problemSize P) ∧
    (∀ x t R, classify P = .eliminate x t R →
      Supported (V.erase x) (substProblem (single x t) R) ∧ (V.erase x).card < V.card) := by
  constructor
  · intro Q hQ
    exact ⟨fun _ hy => hv (keep_variables hQ hy), keep_size hQ⟩
  · intro x t R hs
    refine ⟨?_, Finset.card_erase_lt_of_mem (hv (eliminate_member hs))⟩
    intro y hy
    obtain ⟨hne, hyP⟩ := Finset.mem_erase.mp (eliminate_variables hs hy)
    exact Finset.mem_erase.mpr ⟨hne, hv hyP⟩

theorem unify_sound (P : Problem L) (μ : ℕ → L.Term ℕ)
    (h : unify P = some μ) : Unifies μ P := by
  exact solve_sound (problemVars P) P (fun _ h => h) μ h

/-- The factorization includes every variable, with any residual alphabet. -/
theorem unify_factorization (P : Problem L) (μ : ℕ → L.Term ℕ)
    (h : unify P = some μ) (σ : ℕ → L.Term α) (hσ : Unifies σ P) : Factors σ μ := by
  obtain ⟨θ, ρ, hθ, hρ⟩ := solve_complete_factor (problemVars P) P (fun _ h => h) σ hσ
  have heq : θ = μ := Option.some.inj (hθ.symm.trans h)
  subst θ
  exact ⟨ρ, hρ⟩

theorem unify_complete (P : Problem L) (σ : ℕ → L.Term α) (hσ : Unifies σ P) :
    ∃ μ, unify P = some μ := by
  obtain ⟨μ, ρ, hμ, _⟩ := solve_complete_factor (problemVars P) P (fun _ h => h) σ hσ
  exact ⟨μ, hμ⟩

theorem unify_failure_iff (P : Problem L) :
    unify P = none ↔ ¬ ∃ σ : ℕ → L.Term ℕ, Unifies σ P := by
  constructor
  · rintro hnone ⟨σ, hσ⟩
    obtain ⟨μ, hμ⟩ := unify_complete P σ hσ
    rw [hnone] at hμ
    cases hμ
  · intro hno
    cases h : unify P with
    | none => rfl
    | some μ => exact (hno ⟨μ, unify_sound P μ h⟩).elim

theorem unify_fixes_outside (P : Problem L) (μ : ℕ → L.Term ℕ)
    (h : unify P = some μ) (x : ℕ) (hx : x ∉ problemVars P) : μ x = .var x := by
  exact solve_fixes_outside (problemVars P) P (fun _ h => h) μ h x hx

theorem unify_most_general (P : Problem L) (μ : ℕ → L.Term ℕ)
    (h : unify P = some μ) : MostGeneral.{u, v, w} P μ := by
  exact ⟨unify_sound P μ h, fun _ σ hσ => unify_factorization P μ h σ hσ⟩

/-- Matching changes only the pattern and leaves the target term unchanged. -/
def Matches (s t : L.Term ℕ) : Prop := ∃ σ : ℕ → L.Term ℕ, s.subst σ = t

end Lemmatheca.MathematicalLogic.TermUnification
