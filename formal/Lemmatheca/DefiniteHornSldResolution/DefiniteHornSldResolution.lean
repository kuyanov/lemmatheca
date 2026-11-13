import Lemmatheca.FirstOrderHornRules.FirstOrderHornRules
import Lemmatheca.FirstOrderResolution.FirstOrderResolution

/-! Native list goals, fresh clause variants, actual MGUs, and SLD proof forests. -/
namespace Lemmatheca.MathematicalLogic.DefiniteHornSldResolution

open FirstOrder FirstOrder.Language HerbrandModels

universe u v w z
variable {L : Language.{u, v}}

structure Clause (L : Language.{u, v}) where
  arity : ℕ
  body : List (Atom L (Fin arity))
  head : Atom L (Fin arity)

abbrev Program (L : Language.{u, v}) := List (Clause L)
abbrev Goal (L : Language.{u, v}) (α : Type w) := List (Atom L α)
abbrev Substitution (L : Language.{u, v}) := ℕ → L.Term ℕ

def goalSubst {α : Type w} {β : Type z} (σ : α → L.Term β) (G : Goal L α) : Goal L β :=
  G.map (Atom.subst σ)

def GoalRealize {α : Type w} {M : Type z} [L.Structure M]
    (G : Goal L α) (a : α → M) : Prop := ∀ A ∈ G, A.Realize a

noncomputable def Clause.toRule (c : Clause L) : FirstOrderHornRules.Rule L :=
  ⟨c.arity, c.body.toFinset, c.head⟩

noncomputable def programTheory (P : Program L) : L.Theory :=
  FirstOrderHornRules.theory {r | ∃ c ∈ P, c.toRule = r}

def ProgramModels (P : Program L) (M : Type z) [L.Structure M] : Prop :=
  ∀ c ∈ P, ∀ a : Fin c.arity → M, GoalRealize c.body a → c.head.Realize a

theorem program_models_iff (P : Program L) (M : Type z) [L.Structure M] :
    M ⊨ programTheory P ↔ ProgramModels P M := by
  rw [programTheory, FirstOrderHornRules.theory_models_iff]
  constructor
  · intro h c hc a ha
    apply h c.toRule ⟨c, hc, rfl⟩ a
    intro A hA
    exact ha A (List.mem_toFinset.mp hA)
  · rintro h r ⟨c, hc, rfl⟩ a ha
    apply h c hc a
    intro A hA
    exact ha A (List.mem_toFinset.mpr hA)

theorem goal_subst_subst {α : Type w} {β : Type z} {γ : Type*}
    (G : Goal L α) (σ : α → L.Term β) (τ : β → L.Term γ) :
    goalSubst τ (goalSubst σ G) = goalSubst (fun x => (σ x).subst τ) G := by
  simp only [goalSubst, List.map_map]
  apply List.map_congr_left
  intro A _
  exact Atom.subst_subst A σ τ

theorem goal_subst_realize {α : Type w} {β : Type z} {M : Type*} [L.Structure M]
    (G : Goal L α) (σ : α → L.Term β) (a : β → M) :
    GoalRealize (goalSubst σ G) a ↔ GoalRealize G (fun x => (σ x).realize a) := by
  simp only [GoalRealize, goalSubst, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Atom.subst_realize]

def atomVars (A : Atom L ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => (A.terms i).varFinset)

def goalVars : Goal L ℕ → Finset ℕ
  | [] => ∅
  | A :: G => atomVars A ∪ goalVars G

def freshBase (U : Finset ℕ) : ℕ := if U = ∅ then 0 else U.sup id + 1

def freshInjection (U : Finset ℕ) (n : ℕ) : Fin n ↪ ℕ where
  toFun i := freshBase U + i.val
  inj' := fun _ _ h => Fin.ext (Nat.add_left_cancel h)

theorem fresh_away (U : Finset ℕ) (n : ℕ) (i : Fin n) :
    freshInjection U n i ∉ U := by
  intro h
  by_cases hU : U = ∅
  · simp [hU] at h
  · have hm : freshInjection U n i ≤ U.sup id := Finset.le_sup (f := id) h
    simp only [freshInjection, freshBase, hU, ↓reduceIte, Function.Embedding.coeFn_mk] at hm
    omega

def variantHead (c : Clause L) (ν : Fin c.arity ↪ ℕ) : Atom L ℕ :=
  c.head.subst (fun i => .var (ν i))

def variantBody (c : Clause L) (ν : Fin c.arity ↪ ℕ) : Goal L ℕ :=
  goalSubst (fun i => .var (ν i)) c.body

private theorem term_subst_agree {α : Type*} [DecidableEq α] {β : Type*}
    (t : L.Term α) (σ τ : α → L.Term β)
    (h : ∀ x ∈ t.varFinset, σ x = τ x) : t.subst σ = t.subst τ := by
  induction t with
  | var x => exact h x (Finset.mem_singleton_self x)
  | func f ts ih =>
      simp only [Term.subst]
      apply congrArg (Term.func f)
      funext i
      exact ih i (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩))

private theorem atom_subst_agree (A : Atom L ℕ) {β : Type*}
    (σ τ : ℕ → L.Term β) (h : ∀ x ∈ atomVars A, σ x = τ x) : A.subst σ = A.subst τ := by
  cases A with
  | mk n r ts =>
      apply congrArg (Atom.mk n r)
      funext i
      exact term_subst_agree (ts i) σ τ
        (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩))

private theorem atom_vars_in_goal {A : Atom L ℕ} {G : Goal L ℕ} (h : A ∈ G) :
    atomVars A ⊆ goalVars G := by
  induction G with
  | nil => simp at h
  | cons B G ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih h) Finset.subset_union_right

private theorem goal_vars_mono {G H : Goal L ℕ} (h : G ⊆ H) : goalVars G ⊆ goalVars H := by
  induction G with
  | nil => exact Finset.empty_subset _
  | cons A G ih =>
      exact Finset.union_subset (atom_vars_in_goal (h List.mem_cons_self))
        (ih (fun _ ha => h (List.mem_cons_of_mem _ ha)))

private theorem goal_vars_append (G H : Goal L ℕ) :
    goalVars (G ++ H) = goalVars G ∪ goalVars H := by
  induction G with
  | nil => simp [goalVars]
  | cons A G ih => simp [goalVars, ih, Finset.union_assoc]

private theorem goal_subst_agree {β : Type*} (G : Goal L ℕ) (σ τ : ℕ → L.Term β)
    (h : ∀ x ∈ goalVars G, σ x = τ x) : goalSubst σ G = goalSubst τ G := by
  apply List.map_congr_left
  intro A hA
  exact atom_subst_agree A σ τ (fun x hx => h x (atom_vars_in_goal hA hx))

private theorem atom_vars_subst (A : Atom L ℕ) (σ : Substitution L) :
    atomVars (A.subst σ) = (atomVars A).biUnion (fun x => (σ x).varFinset) := by
  simp only [atomVars, Atom.subst, FirstOrderSyntax.term_varFinset_subst,
    Finset.biUnion_biUnion]
  rfl

private theorem goal_vars_subst (G : Goal L ℕ) (σ : Substitution L) :
    goalVars (goalSubst σ G) = (goalVars G).biUnion (fun x => (σ x).varFinset) := by
  induction G with
  | nil => simp [goalSubst, goalVars]
  | cons A G ih =>
      simp only [goalSubst, List.map_cons, goalVars, atom_vars_subst, Finset.union_biUnion]
      exact congrArg (fun S : Finset ℕ => ((atomVars A).biUnion fun x => (σ x).varFinset) ∪ S) ih

private theorem variant_body_tracked (c : Clause L) (ν : Fin c.arity ↪ ℕ) :
    goalVars (variantBody c ν) ⊆ Finset.univ.image ν := by
  have hterm (t : L.Term (Fin c.arity)) :
      (t.subst (fun i => Term.var (ν i))).varFinset ⊆ Finset.univ.image ν := by
    rw [FirstOrderSyntax.term_varFinset_subst]
    intro x hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    have he : x = ν i := Finset.mem_singleton.mp hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he.symm⟩
  have hbody (G : Goal L (Fin c.arity)) :
      goalVars (goalSubst (fun i => Term.var (ν i)) G) ⊆ Finset.univ.image ν := by
    induction G with
    | nil => exact Finset.empty_subset _
    | cons A G ih =>
        apply Finset.union_subset ?_ ih
        intro x hx
        obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
        exact hterm (A.terms i) hx
  exact hbody c.body

private theorem list_split_at {α : Type*} (G : List α) (i : ℕ) (hi : i < G.length) :
    G.take i ++ [G[i] ] ++ G.drop (i + 1) = G := by
  induction G generalizing i with
  | nil => simp at hi
  | cons A G ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < G.length := by simpa using hi
          change A :: (G.take i ++ [G[i]'hi'] ++ G.drop (i + 1)) = A :: G
          exact congrArg (List.cons A) (ih i hi')

def atomEquations [∀ n, DecidableEq (L.Relations n)] (A B : Atom L ℕ) :
    Option (TermUnification.Problem L) :=
  if h : A.arity = B.arity then
    if A.relation = h ▸ B.relation then
      some (List.ofFn (fun i : Fin A.arity => (A.terms i, B.terms (Fin.cast h i))))
    else none
  else none

def solveAtoms [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]
    (A B : Atom L ℕ) : Option (Substitution L) :=
  (atomEquations A B).bind TermUnification.unify

private theorem pair_unifies {α : Type*} (A B : Atom L ℕ) (σ : ℕ → L.Term α) :
    FirstOrderResolution.AtomUnifies σ {A, B} ↔ A.subst σ = B.subst σ := by
  classical
  constructor
  · intro h
    exact h A (by simp) B (by simp)
  · intro h a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl

private theorem equations_unify [∀ n, DecidableEq (L.Relations n)]
    {α : Type*} (A B : Atom L ℕ) (P : TermUnification.Problem L)
    (h : atomEquations A B = some P) (σ : ℕ → L.Term α) :
    TermUnification.Unifies σ P ↔ A.subst σ = B.subst σ := by
  rcases A with ⟨n, r, ts⟩
  rcases B with ⟨m, t, us⟩
  by_cases hn : n = m
  · subst m
    by_cases hr : r = t
    · subst t
      simp only [atomEquations, ↓reduceDIte, ↓reduceIte, Option.some.injEq] at h
      subst P
      simp [TermUnification.Unifies, List.mem_ofFn, Atom.subst, Atom.mk.injEq, funext_iff]
    · simp [atomEquations, hr] at h
  · simp [atomEquations, hn] at h

private theorem equations_exist [∀ n, DecidableEq (L.Relations n)] {α : Type*}
    (A B : Atom L ℕ) (σ : ℕ → L.Term α) (h : A.subst σ = B.subst σ) :
    ∃ P, atomEquations A B = some P := by
  rcases A with ⟨n, r, ts⟩
  rcases B with ⟨m, t, us⟩
  simp only [Atom.subst, Atom.mk.injEq] at h
  rcases h with ⟨hn, hr, _⟩
  cases hn
  have hr' : r = t := eq_of_heq hr
  cases hr'
  exact ⟨List.ofFn (fun i : Fin n => (ts i, us i)), by simp [atomEquations]⟩

theorem solve_atoms_sound [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] (A B : Atom L ℕ) (μ : Substitution L)
    (h : solveAtoms A B = some μ) : FirstOrderResolution.AtomMGU.{u, v, 0} {A, B} μ := by
  obtain ⟨P, hP, hμ⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨(pair_unifies A B μ).mpr
    ((equations_unify A B P hP μ).mp (TermUnification.unify_sound P μ hμ)), ?_⟩
  intro β σ hσ
  exact TermUnification.unify_factorization P μ hμ σ
    ((equations_unify A B P hP σ).mpr ((pair_unifies A B σ).mp hσ))

theorem solve_atoms_complete [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] {β : Type} (A B : Atom L ℕ)
    (σ : ℕ → L.Term β) (h : A.subst σ = B.subst σ) :
    ∃ μ, solveAtoms A B = some μ := by
  obtain ⟨P, hP⟩ := equations_exist A B σ h
  obtain ⟨μ, hμ⟩ := TermUnification.unify_complete P σ
    ((equations_unify A B P hP σ).mpr h)
  exact ⟨μ, Option.bind_eq_some_iff.mpr ⟨P, hP, hμ⟩⟩

abbrev Selector (L : Language.{u, v}) (α : Type w) :=
  ∀ (G : Goal L α), G ≠ [] → Fin G.length

structure StepData (P : Program L) (U : Finset ℕ) (G : Goal L ℕ) (i : Fin G.length) where
  clause : Clause L
  member : clause ∈ P
  names : Fin clause.arity ↪ ℕ
  fresh : ∀ j, names j ∉ U
  tracked : goalVars G ⊆ U
  unifier : Substitution L
  mostGeneral : FirstOrderResolution.AtomMGU.{u, v, 0}
    {G[i.val], variantHead clause names} unifier

def resolvent {P : Program L} {U G i} (d : StepData P U G i) : Goal L ℕ :=
  goalSubst d.unifier
    (G.take i.val ++ variantBody d.clause d.names ++ G.drop (i.val + 1))

def nextUsed {P : Program L} {U G i} (d : StepData P U G i) : Finset ℕ :=
  let V := U ∪ Finset.univ.image d.names
  V ∪ V.biUnion (fun x => (d.unifier x).varFinset)

theorem resolvent_tracked {P : Program L} {U G i} (d : StepData P U G i) :
    goalVars (resolvent d) ⊆ nextUsed d := by
  let V := U ∪ Finset.univ.image d.names
  have ht : goalVars (G.take i.val) ⊆ V :=
    Finset.Subset.trans (goal_vars_mono (fun _ h => List.mem_of_mem_take h))
      (Finset.Subset.trans d.tracked Finset.subset_union_left)
  have hd : goalVars (G.drop (i.val + 1)) ⊆ V :=
    Finset.Subset.trans (goal_vars_mono (fun _ h => List.mem_of_mem_drop h))
      (Finset.Subset.trans d.tracked Finset.subset_union_left)
  have hb : goalVars (variantBody d.clause d.names) ⊆ V :=
    Finset.Subset.trans (variant_body_tracked d.clause d.names) Finset.subset_union_right
  have hall : goalVars (G.take i.val ++ variantBody d.clause d.names ++ G.drop (i.val + 1)) ⊆ V := by
    simp only [goal_vars_append]
    exact Finset.union_subset (Finset.union_subset ht hb) hd
  rw [resolvent, goal_vars_subst]
  intro y hy
  obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
  exact Finset.mem_union_right V (Finset.mem_biUnion.mpr ⟨x, hall hx, hy⟩)

inductive Refutes (P : Program L) (select : Selector L ℕ) :
    Finset ℕ → Goal L ℕ → Substitution L → Prop
  | done (U) : Refutes P select U [] Term.var
  | step {U G τ} (hne : G ≠ []) (d : StepData P U G (select G hne)) :
      Refutes P select (nextUsed d) (resolvent d) τ →
        Refutes P select U G (TermUnification.compose τ d.unifier)

theorem step_sound {P : Program L} {U G i} (d : StepData P U G i)
    (M : Type z) [L.Structure M] (hM : ProgramModels P M) (a : ℕ → M)
    (hG : GoalRealize (resolvent d) a) : GoalRealize (goalSubst d.unifier G) a := by
  classical
  let b : ℕ → M := fun x => (d.unifier x).realize a
  have hbase : GoalRealize
      (G.take i.val ++ variantBody d.clause d.names ++ G.drop (i.val + 1)) b :=
    (goal_subst_realize _ d.unifier a).mp hG
  have hbody : GoalRealize (variantBody d.clause d.names) b := by
    intro A hA
    exact hbase A (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hA))))
  have hlocal : GoalRealize d.clause.body (fun j => b (d.names j)) :=
    (goal_subst_realize d.clause.body (fun j => Term.var (d.names j)) b).mp hbody
  have hh := hM d.clause d.member (fun j => b (d.names j)) hlocal
  have hfresh : (variantHead d.clause d.names).Realize b :=
    (Atom.subst_realize d.clause.head (fun j => Term.var (d.names j)) b).mpr hh
  have hu := d.mostGeneral.1 (G[i.val]) (by simp)
    (variantHead d.clause d.names) (by simp)
  have hselected : (G[i.val]).Realize b := by
    apply (Atom.subst_realize (G[i.val]) d.unifier a).mp
    rw [hu]
    exact (Atom.subst_realize _ d.unifier a).mpr hfresh
  apply (goal_subst_realize G d.unifier a).mpr
  intro A hA
  rw [← list_split_at G i.val i.isLt] at hA
  rcases List.mem_append.mp hA with hfront | hpost
  · rcases List.mem_append.mp hfront with hpre | hselected'
    · exact hbase A (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hpre))))
    · obtain rfl := List.mem_singleton.mp hselected'
      exact hselected
  · exact hbase A (List.mem_append.mpr (.inr hpost))

theorem answer_sound {P : Program L} {select U G θ} (h : Refutes P select U G θ)
    (M : Type z) [L.Structure M] (hM : ProgramModels P M) (a : ℕ → M) :
    GoalRealize (goalSubst θ G) a := by
  induction h generalizing a with
  | done U => simp [goalSubst, GoalRealize]
  | @step U G τ hne d _ ih =>
      have ht := (goal_subst_realize (resolvent d) τ a).mp (ih a)
      have hs := step_sound d M hM (fun x => (τ x).realize a) ht
      have hp := (goal_subst_realize (goalSubst d.unifier G) τ a).mpr hs
      rw [goal_subst_subst] at hp
      exact hp

noncomputable def Clause.ground {β : Type w} (c : Clause L)
    (σ : Fin c.arity → L.Term β) : FirstOrderHornRules.DefiniteRule (Atom L β) :=
  ⟨(goalSubst σ c.body).toFinset, c.head.subst σ⟩

def grounding (P : Program L) (β : Type w) :
    Set (FirstOrderHornRules.DefiniteRule (Atom L β)) :=
  {r | ∃ c ∈ P, ∃ σ : Fin c.arity → L.Term β, c.ground σ = r}

theorem closed_grounding_bridge (P : Program L) :
    grounding P Empty = FirstOrderHornRules.grounding {r | ∃ c ∈ P, c.toRule = r} := by
  have he (c : Clause L) (σ : Fin c.arity → GroundTerm L) :
      c.ground σ = c.toRule.ground σ := by
    simp only [Clause.ground, Clause.toRule, FirstOrderHornRules.Rule.ground, goalSubst]
    congr 1
    ext A
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  ext r
  constructor
  · rintro ⟨c, hc, σ, rfl⟩
    exact ⟨c.toRule, ⟨c, hc, rfl⟩, σ, (he c σ).symm⟩
  · rintro ⟨r, ⟨c, hc, rfl⟩, σ, rfl⟩
    exact ⟨c, hc, σ, he c σ⟩

mutual
  inductive Tree (P : Program L) (β : Type w) : Atom L β → ℕ → Prop
    | node (c : Clause L) (hc : c ∈ P) (σ : Fin c.arity → L.Term β) {n : ℕ} :
        Forest P β (goalSubst σ c.body) n → Tree P β (c.head.subst σ) (n + 1)
  inductive Forest (P : Program L) (β : Type w) : Goal L β → ℕ → Prop
    | nil : Forest P β [] 0
    | cons {A G n m} : Tree P β A n → Forest P β G m → Forest P β (A :: G) (n + m)
end

private theorem forest_of_trees {P : Program L} {β : Type*} (G : Goal L β)
    (h : ∀ A ∈ G, ∃ n, Tree P β A n) : ∃ n, Forest P β G n := by
  induction G with
  | nil => exact ⟨0, Forest.nil⟩
  | cons A G ih =>
      obtain ⟨n, ht⟩ := h A List.mem_cons_self
      obtain ⟨m, hf⟩ := ih (fun B hB => h B (List.mem_cons_of_mem A hB))
      exact ⟨n + m, Forest.cons ht hf⟩

private theorem forest_member {P : Program L} {β : Type*} {G : Goal L β} {n : ℕ}
    (h : Forest P β G n) (A : Atom L β) (hA : A ∈ G) :
    ∃ k, k ≤ n ∧ Tree P β A k := by
  induction G generalizing n with
  | nil => simp at hA
  | cons B G ih =>
      cases h with
      | @cons _ _ n m ht hf =>
          rcases List.mem_cons.mp hA with rfl | hA
          · exact ⟨n, by omega, ht⟩
          · obtain ⟨k, hk, htree⟩ := ih hf hA
            exact ⟨k, by omega, htree⟩

private theorem forest_append {P : Program L} {β : Type*} {G H : Goal L β} {n m : ℕ}
    (hG : Forest P β G n) (hH : Forest P β H m) : Forest P β (G ++ H) (n + m) := by
  induction G generalizing n with
  | nil => cases hG; simpa using hH
  | cons A G ih =>
      cases hG with
      | cons ht hf =>
          simpa only [List.cons_append, Nat.add_assoc] using Forest.cons ht (ih hf)

private theorem forest_split {P : Program L} {β : Type*} {G : Goal L β} {n : ℕ}
    (h : Forest P β G n) (i : Fin G.length) :
    ∃ p a r, Forest P β (G.take i.val) p ∧ Tree P β (G[i.val]) a ∧
      Forest P β (G.drop (i.val + 1)) r ∧ n = p + a + r := by
  induction G generalizing n with
  | nil => exact Fin.elim0 i
  | cons A G ih =>
      cases h with
      | @cons _ _ n m ht hf =>
          cases i using Fin.cases with
          | zero => exact ⟨0, n, m, Forest.nil, ht, hf, by omega⟩
          | succ i =>
              obtain ⟨p, a, r, hp, ha, hr, hm⟩ := ih hf i
              exact ⟨n + p, a, r, Forest.cons ht hp, ha, hr, by omega⟩

private theorem tree_root {P : Program L} {β : Type*} {A : Atom L β} {n : ℕ}
    (h : Tree P β A n) :
    ∃ c ∈ P, ∃ σ : Fin c.arity → L.Term β, ∃ m,
      c.head.subst σ = A ∧ Forest P β (goalSubst σ c.body) m ∧ m + 1 = n := by
  cases h with
  | node c hc σ hf => exact ⟨c, hc, σ, _, rfl, hf, rfl⟩

theorem tree_iff_least {P : Program L} {β : Type w} (A : Atom L β) :
    (∃ n, Tree P β A n) ↔ A ∈ FirstOrderHornRules.least (grounding P β) := by
  constructor
  · rintro ⟨n, ht⟩
    induction n using Nat.strong_induction_on generalizing A with
    | h n ih =>
        obtain ⟨c, hc, σ, m, rfl, hf, hn⟩ := tree_root ht
        apply (FirstOrderHornRules.least_model (grounding P β)).1
          (c.ground σ) ⟨c, hc, σ, rfl⟩
        intro B hB
        obtain ⟨k, hk, htree⟩ := forest_member hf B (List.mem_toFinset.mp hB)
        exact ih k (by omega) B htree
  · intro ha
    obtain ⟨n, hn⟩ := (FirstOrderHornRules.least_mem_iff_stage (grounding P β) A).mp ha
    clear ha
    induction n generalizing A with
    | zero => simp [FirstOrderHornRules.stage] at hn
    | succ n ih =>
        rcases hn with hprev | ⟨r, hr, rfl, hb⟩
        · exact ih A hprev
        · obtain ⟨c, hc, σ, rfl⟩ := hr
          obtain ⟨m, hf⟩ := forest_of_trees (goalSubst σ c.body)
            (fun B hB => ih B (hb B (List.mem_toFinset.mpr hB)))
          exact ⟨m + 1, Tree.node c hc σ hf⟩

theorem forest_decrease {P : Program L} {β : Type w} {G : Goal L β} {n : ℕ}
    (h : Forest P β G n) (i : Fin G.length) :
    ∃ c ∈ P, ∃ σ : Fin c.arity → L.Term β, ∃ m,
      c.head.subst σ = G[i.val] ∧
      Forest P β (G.take i.val ++ goalSubst σ c.body ++ G.drop (i.val + 1)) m ∧
      m + 1 = n := by
  obtain ⟨p, a, r, hp, ha, hr, hn⟩ := forest_split h i
  obtain ⟨c, hc, σ, m, hh, hb, hm⟩ := tree_root ha
  exact ⟨c, hc, σ, p + m + r, hh, forest_append (forest_append hp hb) hr, by omega⟩

inductive GroundRefutes (P : Program L) {β : Type w} (select : Selector L β) : Goal L β → Prop
  | done : GroundRefutes P select []
  | step {G} (hne : G ≠ []) (c : Clause L) (hc : c ∈ P)
      (σ : Fin c.arity → L.Term β)
      (head : c.head.subst σ = G[(select G hne).val]) :
      GroundRefutes P select
        (G.take (select G hne).val ++ goalSubst σ c.body ++ G.drop ((select G hne).val + 1)) →
          GroundRefutes P select G

theorem ground_refutation_complete {P : Program L} {β : Type w}
    (select : Selector L β) (G : Goal L β)
    (h : ∀ A ∈ G, A ∈ FirstOrderHornRules.least (grounding P β)) :
    GroundRefutes P select G := by
  obtain ⟨n, hf⟩ := forest_of_trees G (fun A hA => (tree_iff_least A).mpr (h A hA))
  clear h
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
      by_cases hne : G = []
      · subst G
        exact GroundRefutes.done
      · obtain ⟨c, hc, σ, m, hh, hb, hm⟩ := forest_decrease hf (select G hne)
        exact GroundRefutes.step hne c hc σ hh (ih m (by omega) _ hb)

theorem one_step_lifting [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)]
    {P : Program L} {U : Finset ℕ} {G : Goal L ℕ} (tracked : goalVars G ⊆ U)
    (i : Fin G.length) {β : Type} (σ : ℕ → L.Term β) (c : Clause L) (hc : c ∈ P)
    (κ : Fin c.arity → L.Term β) (head : c.head.subst κ = (G[i.val]).subst σ) :
    ∃ d : StepData P U G i,
      d.clause = c ∧ d.names = freshInjection U d.clause.arity ∧
      solveAtoms (G[i.val]) (variantHead d.clause d.names) = some d.unifier ∧
      ∃ ρ : ℕ → L.Term β,
        goalSubst ρ (resolvent d) =
          goalSubst σ (G.take i.val) ++ goalSubst κ c.body ++ goalSubst σ (G.drop (i.val + 1)) ∧
        ∀ x ∈ U, (d.unifier x).subst ρ = σ x := by
  classical
  let ν := freshInjection U c.arity
  let γ : ℕ → L.Term β := Function.extend ν κ σ
  have hν (j : Fin c.arity) : γ (ν j) = κ j :=
    ν.injective.extend_apply κ σ j
  have hU (x : ℕ) (hx : x ∈ U) : γ x = σ x := by
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    exact fresh_away U c.arity j (hj ▸ hx)
  have hhead : (variantHead c ν).subst γ = c.head.subst κ := by
    rw [variantHead, Atom.subst_subst]
    congr 1
    funext j
    exact hν j
  have hsel : (G[i.val]).subst γ = (G[i.val]).subst σ :=
    atom_subst_agree _ γ σ (fun x hx => hU x
      (tracked (atom_vars_in_goal (List.getElem_mem i.isLt) hx)))
  have hγ : (G[i.val]).subst γ = (variantHead c ν).subst γ := by
    rw [hhead, hsel]
    exact head.symm
  obtain ⟨μ, hμ⟩ := solve_atoms_complete (G[i.val]) (variantHead c ν) γ hγ
  have hMGU := solve_atoms_sound (G[i.val]) (variantHead c ν) μ hμ
  obtain ⟨ρ, hρ⟩ := hMGU.2 β γ ((pair_unifies _ _ γ).mpr hγ)
  let d : StepData P U G i :=
    ⟨c, hc, ν, fresh_away U c.arity, tracked, μ, hMGU⟩
  refine ⟨d, rfl, rfl, hμ, ρ, ?_, ?_⟩
  · change goalSubst ρ (goalSubst μ
      (G.take i.val ++ variantBody c ν ++ G.drop (i.val + 1))) = _
    rw [goal_subst_subst]
    have hcomp : (fun x => (μ x).subst ρ) = γ := funext hρ
    rw [hcomp]
    have hp : goalSubst γ (G.take i.val) = goalSubst σ (G.take i.val) :=
      goal_subst_agree _ γ σ (fun x hx => hU x
        (tracked (goal_vars_mono (fun _ h => List.mem_of_mem_take h) hx)))
    have hd : goalSubst γ (G.drop (i.val + 1)) = goalSubst σ (G.drop (i.val + 1)) :=
      goal_subst_agree _ γ σ (fun x hx => hU x
        (tracked (goal_vars_mono (fun _ h => List.mem_of_mem_drop h) hx)))
    have hb : goalSubst γ (variantBody c ν) = goalSubst κ c.body := by
      rw [variantBody, goal_subst_subst]
      congr 1
      funext j
      exact hν j
    calc
      goalSubst γ (G.take i.val ++ variantBody c ν ++ G.drop (i.val + 1)) =
          goalSubst γ (G.take i.val) ++ goalSubst γ (variantBody c ν) ++
            goalSubst γ (G.drop (i.val + 1)) := by simp only [goalSubst, List.map_append]
      _ = _ := by rw [hp, hb, hd]
  · intro x hx
    exact (hρ x).trans (hU x hx)

inductive CanonicalRefutes [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] (P : Program L) (select : Selector L ℕ) :
    Finset ℕ → Goal L ℕ → Substitution L → Prop
  | done (U) : CanonicalRefutes P select U [] Term.var
  | step {U G τ} (hne : G ≠ []) (d : StepData P U G (select G hne))
      (variant : d.names = freshInjection U d.clause.arity)
      (solver : solveAtoms (G[(select G hne).val]) (variantHead d.clause d.names) = some d.unifier) :
      CanonicalRefutes P select (nextUsed d) (resolvent d) τ →
        CanonicalRefutes P select U G (TermUnification.compose τ d.unifier)

theorem canonical_refutes [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] {P : Program L} {select U G θ}
    (h : CanonicalRefutes P select U G θ) : Refutes P select U G θ := by
  induction h with
  | done U => exact Refutes.done U
  | step hne d _ _ _ ih => exact Refutes.step hne d ih

theorem answer_completeness [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)]
    {P : Program L} (select : Selector L ℕ) {U : Finset ℕ} {G : Goal L ℕ}
    (tracked : goalVars G ⊆ U) {β : Type} (σ : ℕ → L.Term β)
    (h : ∀ A ∈ goalSubst σ G, A ∈ FirstOrderHornRules.least (grounding P β)) :
    ∃ θ, CanonicalRefutes P select U G θ ∧
      ∃ δ : ℕ → L.Term β, ∀ x ∈ U, (θ x).subst δ = σ x := by
  obtain ⟨n, hf⟩ := forest_of_trees (goalSubst σ G)
    (fun A hA => (tree_iff_least A).mpr (h A hA))
  clear h
  induction n using Nat.strong_induction_on generalizing U G σ with
  | h n ih =>
      by_cases hne : G = []
      · subst G
        exact ⟨Term.var, CanonicalRefutes.done U, σ, fun _ _ => rfl⟩
      · let i := select G hne
        let j : Fin (goalSubst σ G).length :=
          ⟨i.val, by simpa only [goalSubst, List.length_map] using i.isLt⟩
        obtain ⟨c, hc, κ, m, hh, hb, hm⟩ := forest_decrease hf j
        have hhead : c.head.subst κ = (G[i.val]).subst σ := by
          simpa only [j, goalSubst, List.getElem_map] using hh
        obtain ⟨d, _, hnames, hsolve, ρ, hnext, hfactor⟩ :=
          one_step_lifting tracked i σ c hc κ hhead
        have hforest : Forest P β (goalSubst ρ (resolvent d)) m := by
          rw [hnext]
          simpa only [j, goalSubst, List.map_take, List.map_drop] using hb
        obtain ⟨τ, hτ, δ, hδ⟩ := ih m (by omega) (resolvent_tracked d) ρ hforest
        refine ⟨TermUnification.compose τ d.unifier,
          CanonicalRefutes.step hne d hnames hsolve hτ, δ, ?_⟩
        intro x hx
        change ((d.unifier x).subst τ).subst δ = σ x
        rw [FirstOrderProofs.term_subst_subst]
        refine (term_subst_agree (d.unifier x) (fun y => (τ y).subst δ) ρ ?_).trans
          (hfactor x hx)
        intro y hy
        apply hδ y
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left _ hx, hy⟩)

theorem ground_answer_completeness {P : Program L} (select : Selector L ℕ)
    {U : Finset ℕ} {G : Goal L ℕ} (tracked : goalVars G ⊆ U)
    {β : Type} (σ : ℕ → L.Term β)
    (h : ∀ A ∈ goalSubst σ G, A ∈ FirstOrderHornRules.least (grounding P β)) :
    ∃ θ, Refutes P select U G θ ∧
      ∃ δ : ℕ → L.Term β, ∀ x ∈ U, (θ x).subst δ = σ x := by
  classical
  let : ∀ n, DecidableEq (L.Functions n) := fun _ => Classical.decEq _
  let : ∀ n, DecidableEq (L.Relations n) := fun _ => Classical.decEq _
  obtain ⟨θ, hθ, δ, hδ⟩ := answer_completeness select tracked σ h
  exact ⟨θ, canonical_refutes hθ, δ, hδ⟩

@[instance_reducible] noncomputable def parameterInterpretation {β : Type w} (I : Set (Atom L β)) :
    L.Structure (L.Term β) where
  funMap := Term.func
  RelMap r a := (⟨_, r, a⟩ : Atom L β) ∈ I

theorem parameter_evaluation {α : Type z} {β : Type w} (I : Set (Atom L β)) (t : L.Term α)
    (σ : α → L.Term β) :
    @Term.realize L (L.Term β) (parameterInterpretation I) α σ t = t.subst σ := by
  let : L.Structure (L.Term β) := parameterInterpretation I
  induction t with
  | var => rfl
  | func f ts ih =>
      change Term.func f (fun i => (ts i).realize σ) = Term.func f (fun i => (ts i).subst σ)
      exact congrArg (Term.func f) (funext ih)

theorem parameter_atom {α : Type z} {β : Type w} (I : Set (Atom L β))
    (A : Atom L α) (σ : α → L.Term β) :
    @Atom.Realize L α (L.Term β) (parameterInterpretation I) A σ ↔ A.subst σ ∈ I := by
  cases A with
  | mk n r ts =>
      change (⟨n, r, fun i => @Term.realize L (L.Term β) (parameterInterpretation I)
        α σ (ts i)⟩ : Atom L β) ∈ I ↔ _
      simp only [parameter_evaluation, Atom.subst]

theorem parameter_model (P : Program L) :
    @ProgramModels L P (L.Term Unit)
      (parameterInterpretation (FirstOrderHornRules.least (grounding P Unit))) := by
  intro c hc σ hb
  apply (parameter_atom _ c.head σ).mpr
  apply (FirstOrderHornRules.least_model (grounding P Unit)).1 (c.ground σ) ⟨c, hc, σ, rfl⟩
  intro A hA
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
  exact (parameter_atom _ B σ).mp (hb B hB)

def freshTermsEquiv : GroundTerm (freshLanguage L) ≃ L.Term Unit :=
  Term.constantsVarsEquiv.trans (Term.relabelEquiv (Equiv.sumEmpty Unit Empty))

theorem fresh_terms_generator :
    (freshTermsEquiv (L := L)).symm (.var ()) = freshTerm L := by
  rfl

theorem fresh_terms_function {n} (f : L.Functions n) (a : Fin n → L.Term Unit) :
    (freshTermsEquiv (L := L)).symm (.func f a) =
      .func (Sum.inl f) (fun i => (freshTermsEquiv (L := L)).symm (a i)) := by
  rfl

structure Query (L : Language.{u, v}) where
  arity : ℕ
  atoms : Goal L (Fin arity)

def Query.toGoal (q : Query L) : Goal L ℕ := goalSubst (fun i => .var i.val) q.atoms

def Query.formula (q : Query L) : L.Formula (Fin q.arity) :=
  (q.atoms.map Atom.toFormula).foldr (· ⊓ ·) ⊤

def Query.sentence (q : Query L) : L.Sentence :=
  (BoundedFormula.relabel (Sum.inr : Fin q.arity → Empty ⊕ Fin q.arity) q.formula).exs

theorem query_sentence_realize (q : Query L) (M : Type z) [L.Structure M] :
    M ⊨ q.sentence ↔ ∃ a : Fin q.arity → M, GoalRealize q.atoms a := by
  simp only [Query.sentence, Sentence.Realize, BoundedFormula.realize_exs,
    BoundedFormula.realize_relabel, Function.comp_def, Sum.elim_inr,
    Fin.castAdd_zero, Nat.add_zero, Fin.cast_eq_self]
  apply exists_congr
  intro a
  have he : (fun x : Fin 0 => a (Fin.natAdd q.arity x)) = default := Subsingleton.elim _ _
  rw [he]
  simp only [Query.formula, BoundedFormula.realize_foldr_inf, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    ← Atom.realize_toFormula, GoalRealize, Formula.Realize]

private def scopedTerm (n : ℕ) :
    (t : L.Term ℕ) → (∀ x ∈ t.varFinset, x < n) → L.Term (Fin n)
  | .var x, h => .var ⟨x, h x (Finset.mem_singleton_self x)⟩
  | .func f ts, h => .func f (fun i => scopedTerm n (ts i)
      (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)))

private theorem scoped_term_back (n : ℕ) (t : L.Term ℕ)
    (h : ∀ x ∈ t.varFinset, x < n) :
    (scopedTerm n t h).subst (fun i => .var i.val) = t := by
  induction t with
  | var => rfl
  | func f ts ih =>
      apply congrArg (Term.func f)
      funext i
      exact ih i _

private def scopedAtom (n : ℕ) (A : Atom L ℕ) (h : ∀ x ∈ atomVars A, x < n) :
    Atom L (Fin n) :=
  ⟨A.arity, A.relation, fun i => scopedTerm n (A.terms i)
    (fun x hx => h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩))⟩

private theorem scoped_atom_back (n : ℕ) (A : Atom L ℕ)
    (h : ∀ x ∈ atomVars A, x < n) :
    (scopedAtom n A h).subst (fun i => .var i.val) = A := by
  cases A with
  | mk k r ts =>
      apply congrArg (Atom.mk k r)
      funext i
      exact scoped_term_back n (ts i) _

theorem every_goal_scoped (G : Goal L ℕ) : ∃ q : Query L, q.toGoal = G := by
  let n := (goalVars G).sup id + 1
  let restricted : {A : Atom L ℕ // A ∈ G} → Atom L (Fin n) := fun A =>
    scopedAtom n A.val (fun x hx => Nat.lt_succ_of_le
      (Finset.le_sup (f := id) (atom_vars_in_goal A.property hx)))
  let q : Query L := ⟨n, G.attach.map restricted⟩
  refine ⟨q, ?_⟩
  change (G.attach.map restricted).map (Atom.subst (fun i => Term.var i.val)) = G
  rw [List.map_map]
  calc
    _ = G.attach.map Subtype.val := by
      apply List.map_congr_left
      intro A _
      exact scoped_atom_back n A.val _
    _ = G := List.attach_map_subtype_val G

theorem query_instance {β : Type} [Nonempty (L.Term β)] (q : Query L)
    (κ : Fin q.arity → L.Term β) :
    ∃ σ : ℕ → L.Term β, goalSubst σ q.toGoal = goalSubst κ q.atoms := by
  classical
  let σ : ℕ → L.Term β := fun j => if h : j < q.arity then κ ⟨j, h⟩
    else Classical.choice inferInstance
  refine ⟨σ, ?_⟩
  rw [Query.toGoal, goal_subst_subst]
  congr 1
  funext i
  simp [σ]

theorem query_completeness [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] (P : Program L) (select : Selector L ℕ) (q : Query L) :
    programTheory P ⊨ᵇ q.sentence ↔
      ∃ θ, CanonicalRefutes P select (goalVars q.toGoal) q.toGoal θ := by
  constructor
  · intro h
    let I := FirstOrderHornRules.least (grounding P Unit)
    let : L.Structure (L.Term Unit) := parameterInterpretation I
    let : L.Term Unit ⊨ programTheory P :=
      (program_models_iff P (L.Term Unit)).mpr (parameter_model P)
    obtain ⟨κ, hκ⟩ := (query_sentence_realize q (L.Term Unit)).mp
      (h.realize_sentence (L.Term Unit))
    obtain ⟨σ, hσ⟩ := query_instance q κ
    have hG : ∀ A ∈ goalSubst σ q.toGoal, A ∈ I := by
      rw [hσ]
      intro A hA
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
      exact (parameter_atom I B κ).mp (hκ B hB)
    obtain ⟨θ, hθ, _, _⟩ := answer_completeness select (Finset.Subset.refl _) σ hG
    exact ⟨θ, hθ⟩
  · rintro ⟨θ, hθ⟩
    apply Theory.models_sentence_iff.mpr
    intro M
    let a : ℕ → M := fun _ => Classical.choice inferInstance
    have hG := answer_sound (canonical_refutes hθ) M
      ((program_models_iff P M).mp M.is_model) a
    have ht := (goal_subst_realize q.toGoal θ a).mp hG
    apply (query_sentence_realize q M).mpr
    refine ⟨fun i => (θ i.val).realize a, ?_⟩
    exact (goal_subst_realize q.atoms (fun i => Term.var i.val)
      (fun x => (θ x).realize a)).mp ht

theorem query_refutation_iff (P : Program L) (select : Selector L ℕ) (q : Query L) :
    programTheory P ⊨ᵇ q.sentence ↔
      ∃ θ, Refutes P select (goalVars q.toGoal) q.toGoal θ := by
  classical
  let : ∀ n, DecidableEq (L.Functions n) := fun _ => Classical.decEq _
  let : ∀ n, DecidableEq (L.Relations n) := fun _ => Classical.decEq _
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := (query_completeness P select q).mp h
    exact ⟨θ, canonical_refutes hθ⟩
  · rintro ⟨θ, hθ⟩
    apply Theory.models_sentence_iff.mpr
    intro M
    let a : ℕ → M := fun _ => Classical.choice inferInstance
    have hG := answer_sound hθ M ((program_models_iff P M).mp M.is_model) a
    have ht := (goal_subst_realize q.toGoal θ a).mp hG
    apply (query_sentence_realize q M).mpr
    exact ⟨fun i => (θ i.val).realize a,
      (goal_subst_realize q.atoms (fun i => Term.var i.val)
        (fun x => (θ x).realize a)).mp ht⟩

structure SearchState (L : Language.{u, v}) where
  goal : Goal L ℕ
  used : Finset ℕ
  answer : Substitution L

def rootState (G : Goal L ℕ) : SearchState L := ⟨G, goalVars G, Term.var⟩

def canonicalStep [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] (P : Program L) (U : Finset ℕ) (G : Goal L ℕ)
    (i : Fin G.length) (tracked : goalVars G ⊆ U) (c : Clause L) (hc : c ∈ P) :
    Option (StepData P U G i) :=
  (solveAtoms (G[i.val]) (variantHead c (freshInjection U c.arity))).pmap
    (fun μ hμ => ⟨c, hc, freshInjection U c.arity, fresh_away U c.arity,
      tracked, μ, solve_atoms_sound _ _ μ hμ⟩) (fun _ h => h)

def children [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]
    (P : Program L) (select : Selector L ℕ) (s : SearchState L) : List (SearchState L) :=
  if hne : s.goal = [] then [] else
    if tracked : goalVars s.goal ⊆ s.used then
      P.attach.filterMap (fun c =>
        (canonicalStep P s.used s.goal (select s.goal hne) tracked c.val c.property).map
          (fun d => ⟨resolvent d, nextUsed d, TermUnification.compose d.unifier s.answer⟩))
    else []

def frontier [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]
    (P : Program L) (select : Selector L ℕ) (s : SearchState L) : ℕ → List (SearchState L)
  | 0 => [s]
  | n + 1 => (frontier P select s n).flatMap (children P select)

theorem branching_bound [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] (P : Program L) (select : Selector L ℕ) (s : SearchState L) :
    (children P select s).length ≤ P.length := by
  unfold children
  split
  · simp
  · split
    · exact (List.length_filterMap_le _ _).trans_eq List.length_attach
    · simp

private theorem canonical_step_eq [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] {P : Program L} {U G i}
    (d : StepData P U G i) (hn : d.names = freshInjection U d.clause.arity)
    (hs : solveAtoms (G[i.val]) (variantHead d.clause d.names) = some d.unifier)
    (tracked : goalVars G ⊆ U) :
    canonicalStep P U G i tracked d.clause d.member = some d := by
  cases d with
  | mk c hc names fresh oldtracked μ hMGU =>
      dsimp at hn hs
      subst names
      simp only [canonicalStep, hs, Option.pmap_some]

private theorem canonical_child_mem [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] {P : Program L} {select : Selector L ℕ}
    {U G} (hne : G ≠ []) (d : StepData P U G (select G hne))
    (hn : d.names = freshInjection U d.clause.arity)
    (hs : solveAtoms (G[(select G hne).val]) (variantHead d.clause d.names) = some d.unifier)
    (α : Substitution L) :
    (⟨resolvent d, nextUsed d, TermUnification.compose d.unifier α⟩ : SearchState L) ∈
      children P select ⟨G, U, α⟩ := by
  unfold children
  simp only [hne, ↓reduceDIte, d.tracked]
  apply List.mem_filterMap.mpr
  refine ⟨⟨d.clause, d.member⟩, List.mem_attach _ _, ?_⟩
  rw [canonical_step_eq d hn hs]
  rfl

private theorem frontier_child [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] {P : Program L} {select : Selector L ℕ}
    {s t : SearchState L} (ht : t ∈ children P select s) {n : ℕ} {u : SearchState L}
    (hu : u ∈ frontier P select t n) : u ∈ frontier P select s (n + 1) := by
  induction n generalizing u with
  | zero =>
      have he : u = t := List.mem_singleton.mp hu
      subst u
      change t ∈ children P select s ++ []
      simpa only [List.append_nil] using ht
  | succ n ih =>
      obtain ⟨v, hv, hu⟩ := List.mem_flatMap.mp hu
      exact List.mem_flatMap.mpr ⟨v, ih hv, hu⟩

theorem refutation_in_frontier [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] {P : Program L} {select U G θ}
    (h : CanonicalRefutes P select U G θ) (α : Substitution L) :
    ∃ n, ∃ s ∈ frontier P select ⟨G, U, α⟩ n,
      s.goal = [] ∧ s.answer = TermUnification.compose θ α := by
  induction h generalizing α with
  | done U =>
      exact ⟨0, ⟨[], U, α⟩, List.mem_singleton_self _, rfl,
        (TermUnification.compose_id α).1.symm⟩
  | @step U G τ hne d hn hs _ ih =>
      obtain ⟨n, s, hmem, hg, ha⟩ := ih (TermUnification.compose d.unifier α)
      exact ⟨n + 1, s, frontier_child (canonical_child_mem hne d hn hs α) hmem,
        hg, ha.trans (TermUnification.compose_assoc τ d.unifier α)⟩

theorem breadth_first_complete [∀ n, DecidableEq (L.Functions n)]
    [∀ n, DecidableEq (L.Relations n)] (P : Program L) (select : Selector L ℕ) (q : Query L)
    (h : programTheory P ⊨ᵇ q.sentence) :
    ∃ n, ∃ s ∈ frontier P select (rootState q.toGoal) n, s.goal = [] := by
  obtain ⟨θ, hθ⟩ := (query_completeness P select q).mp h
  obtain ⟨n, s, hs, hg, _⟩ := refutation_in_frontier hθ Term.var
  exact ⟨n, s, hs, hg⟩

end Lemmatheca.MathematicalLogic.DefiniteHornSldResolution
