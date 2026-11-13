import Lemmatheca.DefiniteHornSldResolution.DefiniteHornSldResolution

/-! The corrected addition query and a native depth-first looping branch. -/
namespace Lemmatheca.MathematicalLogic.DefiniteHornSldResolution

open FirstOrder FirstOrder.Language HerbrandModels

universe u v

def leftmost {L : Language} {α : Type*} : Selector L α :=
  fun _ h => ⟨0, List.length_pos_iff_ne_nil.mpr h⟩

inductive AdditionFunction : ℕ → Type
  | zero : AdditionFunction 0
  | successor : AdditionFunction 1
  deriving DecidableEq

inductive AdditionRelation : ℕ → Type
  | add : AdditionRelation 3
  deriving DecidableEq

def additionLanguage : Language := ⟨AdditionFunction, AdditionRelation⟩

def zero {α : Type*} : additionLanguage.Term α := .func .zero Fin.elim0

def successor {α : Type*} (t : additionLanguage.Term α) : additionLanguage.Term α :=
  .func .successor (fun _ => t)

def add {α : Type*} (a b c : additionLanguage.Term α) : Atom additionLanguage α :=
  ⟨3, .add, ![a, b, c]⟩

def additionFact : Clause additionLanguage := ⟨1, [], add zero (.var 0) (.var 0)⟩

def additionRecursive : Clause additionLanguage :=
  ⟨3, [add (.var 0) (.var 1) (.var 2)],
    add (successor (.var 0)) (.var 1) (successor (.var 2))⟩

def additionProgram : Program additionLanguage := [additionFact, additionRecursive]

def additionGoal : Goal additionLanguage ℕ :=
  [add (successor zero) (.var 0) (successor (successor zero))]

def additionMiddle : Goal additionLanguage ℕ := [add zero (.var 0) (successor zero)]

def additionFirstUnifier : Substitution additionLanguage :=
  fun j => if j = 1 then zero else if j = 2 then .var 0
    else if j = 3 then successor zero else .var j

def additionSecondUnifier : Substitution additionLanguage :=
  fun j => if j = 0 ∨ j = 4 then successor zero else .var j

@[simp] private theorem zero_subst {α β : Type*} (σ : α → additionLanguage.Term β) :
    (zero : additionLanguage.Term α).subst σ = zero := by
  simp only [zero, Term.subst]
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] private theorem successor_subst {α β : Type*} (t : additionLanguage.Term α)
    (σ : α → additionLanguage.Term β) :
    (successor t).subst σ = successor (t.subst σ) := rfl

@[simp] private theorem add_subst {α β : Type*} (a b c : additionLanguage.Term α)
    (σ : α → additionLanguage.Term β) :
    (add a b c).subst σ = add (a.subst σ) (b.subst σ) (c.subst σ) := by
  change (Atom.mk (L := additionLanguage) 3 AdditionRelation.add
    (fun i => (![a, b, c] i).subst σ)) = _
  apply congrArg (Atom.mk (L := additionLanguage) 3 AdditionRelation.add)
  funext i
  fin_cases i <;> rfl

private theorem successor_injective {α : Type*} {a b : additionLanguage.Term α}
    (h : successor a = successor b) : a = b := by
  exact congrFun (eq_of_heq (Term.func.inj h).2.2) 0

private theorem add_arguments {α : Type*} {a b c d e f : additionLanguage.Term α}
    (h : add a b c = add d e f) : a = d ∧ b = e ∧ c = f := by
  have ht := eq_of_heq (Atom.mk.inj h).2.2
  exact ⟨congrFun ht 0, congrFun ht 1, congrFun ht 2⟩

private theorem pair_mgu {L : Language.{u, v}} (A B : Atom L ℕ) (μ : Substitution L)
    (h : A.subst μ = B.subst μ)
    (factor : ∀ (β : Type) (σ : ℕ → L.Term β), A.subst σ = B.subst σ →
      TermUnification.Factors σ μ) : FirstOrderResolution.AtomMGU.{u, v, 0} {A, B} μ := by
  classical
  constructor
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl
  · intro β σ hσ
    exact factor β σ (hσ A (by simp) B (by simp))

private theorem addition_first_head :
    variantHead additionRecursive (freshInjection {0} 3) =
      add (successor (.var 1)) (.var 2) (successor (.var 3)) := by
  change (add (successor (Term.var (0 : Fin 3))) (.var 1) (successor (.var 2))).subst
    (fun i => .var (freshInjection {0} 3 i)) = _
  rw [add_subst, successor_subst, successor_subst]
  rfl

private theorem addition_second_head :
    variantHead additionFact (freshInjection {0, 1, 2, 3} 1) = add zero (.var 4) (.var 4) := by
  change (add zero (Term.var (0 : Fin 1)) (.var 0)).subst
    (fun i => .var (freshInjection {0, 1, 2, 3} 1 i)) = _
  rw [add_subst, zero_subst]
  rfl

def additionFirstStep : StepData additionProgram {0} additionGoal ⟨0, by decide⟩ where
  clause := additionRecursive
  member := by simp [additionProgram]
  names := freshInjection {0} 3
  fresh := fresh_away {0} 3
  tracked := by
    intro x hx
    simp only [additionGoal, goalVars, Finset.union_empty] at hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    fin_cases i
    · simp [add, successor, zero, Term.varFinset] at hi
    · exact hi
    · simp [add, successor, zero, Term.varFinset] at hi
  unifier := additionFirstUnifier
  mostGeneral := by
    rw [addition_first_head]
    apply pair_mgu
    · simp [additionGoal, additionFirstUnifier]
    · intro β σ hσ
      simp only [additionGoal, List.getElem_cons_zero, add_subst, successor_subst,
        zero_subst, Term.subst] at hσ
      obtain ⟨h₁, h₂, h₃⟩ := add_arguments hσ
      have hu := successor_injective h₁
      have hw := successor_injective h₃
      refine ⟨σ, ?_⟩
      intro x
      by_cases h1 : x = 1
      · subst x
        simpa [additionFirstUnifier] using hu
      · by_cases h2 : x = 2
        · subst x
          simpa [additionFirstUnifier] using h₂
        · by_cases h3 : x = 3
          · subst x
            simpa [additionFirstUnifier] using hw
          · simp [additionFirstUnifier, h1, h2, h3]

def additionSecondStep : StepData additionProgram {0, 1, 2, 3} additionMiddle ⟨0, by decide⟩ where
  clause := additionFact
  member := by simp [additionProgram]
  names := freshInjection {0, 1, 2, 3} 1
  fresh := fresh_away {0, 1, 2, 3} 1
  tracked := by
    intro x hx
    simp only [additionMiddle, goalVars, Finset.union_empty] at hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    fin_cases i <;> simp [add, successor, zero, Term.varFinset] at hi ⊢
    exact Or.inl hi
  unifier := additionSecondUnifier
  mostGeneral := by
    rw [addition_second_head]
    apply pair_mgu
    · simp [additionMiddle, additionSecondUnifier]
    · intro β σ hσ
      simp only [additionMiddle, List.getElem_cons_zero, add_subst, successor_subst,
        zero_subst, Term.subst] at hσ
      obtain ⟨_, h₀, h₄⟩ := add_arguments hσ
      refine ⟨σ, ?_⟩
      intro x
      by_cases hx : x = 0 ∨ x = 4
      · rcases hx with rfl | rfl
        · simpa [additionSecondUnifier] using h₄.trans h₀.symm
        · simpa [additionSecondUnifier] using h₄
      · simp [additionSecondUnifier, hx]

theorem addition_step_values :
    resolvent additionFirstStep = additionMiddle ∧
      nextUsed additionFirstStep = {0, 1, 2, 3} ∧
      resolvent additionSecondStep = [] := by
  refine ⟨?_, ?_, rfl⟩
  · change goalSubst additionFirstUnifier
      (goalSubst (fun i : Fin 3 => Term.var (freshInjection {0} 3 i))
        [add (.var 0) (.var 1) (.var 2)]) = additionMiddle
    rw [goal_subst_subst]
    simp only [goalSubst, List.map_cons, List.map_nil, add_subst, Term.subst]
    rfl
  · decide

theorem addition_refutation :
    Refutes additionProgram leftmost {0} additionGoal
      (TermUnification.compose additionSecondUnifier additionFirstUnifier) ∧
      (TermUnification.compose additionSecondUnifier additionFirstUnifier) 0 = successor zero := by
  have hn₀ : additionGoal ≠ [] := by simp [additionGoal]
  have hn₁ : additionMiddle ≠ [] := by simp [additionMiddle]
  have hend : Refutes additionProgram leftmost (nextUsed additionSecondStep)
      (resolvent additionSecondStep) Term.var := by
    rw [addition_step_values.2.2]
    exact Refutes.done _
  have hsecond := Refutes.step (select := leftmost) hn₁ additionSecondStep hend
  rw [(TermUnification.compose_id additionSecondStep.unifier).1] at hsecond
  have htail : Refutes additionProgram leftmost (nextUsed additionFirstStep)
      (resolvent additionFirstStep) additionSecondUnifier := by
    rw [addition_step_values.1, addition_step_values.2.1]
    exact hsecond
  exact ⟨Refutes.step (select := leftmost) hn₀ additionFirstStep htail, rfl⟩

theorem addition_least_instance :
    add (successor zero) (successor zero) (successor (successor zero)) ∈
      FirstOrderHornRules.least (grounding additionProgram Empty) := by
  have hfact : Tree additionProgram Empty (add zero (successor zero) (successor zero)) 1 := by
    have ht := Tree.node (P := additionProgram) additionFact (by simp [additionProgram])
      (fun _ => (successor zero : GroundTerm additionLanguage)) Forest.nil
    simpa [additionFact] using ht
  let κ : Fin 3 → GroundTerm additionLanguage := ![zero, successor zero, successor zero]
  have hb : Forest additionProgram Empty (goalSubst κ additionRecursive.body) 1 := by
    simpa [goalSubst, additionRecursive, κ] using Forest.cons hfact Forest.nil
  have ht := Tree.node (P := additionProgram) additionRecursive (by simp [additionProgram]) κ hb
  apply (tree_iff_least _).mp
  refine ⟨2, ?_⟩
  simpa [additionRecursive, κ] using ht

instance additionAllTriplesStructure : additionLanguage.Structure ℕ where
  funMap f a := by
    cases f with
    | zero => exact 0
    | successor => exact a 0 + 1
  RelMap _ _ := True

theorem addition_not_exact :
    ProgramModels additionProgram ℕ ∧
      (add zero zero (successor zero) : Atom additionLanguage Empty).Realize (M := ℕ) Empty.elim ∧
      (0 : ℕ) + 0 ≠ 1 := by
  exact ⟨fun _ _ _ _ => True.intro, True.intro, by decide⟩

inductive LoopRelation : ℕ → Type
  | p : LoopRelation 0
  deriving DecidableEq

def loopLanguage : Language := ⟨fun _ => Empty, LoopRelation⟩

instance loopFunctionEquality : ∀ n, DecidableEq (loopLanguage.Functions n) :=
  fun _ => inferInstanceAs (DecidableEq Empty)

instance loopRelationEquality : ∀ n, DecidableEq (loopLanguage.Relations n) :=
  fun n => inferInstanceAs (DecidableEq (LoopRelation n))

def pAtom {α : Type*} : Atom loopLanguage α := ⟨0, .p, Fin.elim0⟩

def recursiveLoopClause : Clause loopLanguage := ⟨0, [pAtom], pAtom⟩
def loopFact : Clause loopLanguage := ⟨0, [], pAtom⟩
def loopProgram : Program loopLanguage := [recursiveLoopClause, loopFact]
def loopRoot : SearchState loopLanguage := rootState [pAtom]

@[simp] private theorem p_subst {α β : Type*} (σ : α → loopLanguage.Term β) :
    (pAtom : Atom loopLanguage α).subst σ = pAtom := by
  change (Atom.mk (L := loopLanguage) 0 LoopRelation.p (fun i => (Fin.elim0 i : loopLanguage.Term α).subst σ)) = _
  apply congrArg (Atom.mk (L := loopLanguage) 0 LoopRelation.p)
  funext i
  exact Fin.elim0 i

private theorem loop_solve : solveAtoms (pAtom : Atom loopLanguage ℕ) pAtom = some Term.var := by
  change TermUnification.unify [] = some Term.var
  have hs : TermUnification.Supported (∅ : Finset ℕ) ([] : TermUnification.Problem loopLanguage) :=
    fun _ h => h
  change TermUnification.solve ∅ [] hs = some Term.var
  rw [TermUnification.solve.eq_def]
  rfl

theorem loop_children :
    children loopProgram leftmost loopRoot = [loopRoot, ⟨[], ∅, Term.var⟩] := by
  simp [children, loopRoot, rootState, loopProgram, recursiveLoopClause, loopFact,
    goalVars, atomVars, variantHead, variantBody, canonicalStep, resolvent,
    nextUsed, goalSubst, loop_solve]
  exact ⟨(TermUnification.compose_id Term.var).1, rfl, (TermUnification.compose_id Term.var).1⟩

def firstChild (s : SearchState loopLanguage) : SearchState loopLanguage :=
  (children loopProgram leftmost s).headD s

theorem depth_first_loops (n : ℕ) :
    ((firstChild^[n]) loopRoot).goal = [pAtom] := by
  have hfix : firstChild loopRoot = loopRoot := by
    rw [firstChild, loop_children]
    rfl
  have hstate (k : ℕ) : (firstChild^[k]) loopRoot = loopRoot := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hfix, ih]
  rw [hstate n]
  rfl

theorem loop_success :
    Refutes loopProgram leftmost ∅ [pAtom] Term.var ∧
      pAtom ∈ FirstOrderHornRules.least (grounding loopProgram Unit) ∧
      ∃ s ∈ frontier loopProgram leftmost loopRoot 1, s.goal = [] := by
  let d : StepData loopProgram ∅ [pAtom] ⟨0, by decide⟩ :=
    { clause := loopFact
      member := by simp [loopProgram]
      names := freshInjection ∅ 0
      fresh := fresh_away ∅ 0
      tracked := by
        simp [goalVars, atomVars, pAtom]
        rfl
      unifier := Term.var
      mostGeneral := by
        apply pair_mgu
        · simp [loopFact, variantHead]
        · intro β σ _
          exact ⟨σ, fun _ => rfl⟩ }
  have hd : resolvent d = [] := rfl
  have href : Refutes loopProgram leftmost ∅ [pAtom] Term.var := by
    have ht : Refutes loopProgram leftmost (nextUsed d) (resolvent d) Term.var := by
      rw [hd]
      exact Refutes.done _
    have hr := Refutes.step (select := leftmost) (by simp) d ht
    change Refutes loopProgram leftmost ∅ [pAtom] (TermUnification.compose Term.var Term.var) at hr
    rw [(TermUnification.compose_id Term.var).1] at hr
    exact hr
  have hleast : pAtom ∈ FirstOrderHornRules.least (grounding loopProgram Unit) := by
    have ht := Tree.node (P := loopProgram) loopFact (by simp [loopProgram])
      (Fin.elim0 : Fin 0 → loopLanguage.Term Unit) Forest.nil
    apply (tree_iff_least _).mp
    exact ⟨1, by simpa [loopFact] using ht⟩
  refine ⟨href, hleast, ⟨[], ∅, Term.var⟩, ?_, rfl⟩
  change (⟨[], ∅, Term.var⟩ : SearchState loopLanguage) ∈
    children loopProgram leftmost loopRoot ++ []
  rw [List.append_nil, loop_children]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

end Lemmatheca.MathematicalLogic.DefiniteHornSldResolution
