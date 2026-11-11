import Lemmatheca.TwoSatisfiability.FiniteTest
import Lemmatheca.DpllSatisfiability.Examples
import Mathlib.Tactic.FinCases


namespace Lemmatheca.Entry.TwoSatisfiability
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.DpllSatisfiability (Cnf opposite Models Sat)
open Lemmatheca.MathematicalLogic.TwoSatisfiability

def diamond : Cnf (Fin 3) :=
  [[⟨0,false⟩,⟨1,true⟩], [⟨1,false⟩,⟨2,true⟩],
   [⟨0,true⟩,⟨1,true⟩], [⟨2,false⟩,⟨1,true⟩]]

def diamondLiteralRank (l : PropLiteral (Fin 3)) : ℕ :=
  if l.atom = 0 then (if l.positive then 1 else 2) else (if l.positive then 3 else 0)

private theorem diamond_test (a b : PropLiteral (Fin 3)) :
    reachTest diamond a b = decide (diamondLiteralRank a = diamondLiteralRank b ∨
      diamondLiteralRank a = 0 ∨ diamondLiteralRank b = 3) := by
  revert a b
  decide

private theorem diamond_rank_bound (a : PropLiteral (Fin 3)) : diamondLiteralRank a ≤ 3 := by
  unfold diamondLiteralRank
  split <;> split <;> omega

theorem diamond_components (a b : PropLiteral (Fin 3)) :
    Mutual diamond a b ↔ diamondLiteralRank a = diamondLiteralRank b := by
  simp only [Mutual, ← reachTest_correct, diamond_test, decide_eq_true_eq]
  omega

theorem diamond_reach (a b : PropLiteral (Fin 3)) :
    Reach diamond a b ↔ diamondLiteralRank a = diamondLiteralRank b ∨
      diamondLiteralRank a = 0 ∨ diamondLiteralRank b = 3 := by
  rw [← reachTest_correct diamond a b, diamond_test]
  simp

def diamondRank : Component diamond → ℕ :=
  Quotient.lift diamondLiteralRank fun a b h => (diamond_components a b).mp h

def diamondRank' (C : Component diamond) : ℕ :=
  if diamondRank C = 1 then 2 else if diamondRank C = 2 then 1 else diamondRank C

theorem diamond_ranks : IsRank diamond diamondRank ∧ IsRank diamond diamondRank' := by
  have hfirst : IsRank diamond diamondRank := by
    constructor
    · intro C D
      refine Quotient.inductionOn₂ C D ?_
      intro a b h
      apply (component_eq diamond a b).mpr
      exact (diamond_components a b).mpr h
    · intro C D
      refine Quotient.inductionOn₂ C D ?_
      intro a b h
      have hr := (diamond_reach a b).mp ((component_le diamond a b).mp h)
      change diamondLiteralRank a ≤ diamondLiteralRank b
      have hb := diamond_rank_bound a
      rcases hr with h | h | h <;> omega
  refine ⟨hfirst, ?_⟩
  constructor
  · intro C D h
    apply hfirst.1
    dsimp [diamondRank'] at h
    split_ifs at h <;> omega
  · intro C D
    refine Quotient.inductionOn₂ C D ?_
    intro a b h
    have hr := (diamond_reach a b).mp ((component_le diamond a b).mp h)
    change (if diamondLiteralRank a = 1 then 2 else
      if diamondLiteralRank a = 2 then 1 else diamondLiteralRank a) ≤
      (if diamondLiteralRank b = 1 then 2 else
      if diamondLiteralRank b = 2 then 1 else diamondLiteralRank b)
    have ha := diamond_rank_bound a
    have hb := diamond_rank_bound b
    split_ifs <;> omega

theorem diamond_assignments :
    orderedAssignment diamond diamondRank = (fun p => decide (p ≠ 0)) ∧
    orderedAssignment diamond diamondRank' = (fun _ => true) ∧
    Models (orderedAssignment diamond diamondRank) diamond ∧
    Models (orderedAssignment diamond diamondRank') diamond := by
  have hfirst : orderedAssignment diamond diamondRank = (fun p => decide (p ≠ 0)) := by
    funext p
    fin_cases p <;> rfl
  have hsecond : orderedAssignment diamond diamondRank' = (fun _ => true) := by
    funext p
    fin_cases p <;> rfl
  refine ⟨hfirst,hsecond,?_,?_⟩
  · rw [hfirst]
    simp [diamond, Models, MathematicalLogic.TseitinEncoding.ListModels]
  · rw [hsecond]
    simp [diamond, Models, MathematicalLogic.TseitinEncoding.ListModels]

theorem unit_chain_cycle :
    List.IsChain (Edge (DpllSatisfiability.unitExample (0 : Fin 3) 1 2))
      [⟨0,false⟩,⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨2,false⟩,⟨1,false⟩,⟨0,false⟩] := by
  decide

theorem unit_chain_component :
    ∀ a b : PropLiteral (Fin 3),
      Mutual (DpllSatisfiability.unitExample (0 : Fin 3) 1 2) a b := by
  have ht : ∀ a b : PropLiteral (Fin 3),
      reachTest (DpllSatisfiability.unitExample (0 : Fin 3) 1 2) a b = true := by decide
  intro a b
  exact ⟨(reachTest_correct _ a b).mp (ht a b), (reachTest_correct _ b a).mp (ht b a)⟩

universe u
variable {α : Type u}

theorem empty_graph (a b : PropLiteral α) :
    ¬ Edge ([] : Cnf α) a b ∧ ¬ Edge ([[]] : Cnf α) a b ∧
    (Reach ([] : Cnf α) a b ↔ a = b) ∧
    (Reach ([[]] : Cnf α) a b ↔ a = b) := by
  have hr (Γ : Cnf α) (hn : ∀ x y, ¬ Edge Γ x y) : Reach Γ a b ↔ a = b := by
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail h e ih => exact (hn _ _ e).elim
    · rintro rfl
      exact .refl
  refine ⟨?_,?_,hr [] ?_,hr [[]] ?_⟩ <;> simp [Edge, edges]

theorem unit_graph (p : α) (a b : PropLiteral α) :
    Edge [[⟨p,true⟩]] a b ↔ a = ⟨p,false⟩ ∧ b = ⟨p,true⟩ := by
  simp [Edge, edges, opposite]

theorem unit_reach (p : α) (a b : PropLiteral α) :
    Reach [[⟨p,true⟩]] a b ↔ a = b ∨ (a = ⟨p,false⟩ ∧ b = ⟨p,true⟩) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail h e ih =>
      obtain ⟨hc,hb⟩ := (unit_graph p _ _).mp e
      rcases ih with h | h
      · exact Or.inr ⟨h.trans hc,hb⟩
      · exact Or.inr ⟨h.1,hb⟩
  · rintro (h | ⟨ha,hb⟩)
    · subst b
      exact .refl
    · exact .single ((unit_graph p a b).mpr ⟨ha,hb⟩)

theorem unit_model (p : α) :
    Models (fun _ => true) [[⟨p,true⟩]] ∧
    Reach [[⟨p,true⟩]] ⟨p,false⟩ ⟨p,true⟩ ∧
    ¬ Reach [[⟨p,true⟩]] ⟨p,true⟩ ⟨p,false⟩ := by
  refine ⟨?_,?_,?_⟩
  · simp [Models, MathematicalLogic.TseitinEncoding.ListModels]
  · exact (unit_reach p _ _).mpr (Or.inr ⟨rfl,rfl⟩)
  · simp [unit_reach, PropLiteral.mk.injEq]

theorem opposite_units (p : α) :
    Mutual [[⟨p,true⟩],[⟨p,false⟩]] ⟨p,true⟩ ⟨p,false⟩ ∧
    ¬ Sat [[⟨p,true⟩],[⟨p,false⟩]] := by
  let Γ : Cnf α := [[⟨p,true⟩],[⟨p,false⟩]]
  have hm : Mutual Γ ⟨p,true⟩ ⟨p,false⟩ := by
    constructor
    · exact .single ((edge_spec Γ _ _).mpr
        (Or.inl ⟨⟨p,false⟩,by simp [Γ],rfl,rfl⟩))
    · exact .single ((edge_spec Γ _ _).mpr
        (Or.inl ⟨⟨p,true⟩,by simp [Γ],rfl,rfl⟩))
  exact ⟨hm,contradictory_component Γ ⟨p,true⟩ hm⟩

def earlierAssignment (Γ : Cnf α) (r : Component Γ → ℕ) : Valuation α :=
  fun p => decide (r (componentOf Γ ⟨p,true⟩) < r (componentOf Γ ⟨p,false⟩))

theorem earlier_fails_unit (p : α) (r : Component [[⟨p,true⟩]] → ℕ)
    (hr : IsRank [[⟨p,true⟩]] r) :
    ¬ Models (earlierAssignment [[⟨p,true⟩]] r) [[⟨p,true⟩]] := by
  have hle := hr.2 ((component_le [[⟨p,true⟩]] ⟨p,false⟩ ⟨p,true⟩).mpr (unit_model p).2.1)
  intro hv
  have hp := MathematicalLogic.DpllSatisfiability.unit_forced (p := p) (b := true) (by simp) _ hv
  change decide (r (componentOf [[⟨p,true⟩]] ⟨p,true⟩) <
    r (componentOf [[⟨p,true⟩]] ⟨p,false⟩)) = true at hp
  exact not_lt_of_ge hle (of_decide_eq_true hp)

end Lemmatheca.Entry.TwoSatisfiability
