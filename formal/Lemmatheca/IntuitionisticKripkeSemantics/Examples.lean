import Lemmatheca.IntuitionisticKripkeSemantics.Constructions
import Mathlib.Data.Bool.Basic

namespace Lemmatheca.Entry.IntuitionisticKripkeSemantics

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic.Kripke

universe u
variable {α : Type u}

/-- The lower Boolean world forces no atom; the upper world forces only the named atom. -/
def chainModel (p : α) : Model α Bool where
  world_nonempty := ⟨false⟩
  valuation w a := w = true ∧ a = p
  persistent {w z} h a ha := by
    rcases ha with ⟨hw, ha⟩
    subst w
    cases z
    · exact ((by decide : ¬ ((true : Bool) ≤ false)) h).elim
    · exact ⟨rfl, ha⟩

/-- All three values of the atom and its two successive negations at the lower world. -/
theorem chain_values (p : α) :
    ¬ Forces (chainModel p) false (atom p) ∧
      ¬ Forces (chainModel p) false (neg (atom p)) ∧
      Forces (chainModel p) false (neg (neg (atom p))) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Forces, chainModel]
  · intro h
    exact h true (by decide) ⟨rfl, rfl⟩
  · intro z _ hn
    exact hn true (by cases z <;> decide) ⟨rfl, rfl⟩

theorem chain_not_excluded_middle (p : α) :
    ¬ Forces (chainModel p) false (disj (atom p) (neg (atom p))) := by
  rintro (h | h)
  · exact (chain_values p).1 h
  · exact (chain_values p).2.1 h

theorem chain_not_dne (p : α) :
    ¬ Forces (chainModel p) false (impl (neg (neg (atom p))) (atom p)) := by
  intro h
  exact (chain_values p).1 (h false le_rfl (chain_values p).2.2)

/-- A root and two incomparable terminal worlds. -/
inductive ForkWorld
  | root | left | right
  deriving DecidableEq

/-- Reachability in the actual three-element fork. -/
def forkLe (w z : ForkWorld) : Prop := w = .root ∨ w = z

instance forkPreorder : Preorder ForkWorld where
  le := forkLe
  le_refl _ := Or.inr rfl
  le_trans _ _ _ h₁ h₂ := by
    rcases h₁ with h | h
    · exact Or.inl h
    · subst_vars
      exact h₂

/-- The two leaves force exactly the separate named atoms, and the root forces none. -/
def forkModel (p q : α) : Model α ForkWorld where
  world_nonempty := ⟨.root⟩
  valuation
    | .root, _ => False
    | .left, a => a = p
    | .right, a => a = q
  persistent {w z} h a ha := by
    rcases h with h | h
    · subst w
      exact ha.elim
    · subst z
      exact ha

/-- The root satisfies the negated conjunction and neither disjunctive negation. -/
theorem fork_values (p q : α) (hpq : p ≠ q) :
    Forces (forkModel p q) .root (neg (conj (atom p) (atom q))) ∧
      ¬ Forces (forkModel p q) .root (disj (neg (atom p)) (neg (atom q))) := by
  constructor
  · intro z _ h
    cases z with
    | root => exact h.1
    | left => exact hpq h.2.symm
    | right => exact hpq h.1
  · rintro (h | h)
    · exact h .left (Or.inl rfl) rfl
    · exact h .right (Or.inl rfl) rfl

theorem fork_not_demorgan (p q : α) (hpq : p ≠ q) :
    ¬ Forces (forkModel p q) .root
      (impl (neg (conj (atom p) (atom q))) (disj (neg (atom p)) (neg (atom q)))) := by
  intro h
  exact (fork_values p q hpq).2 (h .root le_rfl (fork_values p q hpq).1)

theorem not_derives_excluded_middle (p : α) :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (disj (atom p) (neg (atom p))) := by
  apply countermodel_not_derivable (chainModel p) false
  exact ⟨by simp [ForcesContext], chain_not_excluded_middle p⟩

theorem not_derives_dne (p : α) :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (impl (neg (neg (atom p))) (atom p)) := by
  apply countermodel_not_derivable (chainModel p) false
  exact ⟨by simp [ForcesContext], chain_not_dne p⟩

theorem not_derives_demorgan (p q : α) (hpq : p ≠ q) :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (impl (neg (conj (atom p) (atom q))) (disj (neg (atom p)) (neg (atom q)))) := by
  apply countermodel_not_derivable (forkModel p q) .root
  exact ⟨by simp [ForcesContext], fork_not_demorgan p q hpq⟩

theorem demorgan_boolean (p q : α) :
    Tautology
      (impl (neg (conj (atom p) (atom q))) (disj (neg (atom p)) (neg (atom q)))) := by
  intro b
  cases hp : b p <;> cases hq : b q <;> simp [Satisfies, eval, hp, hq]

theorem chain_local_implication (p q : α) (hpq : p ≠ q) :
    ¬ Forces (chainModel p) false (atom p) ∧
      ¬ Forces (chainModel p) false (atom q) ∧
      ¬ Forces (chainModel p) false (impl (atom p) (atom q)) := by
  refine ⟨(chain_values p).1, ?_, ?_⟩
  · simp [Forces, chainModel]
  · intro h
    exact hpq (h true (by decide) ⟨rfl, rfl⟩).2.symm

end Lemmatheca.Entry.IntuitionisticKripkeSemantics
