import Lemmatheca.IntuitionisticPropositionalHarropDisjunction.Consequences
import Lemmatheca.IntuitionisticPropositionalDisjunctionProperty.Examples
import Lemmatheca.IntuitionisticKripkeSemantics.Examples

/-! Concrete trees and boundary witnesses used in the Harrop-context exposition. -/
namespace Lemmatheca.Entry.IntuitionisticPropositionalHarropDisjunction
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open CutFree Harrop
universe u
variable {α : Type u} [DecidableEq α]

theorem contradictory_context (a : α) :
    ContextHarrop ({.atom a, .neg (.atom a)} : Finset (PropFormula α)) ∧
      Nonempty (Proof ({.atom a, .neg (.atom a)} : Finset (PropFormula α)) .falsum) := by
  constructor
  · intro D hD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl <;> trivial
  · exact ⟨.negLeft (A := .atom a) (by simp) (.atom (by simp))⟩

def guardedImplication (p q r : α) : PropFormula α := .impl (.disj (.atom p) (.atom q)) (.atom r)
def guardedHarrop (p q r s : α) : PropFormula α :=
  .conj (guardedImplication p q r) (.neg (.atom s))
def guardedContext (p q r s : α) : Finset (PropFormula α) := {.atom p, guardedHarrop p q r s}
def guardedExpanded (p q r s : α) : Finset (PropFormula α) :=
  insert (guardedImplication p q r) (insert (.neg (.atom s)) (guardedContext p q r s))

private def guardedAntecedent (p q r s : α) :
    Proof (guardedExpanded p q r s) (.disj (.atom p) (.atom q)) :=
  .disjRightLeft (.atom (by simp [guardedExpanded, guardedContext]))

private def guardedContinuation (p q r s t : α) :
    Proof (insert (.atom r) (guardedExpanded p q r s)) (.disj (.atom r) (.atom t)) :=
  .disjRightLeft (.atom (by simp))

/-- The worked input retains the same two left principals and antecedent tree. -/
def guardedInput (p q r s t : α) :
    Proof (guardedContext p q r s) (.disj (.atom r) (.atom t)) :=
  .conjLeft (A := guardedImplication p q r) (B := .neg (.atom s))
    (by simp [guardedContext, guardedHarrop])
    (.implLeft (A := .disj (.atom p) (.atom q)) (B := .atom r)
      (by simp [guardedImplication])
      (guardedAntecedent p q r s) (guardedContinuation p q r s t))

/-- Exactly the retained left spine, with the right disjunction introduction removed. -/
def guardedFactor (p q r s : α) : Proof (guardedContext p q r s) (.atom r) :=
  .conjLeft (A := guardedImplication p q r) (B := .neg (.atom s))
    (by simp [guardedContext, guardedHarrop])
    (.implLeft (A := .disj (.atom p) (.atom q)) (B := .atom r)
      (by simp [guardedImplication])
      (guardedAntecedent p q r s) (.atom (by simp)))

theorem guarded_context_harrop (p q r s : α) : ContextHarrop (guardedContext p q r s) := by
  simp [ContextHarrop, guardedContext, guardedHarrop, guardedImplication, IsHarrop]

theorem guarded_extraction (p q r s t : α) :
    extract (guarded_context_harrop p q r s) (guardedInput p q r s t) =
      Sum.inl (guardedFactor p q r s) := by
  rfl

private def bottomIdentity : Proof (∅ : Finset (PropFormula α)) (.impl .falsum .falsum) :=
  .implRight (.falsumLeft (by simp))

/-- The output follows the supplied introduction even when both formulas coincide. -/
theorem tree_choice :
    let T : PropFormula α := .impl .falsum .falsum
    let u : Proof (∅ : Finset (PropFormula α)) T := bottomIdentity
    extract (fun _ h => by simp at h) (.disjRightLeft (B := T) u) = Sum.inl u ∧
      extract (fun _ h => by simp at h) (.disjRightRight (A := T) u) = Sum.inr u := by
  exact ⟨rfl, rfl⟩

theorem arbitrary_assumptions (p q : α) (hpq : p ≠ q) :
    let D : PropFormula α := .disj (.atom p) (.atom q)
    Nonempty (Proof {D} D) ∧ ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives {D} (.atom p) ∧
      ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives {D} (.atom q) ∧
      (eval (fun a => decide (a = q)) D = true ∧
        eval (fun a => decide (a = q)) (.atom p) = false) ∧
      (eval (fun a => decide (a = p)) D = true ∧
        eval (fun a => decide (a = p)) (.atom q) = false) := by
  dsimp
  have hvq : eval (fun a => decide (a = q)) (.disj (.atom p) (.atom q)) = true ∧
      eval (fun a => decide (a = q)) (.atom p) = false := by
    simp [eval, hpq]
  have hvp : eval (fun a => decide (a = p)) (.disj (.atom p) (.atom q)) = true ∧
      eval (fun a => decide (a = p)) (.atom q) = false := by
    simp [eval, Ne.symm hpq]
  refine ⟨⟨Proof.identity _ (by simp)⟩, ?_, ?_, hvq, hvp⟩
  · intro h
    have hf := boolean_sound h (fun a => decide (a = q)) (by
      intro D hD
      rcases hD with rfl
      exact hvq.1)
    rw [hvq.2] at hf
    cases hf
  · intro h
    have hf := boolean_sound h (fun a => decide (a = p)) (by
      intro D hD
      rcases hD with rfl
      exact hvp.1)
    rw [hvp.2] at hf
    cases hf

/-- The literal substitution from the first answered question. -/
def positiveSubstitution (n : ℕ) : PropFormula ℕ :=
  if n = 0 then .disj (.atom 1) (.atom 2) else .atom n

theorem substitution_boundary :
    IsHarrop (.atom (0 : ℕ)) ∧
      subst positiveSubstitution (.atom 0) = .disj (.atom 1) (.atom 2) ∧
      ¬ IsHarrop (subst positiveSubstitution (.atom 0)) := by
  simp [IsHarrop, subst, positiveSubstitution]

omit [DecidableEq α] in
theorem fork_choice_countermodel [DecidableEq α] (p q : α) (hpq : p ≠ q) :
    ¬ Kripke.Forces (IntuitionisticKripkeSemantics.forkModel p q)
      IntuitionisticKripkeSemantics.ForkWorld.root
      (.disj (.impl (.disj (.atom p) (.atom q)) (.atom p))
        (.impl (.disj (.atom p) (.atom q)) (.atom q))) := by
  rintro (h | h)
  · exact hpq (h .right (Or.inl rfl) (Or.inr rfl))
  · exact hpq.symm (h .left (Or.inl rfl) (Or.inl rfl))

theorem positive_substitution_counterexample :
    let P : PropFormula ℕ := .impl (.atom 0) (.disj (.atom 1) (.atom 2))
    let Q : PropFormula ℕ := .disj (.impl (.atom 0) (.atom 1)) (.impl (.atom 0) (.atom 2))
    Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (subst positiveSubstitution P) ∧
      ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (subst positiveSubstitution Q) ∧
      ¬ DisjunctionProperty.Admissible P Q := by
  dsimp
  have hp : Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (subst positiveSubstitution (.impl (.atom 0) (.disj (.atom 1) (.atom 2)))) := by
    change Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (.impl (.disj (.atom 1) (.atom 2)) (.disj (.atom 1) (.atom 2)))
    exact identity _
  have hn : ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅
      (subst positiveSubstitution
        (.disj (.impl (.atom 0) (.atom 1)) (.impl (.atom 0) (.atom 2)))) := by
    intro hd
    apply fork_choice_countermodel (1 : ℕ) 2 (by decide)
    apply Kripke.sound hd (IntuitionisticKripkeSemantics.forkModel 1 2) .root
    intro D hD
    cases hD
  refine ⟨hp, hn, ?_⟩
  intro hadmissible
  exact hn (hadmissible positiveSubstitution hp)

end Lemmatheca.Entry.IntuitionisticPropositionalHarropDisjunction
