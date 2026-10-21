import Lemmatheca.HornClauses.HornClauses

namespace Lemmatheca.Entry.HornClauses

open Lemmatheca.MathematicalLogic.HornClauses

inductive Atom | p | q | r | s deriving DecidableEq
open Atom

def traceTheory : Finset (Rule Atom) :=
  {⟨∅, some p⟩, ⟨{p}, some q⟩, ⟨{p,q}, some r⟩,
   ⟨{r}, some q⟩, ⟨{r,s}, none⟩}

def cycleTheory : Finset (Rule Atom) := {⟨{p}, some q⟩, ⟨{q}, some p⟩}

def seededCycle : Finset (Rule Atom) := insert ⟨∅, some p⟩ cycleTheory

def inconsistentCycle : Finset (Rule Atom) := insert ⟨{q}, none⟩ seededCycle

theorem trace_stages :
    support traceTheory = {p,q,r,s} ∧
    stage traceTheory 0 = ∅ ∧ stage traceTheory 1 = {p} ∧
    stage traceTheory 2 = {p,q} ∧ stage traceTheory 3 = {p,q,r} ∧
    stage traceTheory 4 = {p,q,r} ∧ closure traceTheory = {p,q,r} := by decide

theorem trace_models_and_consequences :
    models traceTheory (↑({p,q,r} : Finset Atom)) ∧
    (∀ X : Set Atom, models traceTheory X → s ∉ X) ∧
    ¬(∀ X : Set Atom, models traceTheory X → s ∈ X) := by
  have hmodel : models traceTheory (↑({p,q,r} : Finset Atom)) := by
    simp [models, TheoryModels, Holds, traceTheory]
  refine ⟨hmodel, ?_, ?_⟩
  · intro X hX hs
    have hr : r ∈ X := models_least traceTheory hX r (by decide)
    have hc : (⟨{r,s}, none⟩ : Rule Atom) ∈ traceTheory := by decide
    apply hX _ hc
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hr
    · exact hs
  · intro h
    have hs := h _ hmodel
    simp at hs

theorem cycle_no_facts :
    (∀ n, stage cycleTheory n = ∅) ∧
    models cycleTheory (∅ : Set Atom) ∧
    models cycleTheory (↑({p,q} : Finset Atom)) := by
  constructor
  · intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change step cycleTheory (stage cycleTheory n) = ∅
      rw [ih]
      decide
  · constructor <;> simp [models, TheoryModels, Holds, cycleTheory]

theorem cycle_with_fact :
    stage seededCycle 0 = ∅ ∧ stage seededCycle 1 = {p} ∧
    stage seededCycle 2 = {p,q} ∧ closure seededCycle = {p,q} ∧
    models seededCycle (↑({p,q} : Finset Atom)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  simp [models, TheoryModels, Holds, seededCycle, cycleTheory]

theorem inconsistent_cycle :
    closure inconsistentCycle = {p,q} ∧
    ¬(∃ X : Set Atom, models inconsistentCycle X) ∧
    r ∉ closure inconsistentCycle ∧
    (∀ X : Set Atom, models inconsistentCycle X → r ∈ X) := by
  have hn : ¬(∃ X : Set Atom, models inconsistentCycle X) := by
    rw [satisfies_iff]
    decide
  exact ⟨by decide, hn, by decide, fun X hX => False.elim (hn ⟨X, hX⟩)⟩

end Lemmatheca.Entry.HornClauses
