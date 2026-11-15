import Lemmatheca.IntuitionisticPropositionalCutElimination.Translations

/-! G4ip on finite contexts in the shared native syntax. The intended inputs are
negation-free; public native inputs are explicitly expanded. Each left constructor
erases its selected principal. There is no cut, weakening or general implication-left
constructor. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.G4ip

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

abbrev Context (α : Type u) := Finset (PropFormula α)
abbrev Goal (α : Type u) := Context α × PropFormula α

def ReducedContext (Γ : Context α) : Prop := ∀ A ∈ Γ, NegationFree A

def remainder (Γ : Context α) (F : PropFormula α) : Context α := Γ.erase F

/-- Actual primitive-rule trees. Restricting the indices to reduced goals gives the
entry's G4ip certificates; native negation is handled by explicit expansion. -/
inductive Proof : Context α → PropFormula α → Type u
  | atom {Γ a} : atom a ∈ Γ → Proof Γ (atom a)
  | falsumLeft {Γ E} : falsum ∈ Γ → Proof Γ E
  | conjRight {Γ A B} : Proof Γ A → Proof Γ B → Proof Γ (conj A B)
  | disjRightLeft {Γ A B} : Proof Γ A → Proof Γ (disj A B)
  | disjRightRight {Γ A B} : Proof Γ B → Proof Γ (disj A B)
  | implRight {Γ A B} : Proof (insert A Γ) B → Proof Γ (impl A B)
  | conjLeft {Γ A B E} : conj A B ∈ Γ →
      Proof (insert A (insert B (remainder Γ (conj A B)))) E → Proof Γ E
  | disjLeft {Γ A B E} : disj A B ∈ Γ →
      Proof (insert A (remainder Γ (disj A B))) E →
      Proof (insert B (remainder Γ (disj A B))) E → Proof Γ E
  | atomImplLeft {Γ a B E} : impl (atom a) B ∈ Γ → atom a ∈ Γ →
      Proof (insert B (remainder Γ (impl (atom a) B))) E → Proof Γ E
  | botImplLeft {Γ B E} : impl falsum B ∈ Γ →
      Proof (remainder Γ (impl falsum B)) E → Proof Γ E
  | conjImplLeft {Γ A B C E} : impl (conj A B) C ∈ Γ →
      Proof (insert (impl A (impl B C)) (remainder Γ (impl (conj A B) C))) E →
      Proof Γ E
  | disjImplLeft {Γ A B C E} : impl (disj A B) C ∈ Γ →
      Proof (insert (impl A C) (insert (impl B C) (remainder Γ (impl (disj A B) C)))) E →
      Proof Γ E
  | implImplLeft {Γ A B C E} : impl (impl A B) C ∈ Γ →
      Proof (insert (impl B C) (remainder Γ (impl (impl A B) C))) (impl A B) →
      Proof (insert C (remainder Γ (impl (impl A B) C))) E → Proof Γ E

/-- One immediate backward premise, exactly for a primitive constructor above. -/
inductive Backward : Goal α → Goal α → Prop
  | conjRightLeft (Γ : Context α) (A B) : Backward (Γ, A) (Γ, conj A B)
  | conjRightRight (Γ : Context α) (A B) : Backward (Γ, B) (Γ, conj A B)
  | disjRightLeft (Γ : Context α) (A B) : Backward (Γ, A) (Γ, disj A B)
  | disjRightRight (Γ : Context α) (A B) : Backward (Γ, B) (Γ, disj A B)
  | implRight (Γ : Context α) (A B) : Backward (insert A Γ, B) (Γ, impl A B)
  | conjLeft {Γ A B E} (h : conj A B ∈ Γ) :
      Backward (insert A (insert B (remainder Γ (conj A B))), E) (Γ, E)
  | disjLeftLeft {Γ A B E} (h : disj A B ∈ Γ) :
      Backward (insert A (remainder Γ (disj A B)), E) (Γ, E)
  | disjLeftRight {Γ A B E} (h : disj A B ∈ Γ) :
      Backward (insert B (remainder Γ (disj A B)), E) (Γ, E)
  | atomImplLeft {Γ a B E} (h : impl (atom a) B ∈ Γ) (ha : atom a ∈ Γ) :
      Backward (insert B (remainder Γ (impl (atom a) B)), E) (Γ, E)
  | botImplLeft {Γ B E} (h : impl falsum B ∈ Γ) :
      Backward (remainder Γ (impl falsum B), E) (Γ, E)
  | conjImplLeft {Γ A B C E} (h : impl (conj A B) C ∈ Γ) :
      Backward (insert (impl A (impl B C)) (remainder Γ (impl (conj A B) C)), E) (Γ, E)
  | disjImplLeft {Γ A B C E} (h : impl (disj A B) C ∈ Γ) :
      Backward (insert (impl A C) (insert (impl B C) (remainder Γ (impl (disj A B) C))), E) (Γ, E)
  | implImplLeftFirst {Γ A B C E} (h : impl (impl A B) C ∈ Γ) :
      Backward (insert (impl B C) (remainder Γ (impl (impl A B) C)), impl A B) (Γ, E)
  | implImplLeftSecond {Γ A B C E} (h : impl (impl A B) C ∈ Γ) :
      Backward (insert C (remainder Γ (impl (impl A B) C)), E) (Γ, E)

/-- The producer premise of the old, unrestricted retained-principal rule. -/
def RetainedProducer (child parent : Goal α) : Prop :=
  ∃ A B, impl A B ∈ parent.1 ∧ child = (parent.1, A)

end Lemmatheca.ProofTheory.Intuitionistic.G4ip
