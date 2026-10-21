import Lemmatheca.InfinitaryLogic.Syntax

/-! Separate witnesses for countably many predicates need not be one common witness. -/
namespace Lemmatheca.Entry.InfinitaryLogic

open FirstOrder
open Lemmatheca.MathematicalLogic.InfinitaryLogic

inductive PredicateSymbol : ℕ → Type
  | pred (i : ℕ) : PredicateSymbol 1

def predicateLanguage : Language := ⟨fun _ => Empty, PredicateSymbol⟩

def predicateBody (i : ℕ) : Formula predicateLanguage Empty 1 :=
  .rel (.pred i) (fun _ => .var (.inr 0))

def separateWitnesses : Sentence predicateLanguage :=
  .conj fun i => (predicateBody i).ex

def commonWitness : Sentence predicateLanguage :=
  (Formula.conj predicateBody).ex

instance singletonPredicateStructure : predicateLanguage.Structure ℕ where
  funMap f := Empty.elim f
  RelMap r a := match r with
    | .pred i => a 0 = i

theorem witnesses_differ :
    Sentence.Realize separateWitnesses ℕ ∧ ¬ Sentence.Realize commonWitness ℕ := by
  constructor
  · intro i
    apply (realize_ex (predicateBody i) Empty.elim Fin.elim0).mpr
    exact ⟨i, rfl⟩
  · intro h
    obtain ⟨x, hx⟩ := (realize_ex (Formula.conj predicateBody) Empty.elim Fin.elim0).mp h
    have h0 := hx 0
    have h1 := hx 1
    change x = 0 at h0
    change x = 1 at h1
    omega

theorem common_implies_separate {M : Type*} [predicateLanguage.Structure M] :
    Sentence.Realize commonWitness M → Sentence.Realize separateWitnesses M := by
  intro h
  obtain ⟨x, hx⟩ := (realize_ex (Formula.conj predicateBody) Empty.elim Fin.elim0).mp h
  intro i
  exact (realize_ex (predicateBody i) Empty.elim Fin.elim0).mpr ⟨x, hx i⟩

end Lemmatheca.Entry.InfinitaryLogic
