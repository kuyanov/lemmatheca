import Lemmatheca.PropositionalLogic.Propositional

/-! Signed negation-normal syntax and its explicit shared-language translations. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional

open Lemmatheca.MathematicalLogic.Propositional

universe u

/-- One-sided propositional syntax with negation only in the signed atoms. -/
inductive Nnf (α : Type u) : Type u
  | pos : α → Nnf α
  | neg : α → Nnf α
  | bot : Nnf α
  | top : Nnf α
  | and : Nnf α → Nnf α → Nnf α
  | or : Nnf α → Nnf α → Nnf α
  deriving DecidableEq

namespace Nnf

variable {α : Type u}

/-- Syntactic Boolean dual, without introducing a negation constructor. -/
def dual : Nnf α → Nnf α
  | .pos p => .neg p
  | .neg p => .pos p
  | .bot => .top
  | .top => .bot
  | .and A B => .or (dual A) (dual B)
  | .or A B => .and (dual A) (dual B)

/-- Boolean evaluation of the signed language. -/
def eval (v : α → Bool) : Nnf α → Bool
  | .pos p => v p
  | .neg p => !(v p)
  | .bot => false
  | .top => true
  | .and A B => eval v A && eval v B
  | .or A B => eval v A || eval v B

/-- The ordinary propositional formula read from a signed expression. -/
def read : Nnf α → PropFormula α
  | .pos p => .atom p
  | .neg p => .neg (.atom p)
  | .bot => .falsum
  | .top => verum
  | .and A B => .conj (read A) (read B)
  | .or A B => .disj (read A) (read B)

/-- All underlying atom names occurring in a signed expression. -/
def atoms [DecidableEq α] : Nnf α → Finset α
  | .pos p | .neg p => {p}
  | .bot | .top => ∅
  | .and A B | .or A B => atoms A ∪ atoms B

/-- Simultaneous positive/negative normalization of the actual shared syntax. -/
def normalize : PropFormula α → Bool → Nnf α
  | .atom p, true => .pos p
  | .atom p, false => .neg p
  | .falsum, true => .bot
  | .falsum, false => .top
  | .neg A, b => normalize A (!b)
  | .conj A B, true => .and (normalize A true) (normalize B true)
  | .conj A B, false => .or (normalize A false) (normalize B false)
  | .disj A B, true => .or (normalize A true) (normalize B true)
  | .disj A B, false => .and (normalize A false) (normalize B false)
  | .impl A B, true => .or (normalize A false) (normalize B true)
  | .impl A B, false => .and (normalize A true) (normalize B false)

abbrev positive (A : PropFormula α) : Nnf α := normalize A true
abbrev negative (A : PropFormula α) : Nnf α := normalize A false

end Nnf

variable {α : Type u} [DecidableEq α]

/-- A sequent is a finite set of signed formulas, read disjunctively. -/
abbrev Sequent (α : Type u) := Finset (Nnf α)

/-- At least one of the sequent's alternatives is true under the valuation. -/
def SatisfiesSequent (v : α → Bool) (Γ : Sequent α) : Prop :=
  ∃ A ∈ Γ, Nnf.eval v A = true

/-- Every valuation satisfies the sequent. -/
def Valid (Γ : Sequent α) : Prop := ∀ v, SatisfiesSequent v Γ

/-- Negated hypotheses and positive conclusions, as one actual finite set. -/
def encode (Λ Δ : Finset (PropFormula α)) : Sequent α :=
  Λ.image Nnf.negative ∪ Δ.image Nnf.positive

end Lemmatheca.ProofTheory.ClassicalPropositional
