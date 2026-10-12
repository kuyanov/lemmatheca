import Lemmatheca.MathematicalLogic.FirstOrderProofs
import Mathlib.ModelTheory.Encoding

/-! The fixed auxiliary-constant syntax for the Henkin construction. -/
namespace Lemmatheca.MathematicalLogic.HenkinCompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u, v}} {α : Type w} {n : ℕ}
noncomputable section
local instance : DecidableEq (L.Formula α) := Classical.decEq _

/-- Countability includes finite signatures, with symbol arities recorded. -/
def CountableLanguage (L : Language.{u, v}) : Prop := Countable L.Symbols
/-- The language and free-name type stay fixed while every sentence is decided. -/
def Complete (S : Set (L.Formula α)) : Prop := ∀ A, A ∈ S ∨ A.not ∈ S
/-- Regard original sentences as formulas with auxiliary constant names. -/
def liftTheory (T : L.Theory) : Set (L.Formula ℕ) := Formula.relabel Empty.elim '' T
/-- The usual conditional witness axiom, with an auxiliary constant name. -/
def witnessAxiom (φ : L.BoundedFormula ℕ 1) (c : ℕ) : L.Formula ℕ :=
  φ.ex.imp (instantiate φ (.var c))
/-- A conditional constant witness exists for every quantified body. -/
def Henkin (S : Set (L.Formula ℕ)) : Prop :=
  ∀ φ : L.BoundedFormula ℕ 1, ∃ c : ℕ, witnessAxiom φ c ∈ S
/-- The parameter is absent from every allowed open assumption. -/
def FreshFor (c : ℕ) (T : Set (L.Formula ℕ)) : Prop := ∀ A ∈ T, c ∉ A.freeVarFinset
/-- Fill scoped slots with term representatives; free names remain constants. -/
def closeSlots (φ : L.BoundedFormula ℕ n) (ts : Fin n → L.Term ℕ) : L.Formula ℕ :=
  φ.toFormula.subst (Sum.elim Term.var ts)
/-- Expanded closed terms are equivalent when their equality belongs to the theory. -/
def TermEquivalent (S : Set (L.Formula ℕ)) (t u : L.Term ℕ) : Prop := t.equal u ∈ S
/-- Unquotiented functions build terms and relations consult the completed theory. -/
@[instance_reducible]
def termStructure (S : Set (L.Formula ℕ)) : L.Structure (L.Term ℕ) where
  funMap f ts := .func f ts
  RelMap r ts := r.formula ts ∈ S


end
end Lemmatheca.MathematicalLogic.HenkinCompleteness
