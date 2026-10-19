import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityBasic

namespace Lemmatheca.Entry.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section

/-- A direct representing graph for squaring. -/
def squareGraph : language.Formula (Fin 1 ⊕ Unit) :=
  (Term.var (.inr ())).equal
    (mulTerm (.var (.inl 0)) (.var (.inl 0)))

theorem squareGraph_represents :
    StronglyRepresents (fun x : Fin 1 → ℕ => (x 0) ^ 2) squareGraph := by
  apply stronglyRepresents_of_modelwise
  intro M x y
  simp only [squareGraph, Formula.realize_equal, realize_mulTerm,
    Term.realize_var, extend, Sum.elim_inl, Sum.elim_inr, numeral_mul, pow_two]

end
end Lemmatheca.Entry.ArithmeticRepresentability
