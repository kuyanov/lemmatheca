import Lemmatheca.TseitinEncoding.TseitinEncoding

namespace Lemmatheca.Entry.TseitinEncoding
open MathematicalLogic.Propositional MathematicalLogic.TseitinEncoding

def sample : PropFormula (Fin 3) := .disj (.atom 0) (.conj (.atom 1) (.atom 2))
def sampleValuation : Valuation (Fin 3) := fun i => decide (i ≠ 0)

theorem sample_encoding :
    treeSize sample = 5 ∧ (encoding sample).length = 13 ∧
    literalCount (encoding sample) = 27 ∧
    extend sampleValuation (fresh (.atom 0)) = false ∧
    extend sampleValuation (fresh (.atom 1)) = true ∧
    extend sampleValuation (fresh (.atom 2)) = true ∧
    extend sampleValuation (fresh (.conj (.atom 1) (.atom 2))) = true ∧
    extend sampleValuation (fresh sample) = true ∧
    ListModels (extend sampleValuation) (encoding sample) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact (encoding_extend sampleValuation sample).mpr rfl

theorem falsum_encoding :
    definitions (.falsum : PropFormula Unit) = [[neg (fresh .falsum)]] ∧
    encoding (.falsum : PropFormula Unit) =
      [[pos (fresh .falsum)], [neg (fresh .falsum)]] ∧
    ¬ ∃ w, ListModels w (encoding (.falsum : PropFormula Unit)) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [equisatisfiable]
  simp [eval]

def badValuation : Valuation (ExpandedAtom Unit)
  | .inl _ => true
  | .inr _ => false

theorem not_equivalent :
    eval (restrict badValuation) (.atom ()) = true ∧
    ¬ ListModels badValuation (encoding (.atom ())) := by
  simp [eval, restrict, old, badValuation, ListModels, encoding, pos, fresh]

end Lemmatheca.Entry.TseitinEncoding
