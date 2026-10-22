import Lemmatheca.AtomicAndPrimeModels.AtomicModels
import Lemmatheca.IsolatedTypes.Patterns
import Lemmatheca.BackAndForth.BackAndForthStrictTheory
import Mathlib.Analysis.Real.Cardinality

/-! Atomicity does not imply primeness for uncountable dense orders. -/
namespace Lemmatheca.Entry.AtomicAndPrimeModels

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.AtomicAndPrimeModels
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.QuantifierElimination

/-- Every finite tuple type in a nonempty dense order is isolated. -/
theorem dlo_atomic (M : Type) [binaryRelLanguage.Structure M]
    [Nonempty M] [M ⊨ Shared.strictDloTheory] :
    IsAtomic Shared.strictDloTheory M := by
  intro n a
  let := Lemmatheca.ModelTheory.IsolatedTypes.finite_dloTypes n
  exact Lemmatheca.ModelTheory.IsolatedTypes.isolated_of_finite (Shared.strictDloTheory.typeOf a)

/-- The actual rational strict-order structure is prime. -/
theorem rational_order_prime :
    letI : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (fun a b => a < b)
    IsPrime Shared.strictDloTheory ℚ := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (fun a b => a < b)
  let : ℚ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
  exact countable_atomic_prime Lemmatheca.ModelTheory.BackAndForth.strictDlo_complete (dlo_atomic ℚ)

/-- The actual real strict order is atomic but cannot be prime. -/
theorem real_order_atomic_not_prime :
    letI : binaryRelLanguage.Structure ℝ := binaryRelStructure ℝ (fun a b => a < b)
    letI : ℝ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
    IsAtomic Shared.strictDloTheory ℝ ∧ ¬IsPrime Shared.strictDloTheory ℝ := by
  let : binaryRelLanguage.Structure ℝ := binaryRelStructure ℝ (fun a b => a < b)
  let : ℝ ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
  refine ⟨dlo_atomic ℝ, fun h => ?_⟩
  have hc := prime_countable Lemmatheca.ModelTheory.BackAndForth.strictDlo_complete h
  exact not_countable (α := ℝ) hc

end Lemmatheca.Entry.AtomicAndPrimeModels
