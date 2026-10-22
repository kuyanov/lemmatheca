import Lemmatheca.IsolatedTypes.IsolatedTypes
import Lemmatheca.TypesAndRealization.Examples

namespace Lemmatheca.Entry.IsolatedTypes

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types
open Lemmatheca.ModelTheory.IsolatedTypes
open Lemmatheca.ModelTheory.ArithmeticTheories
open Lemmatheca.Entry.TypesAndRealization

/-- No complete extension of all numeral exclusions is isolated over true arithmetic. -/
theorem nonstandard_extensions_nonisolated (p : trueArithmetic.CompleteType (Fin 1))
    (hp : nonstandardConditions ⊆ formulas p) : ¬ Isolated trueArithmetic p := by
  intro hi
  obtain ⟨a, ha⟩ := isolated_realized (M := ℕ)
    (completeTheory.isComplete language ℕ) p hi
  exact nonstandard_omitted ⟨a, fun φ hφ => ha φ (hp hφ)⟩

end Lemmatheca.Entry.IsolatedTypes
