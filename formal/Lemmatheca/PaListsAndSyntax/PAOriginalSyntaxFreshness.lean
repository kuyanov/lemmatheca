import Lemmatheca.PaListsAndSyntax.PANativeNoAux
import Lemmatheca.PaListsAndSyntax.PAFixedFormulaCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Original-language formula bounds rule out every auxiliary-name occurrence. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedSyntaxPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem noAux_of_formulaBound {k : ℕ} {e : M} (he : FormulaBound k e) (j : M) :
    occursAux.value ![j, e] = zeroValue M := by
  obtain ⟨d, hd, _, hs⟩ := he
  have hne : d ≠ zeroValue M := by
    intro hz
    rw [hz, numeral_value_succ, numeral_value_zero] at hd
    exact ((successor_le_iff_lt _ _).mp hd).2 (le_refl_value _)
  apply (recognized_noAux j e).2
  · simpa only [formDepth, hs, modelSummary_part_value, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hne
  · simp only [statsPart, hs, modelSummary_part_value, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.BoundedSyntaxPrograms
