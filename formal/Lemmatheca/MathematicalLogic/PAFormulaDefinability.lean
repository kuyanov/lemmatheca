import Lemmatheca.MathematicalLogic.PAInternalDefinability
import Lemmatheca.MathematicalLogic.PAInduction
import Lemmatheca.MathematicalLogic.ArithmeticRepresentabilityRecursion

/-! Arithmetic formulas evaluated at definable coordinate functions give
definable induction invariants, including finite-history comparisons. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u
variable {M : Type u} [language.Structure M] {α β : Type} [Finite β]

theorem dp_formula (φ : language.Formula β) (f : (α → M) → β → M)
    (hf : ∀ i, Set.univ.DefinableFun language (fun v => f v i)) :
    DPred (fun v => φ.Realize (f v)) := by
  have h : (Set.univ : Set M).Definable language {v : β → M | φ.Realize v} :=
    (Set.empty_definable_iff.mpr ⟨φ, rfl⟩).mono (Set.empty_subset _)
  exact h.preimage_map hf

theorem dp_decode (c d i z : (α → M) → M)
    (hc : Set.univ.DefinableFun language c) (hd : Set.univ.DefinableFun language d)
    (hi : Set.univ.DefinableFun language i) (hz : Set.univ.DefinableFun language z) :
    DPred (fun v => decodeRealizes betaGraph (c v) (d v) (i v) (z v)) := by
  apply dp_formula betaGraph (fun v => extend ![c v, d v, i v] (z v))
  intro j
  cases j with
  | inl j => fin_cases j; exact hc; exact hd; exact hi
  | inr j => exact hz

end
end Lemmatheca.MathematicalLogic.PAComputations
