import Lemmatheca.ClassicalFirstOrderDeductionTranslations.Public
import Lemmatheca.IntuitionisticFirstOrderDeduction.Examples

namespace Lemmatheca.Entry.ClassicalFirstOrderDeductionTranslations
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
universe u v w

/-- The round-trip preserves classical proofs, not full constructor identity. -/
theorem expanded_conjunction_ne (L : Language.{u,v}) (α : Type w) (n : ℕ) :
    expanded (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.conj .falsum .falsum : BF L α n) ≠ Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.conj .falsum .falsum := by
  intro h
  cases h

/-- The actual existing small public relation has the constant-free existence theorem. -/
theorem constantFree_public_small : Lemmatheca.MathematicalLogic.FirstOrderProofs.Proof Language.empty ∅
    Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula.toClassical := by
  simpa only [expandContext, Finset.image_empty] using
    public_toSmall Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeExistence

/-- A raw old proof over no parameters would contradict the raw full obstruction. -/
theorem constantFree_raw_small_impossible :
    ¬ Lemmatheca.MathematicalLogic.FirstOrderProofs.CoreProof Language.empty ∅
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula.toClassical := by
  intro h
  rcases raw_ofSmall h with ⟨p⟩
  have q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true true
      Language.empty ∅
      (expanded Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula) := by
    simpa only [includeContext, Finset.image_empty, expanded] using p
  exact Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeRawImpossible true true
    ⟨Raw.fromExpanded _ q⟩

end Lemmatheca.Entry.ClassicalFirstOrderDeductionTranslations
