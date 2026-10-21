import Lemmatheca.ArithmeticRepresentability.ArithmeticBoundedFormulas
import Lemmatheca.PaComputations.PAComputations

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Eliminate literal strict bounded quantifiers by an explicit inclusive
bound and endpoint inequality. The equivalence is internal to PA. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

theorem strict_iff_le_ne {M : Type*} [language.Structure M] [M ⊨ PA] (a b : M) :
    leValue M (succValue M a) b ↔ leValue M a b ∧ a ≠ b := by
  rw [successor_le_iff_lt]
  constructor
  · rintro ⟨hle, hnot⟩
    exact ⟨hle, fun he => hnot (he ▸ le_refl_value a)⟩
  · rintro ⟨hle, hne⟩
    exact ⟨hle, fun hrev => hne (le_antisymm_value hle hrev)⟩

def endpointDifferent {α : Type} (t : language.Term α) :
    language.Formula (α ⊕ Unit) :=
  ((Term.var (.inr ())).equal (t.relabel Sum.inl)).not

theorem endpointDifferent_deltaZero {α : Type} (t : language.Term α) :
    DeltaZero (endpointDifferent t) := .imp (.equal _ _) .falsum

def ModelEquivalent {α : Type} (φ ψ : language.Formula α) : Prop :=
  ∀ (M : Type) [language.Structure M] [M ⊨ PA] (v : α → M), φ.Realize v ↔ ψ.Realize v

theorem boundedArithmetic_core {α : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) :
    ∃ ψ : language.Formula α, DeltaZero ψ ∧ ModelEquivalent φ ψ := by
  induction hφ with
  | core h => exact ⟨_, h, fun _ _ _ _ => Iff.rfl⟩
  | imp hφ hχ ihφ ihχ =>
    obtain ⟨ψ, hψ, h₁⟩ := ihφ
    obtain ⟨ξ, hξ, h₂⟩ := ihχ
    refine ⟨ψ.imp ξ, .imp hψ hξ, ?_⟩
    intro M _ _ v
    simp only [Formula.realize_imp, h₁ M v, h₂ M v]
  | all t hφ ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    refine ⟨boundedAll t ψ, .all t hψ, ?_⟩
    intro M _ _ v
    simp only [realize_boundedAll, h M]
  | ex t hφ ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    refine ⟨boundedEx t ψ, .ex t hψ, ?_⟩
    intro M _ _ v
    simp only [realize_boundedEx, h M]
  | strictAll t hφ ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    refine ⟨boundedAll t ((endpointDifferent t).imp ψ),
      .all t (.imp (endpointDifferent_deltaZero t) hψ), ?_⟩
    intro M _ _ v
    simp only [realize_strictAll, realize_boundedAll, Formula.realize_imp,
      endpointDifferent, Formula.realize_not, Formula.realize_equal,
      Term.realize_var, Term.realize_relabel, Function.comp_def,
      h M, strict_iff_le_ne]
    constructor
    · intro hh a ha hne
      exact hh a ⟨ha, hne⟩
    · intro hh a ha
      exact hh a ha.1 ha.2
  | strictEx t hφ ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    have hb : DeltaZero ((endpointDifferent t) ⊓ ψ) :=
      .imp (.imp (endpointDifferent_deltaZero t) (.imp hψ .falsum)) .falsum
    refine ⟨boundedEx t ((endpointDifferent t) ⊓ ψ), .ex t hb, ?_⟩
    intro M _ _ v
    simp only [realize_strictEx, realize_boundedEx, Formula.realize_inf,
      endpointDifferent, Formula.realize_not, Formula.realize_equal,
      Term.realize_var, Term.realize_relabel, Function.comp_def,
      h M, strict_iff_le_ne]
    exact exists_congr fun _ => and_assoc

theorem coreSigmaOne_bounded {α : Type} {A : language.Formula α} (hA : SigmaOne A) :
    BoundedSigmaOne A := by
  obtain ⟨k, D, hD, rfl⟩ := hA
  exact ⟨k, D, .core hD, rfl⟩

end
end Lemmatheca.ProofTheory.PAComputations
namespace Lemmatheca.ProofTheory.ArithmeticRepresentability.BoundedArithmetic
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs PAComputations
noncomputable section

def normalForm {α : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) : language.Formula α :=
  Classical.choose (boundedArithmetic_core hφ)

theorem normalForm_deltaZero {α : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) : DeltaZero hφ.normalForm :=
  (Classical.choose_spec (boundedArithmetic_core hφ)).1

theorem normalForm_realize {α : Type} {φ : language.Formula α}
    (hφ : BoundedArithmetic φ) : ModelEquivalent φ hφ.normalForm :=
  (Classical.choose_spec (boundedArithmetic_core hφ)).2

theorem normalForm_equivalence {r : ℕ} {φ : language.Formula (Fin r)}
    (hφ : BoundedArithmetic φ) : Derives PA (close (φ.iff hφ.normalForm)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro v
  exact Formula.realize_iff.mpr (hφ.normalForm_realize M v)

end
end Lemmatheca.ProofTheory.ArithmeticRepresentability.BoundedArithmetic

namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

theorem boundedSigmaOne_normalize {α : Type} [Fintype α] {A : language.Formula α}
    (hA : BoundedSigmaOne A) : SigmaOneEquivalent A := by
  obtain ⟨k, D, hD, rfl⟩ := hA
  refine ⟨⟨k, hD.normalForm, hD.normalForm_deltaZero⟩, ?_⟩
  change Derives PA (allClose ((D.iExs (Fin k)).iff
    (hD.normalForm.iExs (Fin k))))
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_allClose]
  intro v
  rw [Formula.realize_iff, Formula.realize_iExs, Formula.realize_iExs]
  exact exists_congr fun y => hD.normalForm_realize M (Sum.elim v y)

end
end Lemmatheca.ProofTheory.PAComputations
