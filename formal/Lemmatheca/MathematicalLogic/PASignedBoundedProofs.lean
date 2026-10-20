import Lemmatheca.MathematicalLogic.PASignedProofBasics
import Lemmatheca.MathematicalLogic.PANativeLogicalProofs
import Lemmatheca.MathematicalLogic.PASignedUniversalProofs
import Lemmatheca.MathematicalLogic.PASignedExistentialProofs

/-! Signed proof compilation by induction on the shared bounded-formula
derivation. Every selected program includes its correctness in all PA models. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs BoundedSyntaxPrograms BoundedTruthPrograms LogicalProofs
noncomputable section

def bottomPrograms {α : Type} {r : ℕ} (name : α → Program r) :
    SignedPrograms (⊥ : language.Formula α) name where
  positive := constant 0
  negative := bottomNegative
  positive_correct := by
    intro M _ _ x h
    exact False.elim (Formula.realize_bot.mp h)
  negative_correct := by
    intro M _ _ x _
    rw [namedFormula_bot]
    exact certified_bottomNegative axiomVerifier x

def equalityPrograms {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (s t : language.Term α) : SignedPrograms (s.equal t) name where
  positive := positiveEquality name s t
  negative := negativeEquality name s t
  positive_correct := by
    intro M _ _ x h
    rw [namedFormula_equal]
    exact certified_positiveEquality name s t x (Formula.realize_equal.mp h)
  negative_correct := by
    intro M _ _ x h
    rw [namedFormula_equal]
    apply certified_negativeEquality name s t x
    intro heq
    exact h (Formula.realize_equal.mpr heq)

def orderPrograms {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (s t : language.Term α) : SignedPrograms (leFormula s t) name where
  positive := orderAtom false name s t
  negative := orderAtom true name s t
  positive_correct := by
    intro M _ _ x h
    rw [namedFormula_le]
    simpa only [signedOrder, Bool.false_eq_true, ↓reduceIte] using
      certified_orderAtom false name s t x ((realize_leFormula _ s t).mp h)
  negative_correct := by
    intro M _ _ x h
    rw [namedFormula_le]
    have hn : ¬leValue M (s.realize (fun a => (name a).value x))
        (t.realize (fun a => (name a).value x)) :=
      fun he => h ((realize_leFormula _ s t).mpr he)
    simpa only [signedOrder, ↓reduceIte] using certified_orderAtom true name s t x hn

def implicationPrograms {α : Type} [Fintype α] {r : ℕ}
    {D F : language.Formula α} (hF : DeltaZero F) (name : α → Program r)
    (left : SignedPrograms D name) (right : SignedPrograms F name) :
    SignedPrograms (D.imp F) name where
  positive := ternary select (test hF name)
    (ternary implicationFromConsequent right.positive (namedFormula name D) (namedFormula name F))
    (ternary implicationFromNegative left.negative (namedFormula name D) (namedFormula name F))
  negative := .comp negativeImplication
    ![left.positive, right.negative, namedFormula name D, namedFormula name F]
  positive_correct := by
    intro M _ _ x h
    rw [Formula.realize_imp] at h
    rw [ternary_value, test_value, select_truthValue, namedFormula_imp]
    by_cases hFtrue : F.Realize (fun a => (name a).value x)
    · rw [ite_eq_left hFtrue, ternary_value]
      exact certified_implicationFromConsequent axiomVerifier _ _ _
        (right.positive_correct x hFtrue) (namedFormula_pure name D x) (namedFormula_pure name F x)
    · rw [ite_eq_right hFtrue, ternary_value]
      exact certified_implicationFromNegative axiomVerifier _ _ _
        (left.negative_correct x (fun hd => hFtrue (h hd)))
        (namedFormula_pure name D x) (namedFormula_pure name F x)
  negative_correct := by
    intro M _ _ x h
    rw [Formula.realize_imp] at h
    have hDtrue : D.Realize (fun a => (name a).value x) := by
      by_contra hd
      exact h (fun hx => False.elim (hd hx))
    have hFfalse : ¬F.Realize (fun a => (name a).value x) := fun hf => h (fun _ => hf)
    rw [value_comp_four, namedFormula_imp]
    exact certified_negativeImplication axiomVerifier _ _ _ _
      (left.positive_correct x hDtrue) (right.negative_correct x hFfalse)
      (namedFormula_pure name D x) (namedFormula_pure name F x)

/-- Structural induction is performed in `Prop`. Thus the boundedness proof
selects programs only after their all-model correctness has been established. -/
theorem exists_signed {α : Type} {D : language.Formula α} (hD : DeltaZero D) :
    ∀ [Fintype α] (r : ℕ) (name : α → Program r), Nonempty (SignedPrograms D name) := by
  induction hD with
  | falsum =>
    intro _ r name
    exact ⟨bottomPrograms name⟩
  | equal s t =>
    intro _ r name
    exact ⟨equalityPrograms name s t⟩
  | le s t =>
    intro _ r name
    exact ⟨orderPrograms name s t⟩
  | @imp α D F hD hF ihD ihF =>
    intro _ r name
    obtain ⟨left⟩ := ihD r name
    obtain ⟨right⟩ := ihF r name
    exact ⟨implicationPrograms hF name left right⟩
  | @all α t D hD ih =>
    intro _ r name
    obtain ⟨child⟩ := ih (r + 1) (extendName name)
    exact ⟨universalPrograms t hD name child⟩
  | @ex α t D hD ih =>
    intro _ r name
    obtain ⟨child⟩ := ih (r + 1) (extendName name)
    exact ⟨existentialPrograms t hD name child⟩

def compiled {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D) :
    SignedPrograms D (fun i => Program.proj i) :=
  Classical.choice (exists_signed hD r (fun i => Program.proj i))

theorem projection_namedFormula {r : ℕ} (D : language.Formula (Fin r)) :
    namedFormula (fun i => Program.proj i) D = FixedSyntaxPrograms.substitution D := rfl

theorem compiled_positive_correct {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D)
    {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M) (h : D.Realize x) :
    Certified axiomVerifier ((compiled D hD).positive.value x)
      ((FixedSyntaxPrograms.substitution D).value x) := by
  rw [← projection_namedFormula]
  apply (compiled D hD).positive_correct x
  simpa only [Program.value_proj] using h

theorem compiled_negative_correct {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D)
    {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M) (h : ¬D.Realize x) :
    Certified axiomVerifier ((compiled D hD).negative.value x)
      (negValue ((FixedSyntaxPrograms.substitution D).value x)) := by
  rw [← projection_namedFormula]
  apply (compiled D hD).negative_correct x
  simpa only [Program.value_proj] using h

end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.SignedProofs
