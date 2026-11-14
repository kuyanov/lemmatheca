import Lemmatheca.FirstOrderNegativeTranslation.Public
import Lemmatheca.FirstOrderNegativeTranslation.Conventions
import Lemmatheca.IntuitionisticFirstOrderQuantifierPrinciples.Countermodels

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
local instance negativeExamplesFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

open Kripke

/-- Quantified excluded middle for the supplied arbitrary one-slot body. -/
def quantifiedEM (R : BoundedFormula L α 1) : Formula L α := .all (.disj R (.neg R))

theorem negative_quantifiedEM (R : BoundedFormula L α 1) :
    negative (quantifiedEM R) =
      .all (.neg (.neg (.disj (negative R) (.neg (negative R))))) := by
  rfl

def quantifiedEM_classical (e : Bool) (R : BoundedFormula L α 1) :
    NaturalDeduction.Derivation true e L ∅ (quantifiedEM R) := by
  apply NaturalDeduction.Derivation.allIntro
  exact NaturalDeduction.Derivation.excludedMiddle _ R.toFormula

/-- The direct construction retains all translated occurrences inside the universal. -/
def quantifiedEM_intuitionistic (e : Bool) (R : BoundedFormula L α 1) :
    NaturalDeduction.Derivation false e L ∅ (negative (quantifiedEM R)) := by
  rw [negative_quantifiedEM]
  apply NaturalDeduction.Derivation.allIntro
  exact QuantifierPrinciples.doubleNegExcludedMiddle_raw e _ (negative R).toFormula

def eventual_G_intuitionistic (e : Bool) :
    NaturalDeduction.Derivation false e QuantifierPrinciples.predicateLanguage ∅
      (negative QuantifierPrinciples.allExcludedMiddle) :=
  quantifiedEM_intuitionistic e QuantifierPrinciples.predicateBody

/-- The explicit premise in the unchanged-hypotheses counterexample. -/
def untranslatedPremise : Formula QuantifierPrinciples.predicateLanguage Empty :=
  .neg QuantifierPrinciples.allPredicate

def untranslatedContext : NaturalDeduction.Context QuantifierPrinciples.predicateLanguage Empty :=
  {untranslatedPremise}

def sourceAssumption (e : Bool) :
    NaturalDeduction.Derivation true e QuantifierPrinciples.predicateLanguage
      untranslatedContext untranslatedPremise := by
  exact .assumption (Finset.mem_singleton_self _)

theorem negative_untranslatedPremise :
    negative untranslatedPremise = .neg QuantifierPrinciples.allDoubleNegPredicate := by
  rfl

theorem eventual_not_translatedPremise (w : ℕ) :
    ¬ Holds QuantifierPrinciples.eventualModel w (negative untranslatedPremise) Empty.elim := by
  rw [negative_untranslatedPremise]
  intro h
  have hp := h w le_rfl
  rw [transport_refl] at hp
  exact hp (QuantifierPrinciples.eventual_allDoubleNegPredicate w)

theorem untranslated_nonderivable (e : Bool) :
    ¬ NaturalDeduction.Derives false e QuantifierPrinciples.predicateLanguage
      untranslatedContext (negative untranslatedPremise) := by
  rintro ⟨p⟩
  apply eventual_not_translatedPremise 0
  apply proof_sound QuantifierPrinciples.eventualModel p 0 Empty.elim
  intro B hB
  simp only [untranslatedContext, Finset.mem_singleton] at hB
  subst B
  exact QuantifierPrinciples.eventual_neg_allPredicate 0

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
