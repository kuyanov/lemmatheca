import Lemmatheca.DiagonalLemma.DiagonalLemma

open Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory Lemmatheca.ProofTheory

namespace Lemmatheca.Entry.DiagonalLemma
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
open Lemmatheca.ProofTheory.DiagonalLemma

/-- Equality of the unique free variable with itself. -/
def reflexiveProperty : language.Formula Unit := (Term.var ()).equal (.var ())

/-- The sentence constructed from a true numerical equality is provable in Q. -/
theorem true_property_fixedPoint : Derives Q (fixedPoint reflexiveProperty) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  apply (fixedPoint_modelwise reflexiveProperty).mpr
  rw [realize_numeralSubstitution]
  simp [reflexiveProperty]

/-- The sentence constructed from an impossible disequality is refutable in Q. -/
theorem false_property_fixedPoint : Derives Q (fixedPoint reflexiveProperty.not).not := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  apply (Sentence.realize_not M).mpr
  intro h
  have hh := (fixedPoint_modelwise reflexiveProperty.not).mp h
  simp [realize_numeralSubstitution, reflexiveProperty] at hh

end Lemmatheca.Entry.DiagonalLemma
