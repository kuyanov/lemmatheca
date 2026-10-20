import Lemmatheca.MathematicalLogic.FormalizedProvability
import Lemmatheca.MathematicalLogic.FirstIncompleteness

/-! An individual reflection instance which a consistent theory cannot prove,
without using the second or third derivability condition. -/
namespace Lemmatheca.MathematicalLogic.FormalizedProvability
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories FirstOrderProofs FirstIncompleteness

theorem godel_reflection_unprovable {T : language.Theory} (P : ProofRepresentation T)
    (hQ : Q ⊆ T) (hcon : Consistent T) :
    ¬ Derives T ((provabilitySentence P (godelSentence P)).imp (godelSentence P)) := by
  intro hr
  apply godel_unprovable P hQ hcon
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  let : M ⊨ Q := (inferInstance : M ⊨ T).mono hQ
  have hf := godel_modelwise P M
  have hh : M ⊨ (provabilitySentence P (godelSentence P)).imp (godelSentence P) :=
    derives_sound hr default (fun B hB => Theory.realize_sentence_of_mem T hB)
  rw [Sentence.realize_imp] at hh
  tauto

end Lemmatheca.MathematicalLogic.FormalizedProvability
