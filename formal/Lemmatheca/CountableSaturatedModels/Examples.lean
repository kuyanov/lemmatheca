import Lemmatheca.CountableSaturatedModels.Constructions
import Lemmatheca.BackAndForth.BackAndForthStrictTheory

/-! The existing equality and dense-order theories satisfy both existence criteria. -/
namespace Lemmatheca.Entry.CountableSaturatedModels

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open CountableSaturatedModels
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open QuantifierElimination

theorem equality_models_saturated_prime (M : Type) [Language.empty.Structure M]
    [Nonempty M] [Countable M] [Infinite M] :
    Saturation.OmegaSaturated Language.empty M ∧
      AtomicAndPrimeModels.IsPrime Language.empty.infiniteTheory M := by
  let : M ⊨ Language.empty.infiniteTheory := Language.empty.model_infiniteTheory
  exact categorical_models_saturated_prime Shared.equality_isComplete
    ⟨Theory.ModelType.of _ M, by change Infinite M; infer_instance⟩
    (Cardinal.empty_theory_categorical _ _)

theorem dlo_models_saturated_prime (M : Type) [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] [Countable M] :
    letI : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    Saturation.OmegaSaturated binaryRelLanguage M ∧
      AtomicAndPrimeModels.IsPrime Shared.strictDloTheory M := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  let : M ⊨ Shared.strictDloTheory := Shared.model_strictDloTheory
  let : Infinite M := BackAndForth.strictDlo_models_infinite M
  exact categorical_models_saturated_prime Shared.strictDlo_isComplete
    ⟨Theory.ModelType.of _ M, by change Infinite M; infer_instance⟩
    BackAndForth.strictDlo_countably_categorical

end Lemmatheca.Entry.CountableSaturatedModels
