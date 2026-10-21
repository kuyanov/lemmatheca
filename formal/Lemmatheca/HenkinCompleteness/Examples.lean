import Lemmatheca.FirstOrderProofs.Examples

/-! A fixed two-element example showing why witness freshness is necessary. -/
namespace Lemmatheca.Entry.HenkinCompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.Entry.FirstOrderProofs

theorem nonfresh_witness_breaks_consistency :
    Consistent ({witnessBody.ex, namedProperty.not} : witnessLanguage.Theory) ∧
    ¬ Consistent ({witnessBody.ex, namedProperty.not,
      witnessBody.ex.imp namedProperty} : witnessLanguage.Theory) := by
  classical
  constructor
  · let : witnessLanguage.Structure Bool := witnessStructure
    apply consistent_of_model (default : Empty → Bool)
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact witness_countermodel.1
    · rcases Set.mem_singleton_iff.mp hA with rfl
      exact witness_countermodel.2.2
  · intro hcon
    apply hcon
    let Γ : Finset witnessLanguage.Sentence :=
      {witnessBody.ex, namedProperty.not, witnessBody.ex.imp namedProperty}
    refine ⟨Γ, by simp [Γ], ?_⟩
    apply Proof.negElim (A := namedProperty)
    · exact .impElim (A := witnessBody.ex) (.assumption (by simp [Γ])) (.assumption (by simp [Γ]))
    · exact .assumption (by simp [Γ])

end Lemmatheca.Entry.HenkinCompleteness
