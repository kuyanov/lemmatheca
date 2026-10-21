import Lemmatheca.JointConsistency.JointConsistency

namespace Lemmatheca.Entry.JointConsistency
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-- Equality alone can separate separately consistent theories. -/
theorem equality_obstruction :
    Consistent ({allPairEqual Language.empty} : Language.empty.Theory) ∧
    Consistent ({(allPairEqual Language.empty).not} : Language.empty.Theory) ∧
    ¬ ({allPairEqual Language.empty, (allPairEqual Language.empty).not} :
      Language.empty.Theory).IsSatisfiable := by
  refine ⟨?_, ?_, ?_⟩
  · let : Language.empty.Structure Unit := Language.emptyStructure
    apply theory_consistent_of_model (M := Unit)
    constructor
    intro A hA
    rw [Set.mem_singleton_iff.mp hA, allPairEqual_realize]
    infer_instance
  · let : Language.empty.Structure Bool := Language.emptyStructure
    apply theory_consistent_of_model (M := Bool)
    constructor
    intro A hA
    rw [Set.mem_singleton_iff.mp hA, Sentence.realize_not, allPairEqual_realize]
    intro hs
    exact Bool.false_ne_true (@Subsingleton.elim Bool hs false true)
  · intro h
    let M := h.some
    have hp := Theory.realize_sentence_of_mem (M := M)
      ({allPairEqual Language.empty, (allPairEqual Language.empty).not} : Language.empty.Theory)
      (by simp : allPairEqual Language.empty ∈ _)
    have hn := Theory.realize_sentence_of_mem (M := M)
      ({allPairEqual Language.empty, (allPairEqual Language.empty).not} : Language.empty.Theory)
      (by simp : (allPairEqual Language.empty).not ∈ _)
    exact hn hp

end Lemmatheca.Entry.JointConsistency
