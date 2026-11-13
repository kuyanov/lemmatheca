import Lemmatheca.ScottSentencesForCountableStructures.ScottAnalysis
import Lemmatheca.InfinitaryLogic.Infinity

/-! Infinitude is a Scott sentence for the countable pure equality structure. -/
namespace Lemmatheca.Entry.ScottSentencesForCountableStructures

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.InfinitaryLogic

universe w

local instance equalityStructure (X : Type w) : Language.empty.Structure X :=
  Language.emptyStructure

theorem infinity_countable_equality (N : Type w) [Countable N] :
    Sentence.Realize (infinitySentence Language.empty) N ↔
      Nonempty (ℕ ≃[Language.empty] N) := by
  rw [infinitySentence_realize, FirstOrder.Language.empty.nonempty_equiv_iff]
  constructor
  · intro h
    let := h
    simp only [Cardinal.mk_eq_aleph0 ℕ, Cardinal.mk_eq_aleph0 N, Cardinal.lift_aleph0]
  · intro h
    have hcard : Cardinal.mk N = Cardinal.aleph0 := by
      simpa only [Cardinal.mk_eq_aleph0 ℕ, Cardinal.lift_aleph0, Cardinal.lift_eq_aleph0] using h.symm
    exact Cardinal.infinite_iff.mpr hcard.ge

theorem infinity_has_uncountable_model :
    Sentence.Realize (infinitySentence Language.empty) (Set ℕ) ∧
      ¬ Countable (Set ℕ) := by
  refine ⟨(infinitySentence_realize (L := Language.empty) (Set ℕ)).mpr inferInstance, ?_⟩
  intro hc
  have hle := Cardinal.mk_le_aleph0_iff.mpr hc
  have hlt : Cardinal.aleph0 < Cardinal.mk (Set ℕ) := by
    simpa only [Cardinal.mk_set, Cardinal.mk_eq_aleph0 ℕ] using
      Cardinal.cantor Cardinal.aleph0
  exact hlt.not_ge hle

end Lemmatheca.Entry.ScottSentencesForCountableStructures
