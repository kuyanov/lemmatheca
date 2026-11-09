import Lemmatheca.OneGenericSets.Basic
import Lemmatheca.ForcingAndGenericFilters.Orders

/-! The optional comparison uses exactly the reverse-prefix order, without model genericity. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open IncomparableTuringDegrees ComputableTreesAndPaths

abbrev WordCondition := {u : ℕ // ValidCode u}

instance wordConditionPartialOrder : PartialOrder WordCondition where
  le u v := Prefix v.val u.val
  lt u v := Prefix v.val u.val ∧ ¬ Prefix u.val v.val
  le_refl := fun u => prefix_refl u.val
  le_trans := fun _ _ _ hab hbc => prefix_trans hbc hab
  le_antisymm := by
    intro u v huv hvu
    apply Subtype.ext
    have he : word u.val = word v.val :=
      List.IsPrefix.eq_of_length ((prefix_native _ _).mp hvu) (by
        rw [(word_interpretation u.val 0).2.1, (word_interpretation v.val 0).2.1]
        exact Nat.le_antisymm hvu.1 huv.1)
    rw [valid_code_interpretation _ u.property, valid_code_interpretation _ v.property] at he
    simpa only [FiniteSequenceCoding.code_decode] using congrArg FiniteSequenceCoding.code he

def wordConditionSet (S : Set ℕ) : Set WordCondition := {u | u.val ∈ S}

theorem density_bridge (S : Set ℕ) :
    Dense S ↔ Lemmatheca.SetTheory.ForcingAndGenericFilters.Dense (wordConditionSet S)  := by
  constructor
  · intro h u
    obtain ⟨v, hv, hp, hS⟩ := h u.val u.property
    exact ⟨⟨v, hv⟩, hS, hp⟩
  · intro h u hu
    obtain ⟨v, hS, hp⟩ := h ⟨u, hu⟩
    exact ⟨v.val, v.property, hp, hS⟩

end Lemmatheca.ComputabilityTheory.OneGenericSets
