import Lemmatheca.SetTheory.Choice
import Lemmatheca.SetTheory.Ordinals

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.AxiomOfChoice
open Set
universe u v

/-- Exactly two strict total orders extend the strict empty relation on two points. -/
theorem two_point_extensions :
    {r : Fin 2 → Fin 2 → Prop | Std.Irrefl r ∧ IsTrans (Fin 2) r ∧
      ∀ a b, a ≠ b → r a b ∨ r b a} =
    {((· < ·) : Fin 2 → Fin 2 → Prop), (fun a b : Fin 2 => b < a)} := by
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hi, ht, htot⟩
    have hir : ∀ a, ¬ r a a := hi.irrefl
    have htr : ∀ a b c, r a b → r b c → r a c := ht.trans
    rcases htot 0 1 (by decide) with h | h
    · left
      funext a b
      fin_cases a <;> fin_cases b <;> apply propext <;> norm_num <;> grind
    · right
      funext a b
      fin_cases a <;> fin_cases b <;> apply propext <;> norm_num <;> grind
  · rintro (rfl | rfl)
    · exact ⟨inferInstance, inferInstance, fun a b h => lt_or_gt_of_ne h⟩
    · refine ⟨⟨fun a => lt_irrefl a⟩, ⟨fun a b c hab hbc => hbc.trans hab⟩, ?_⟩
      intro a b h
      exact (lt_or_gt_of_ne h).symm

end Lemmatheca.Entry.AxiomOfChoice
