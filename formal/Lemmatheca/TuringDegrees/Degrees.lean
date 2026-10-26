import Lemmatheca.TuringDegrees.Reductions

/-! The set-degree quotient, using the generic preorder antisymmetrization. -/
namespace Lemmatheca.ComputabilityTheory.TuringDegrees

open UniversalComputation

noncomputable section

/-- A wrapper keeps oracle reducibility separate from the subset order on sets. -/
structure Problem where
  carrier : Set ℕ

instance problemPreorder : Preorder Problem where
  le A B := Reducible A.carrier B.carrier
  le_refl A := reducible_refl A.carrier
  le_trans _ _ _ := reducible_trans

abbrev Degree := Antisymmetrization Problem (· ≤ ·)

def degree (A : Set ℕ) : Degree := toAntisymmetrization (· ≤ ·) ⟨A⟩

def literalClass (A : Set ℕ) : Set (Set ℕ) := {B | Equivalent B A}

def classOf (d : Degree) : Set (Set ℕ) := {A | degree A = d}

theorem degree_surjective : Function.Surjective degree := by
  intro d
  induction d using Antisymmetrization.ind with
  | _ A => exact ⟨A.carrier, rfl⟩

theorem classOf_degree (A : Set ℕ) : classOf (degree A) = literalClass A := by
  ext B
  exact toAntisymmetrization_eq (· ≤ ·) (⟨B⟩ : Problem) ⟨A⟩

theorem classOf_injective : Function.Injective classOf := by
  intro a b h
  obtain ⟨A, rfl⟩ := degree_surjective a
  have hA : A ∈ classOf (degree A) := rfl
  rw [h] at hA
  exact hA

theorem degree_eq_iff_class_eq (A B : Set ℕ) :
    degree A = degree B ↔ literalClass A = literalClass B := by
  rw [← classOf_degree, ← classOf_degree]
  exact classOf_injective.eq_iff.symm

def zeroDegree : Degree := degree ∅

theorem zeroDegree_le (d : Degree) : zeroDegree ≤ d := by
  obtain ⟨A, rfl⟩ := degree_surjective d
  obtain ⟨r, _, hr⟩ := computable_uniform ∅ ⟨inferInstance, Computable.const false⟩
  exact ⟨OracleComputation.embed r, hr A⟩

theorem degree_eq_zero_iff (A : Set ℕ) :
    degree A = zeroDegree ↔ ComputablePred (fun n => n ∈ A) := by
  constructor
  · intro h
    apply (reducible_empty_iff A).mp
    have := le_of_eq h
    exact this
  · intro h
    apply le_antisymm
    · exact (reducible_empty_iff A).mpr h
    · exact zeroDegree_le _

theorem zero_lt_halting : zeroDegree < degree haltingDiagonal := by
  apply lt_of_le_of_ne (zeroDegree_le _)
  intro h
  exact haltingDiagonal_undecidable ((degree_eq_zero_iff _).mp h.symm)

end
end Lemmatheca.ComputabilityTheory.TuringDegrees
