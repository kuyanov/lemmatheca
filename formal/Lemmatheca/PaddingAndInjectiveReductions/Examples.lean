import Lemmatheca.PaddingAndInjectiveReductions.Padding
import Lemmatheca.RicesTheorem.RicesTheorem

/-! Fresh names and the finite obstruction to arbitrary injective reductions. -/
namespace Lemmatheca.Entry.PaddingAndInjectiveReductions

open ComputabilityTheory.UniversalComputation
open ComputabilityTheory.PaddingAndInjectiveReductions

theorem fresh_contrasting_behavior (lcode : ℕ) :
    (∃ e, freshIndex e lcode ∉ ComputabilityTheory.FiniteSequenceCoding.decode lcode ∧
      ∀ x, phi (freshIndex e lcode) x = Part.none) ∧
    (∃ e, freshIndex e lcode ∉ ComputabilityTheory.FiniteSequenceCoding.decode lcode ∧
      ∀ x, phi (freshIndex e lcode) x = Part.some 0) := by
  obtain ⟨e, he⟩ := phi_complete Nat.Partrec.none
  refine ⟨⟨e, (escapingTag_spec e lcode).2.1, ?_⟩,
    ⟨Encodable.encode Nat.Partrec.Code.zero,
      (escapingTag_spec (Encodable.encode Nat.Partrec.Code.zero) lcode).2.1, ?_⟩⟩
  · intro x
    rw [freshIndex_eval, he]
  · intro x
    rw [freshIndex_eval]
    simp only [phi, Denumerable.ofNat_encode, Nat.Partrec.Code.eval]
    rfl

def collapseMap (n : ℕ) : ℕ := if n ≤ 1 then 0 else 1

def doubleMap (n : ℕ) : ℕ := 2 * n

theorem collapseMap_contract :
    Primrec collapseMap ∧ ∀ n, n ∈ ({0, 1} : Set ℕ) ↔ collapseMap n ∈ ({0} : Set ℕ) := by
  refine ⟨Primrec.ite (Primrec.nat_le.comp Primrec.id (Primrec.const 1))
    (Primrec.const 0) (Primrec.const 1), ?_⟩
  intro n
  change (n = 0 ∨ n = 1) ↔ (if n ≤ 1 then 0 else 1) = 0
  constructor
  · rintro (rfl | rfl) <;> rfl
  · intro h
    split_ifs at h with hn
    · omega

theorem doubleMap_contract :
    Primrec doubleMap ∧ ∀ n, n ∈ ({0} : Set ℕ) ↔ doubleMap n ∈ ({0, 1} : Set ℕ) := by
  refine ⟨Primrec.nat_mul.comp (Primrec.const 2) Primrec.id, ?_⟩
  intro n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, doubleMap]
  omega

theorem finite_not_oneone : ¬ (({0, 1} : Set ℕ) ≤₁ ({0} : Set ℕ)) := by
  rintro ⟨f, _hf, hi, hr⟩
  have h0 : f 0 = 0 := (hr 0).mp (Or.inl rfl)
  have h1 : f 1 = 0 := (hr 1).mp (Or.inr rfl)
  exact Nat.zero_ne_one (hi (h0.trans h1.symm))

end Lemmatheca.Entry.PaddingAndInjectiveReductions
