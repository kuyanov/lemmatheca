import Lemmatheca.SetTheory.RadoHall

/-! The finite counting obstruction and the infinite-member Hall counterexample. -/

namespace Lemmatheca.Entry.RadoHallExamples

open Lemmatheca.SetTheory.RadoHall

theorem three_two_value_obstruction :
    (∀ s : Finset (Fin 3), s.card ≤ 2 →
      s.card ≤ (s.biUnion (fun _ => ({0, 1} : Finset ℕ))).card) ∧
    ¬ ∃ f : Fin 3 → ℕ, Function.Injective f ∧ ∀ i, f i ∈ ({0, 1} : Finset ℕ) := by
  constructor
  · intro s hs
    by_cases h : s.Nonempty
    · have hu : s.biUnion (fun _ => ({0, 1} : Finset ℕ)) = {0, 1} := by
        ext x
        simp only [Finset.mem_biUnion]
        exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx =>
          let ⟨i, hi⟩ := h
          ⟨i, hi, hx⟩⟩
      simpa [hu] using hs
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [he]
  · rintro ⟨f, hf, hmem⟩
    let g : Fin 3 → Fin 2 := fun i => ⟨f i, by
      have hi := hmem i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      omega⟩
    have hg : Function.Injective g := by
      intro i j hij
      apply hf
      exact congrArg Fin.val hij
    have hc := Fintype.card_le_of_injective g hg
    simp at hc

theorem three_modified_witness :
    Function.Injective (fun i : Fin 3 => i.val) ∧
    ∀ i : Fin 3, i.val ∈ (if i = 2 then ({1, 2} : Finset ℕ) else {0, 1}) := by
  exact ⟨Fin.val_injective, by decide⟩

/-- Index zero allows every positive natural, while positive indices force themselves. -/
def PositiveAvailable (n : ℕ) : Set ℕ := if n = 0 then Set.Ioi 0 else {n}

theorem positive_family_finite_witness (s : Finset ℕ) :
    let m := s.sup id + 1
    let f : s → ℕ := fun i => if i.val = 0 then m else i.val
    Function.Injective f ∧ ∀ i : s, f i ∈ PositiveAvailable i := by
  dsimp only
  have hbound (i : s) : i.val < s.sup id + 1 := by
    have hi : i.val ≤ s.sup id := Finset.le_sup (f := id) i.property
    omega
  constructor
  · intro i j hij
    have hi := hbound i
    have hj := hbound j
    apply Subtype.ext
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · exact hi0.trans hj0.symm
    · simp only [hi0, hj0, ite_true, ite_false] at hij
      omega
    · simp only [hi0, hj0, ite_true, ite_false] at hij
      omega
    · simpa only [hi0, hj0, ite_false] using hij
  · intro i
    by_cases hi0 : i.val = 0
    · simp [PositiveAvailable, hi0]
    · simp [PositiveAvailable, hi0]

theorem positive_family_no_global :
    ¬ ∃ f : ℕ → ℕ, IsDistinctRepresentative PositiveAvailable f := by
  rintro ⟨f, hf, hmem⟩
  have hpos : 0 < f 0 := by simpa [PositiveAvailable] using hmem 0
  have hforced : f (f 0) = f 0 := by
    simpa [PositiveAvailable, hpos.ne'] using hmem (f 0)
  have hzero := hf hforced
  omega

end Lemmatheca.Entry.RadoHallExamples
