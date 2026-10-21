import Lemmatheca.CodingFormalProofs.CodingFormalProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

def proofHistory (d : ℕ) : ℕ :=
  FiniteSequenceCoding.historyCode (fun e h => if localCheck S e h then 1 else 0) d

theorem derivationCheck_eq_local (d : ℕ) :
    derivationCheck S d = localCheck S d (proofHistory S d) := by
  unfold derivationCheck earlierFold FiniteSequenceCoding.historyValue
  change decide (0 < if localCheck S d (proofHistory S d) then 1 else 0) = _
  by_cases h : localCheck S d (proofHistory S d) = true
  · simp only [h, ↓reduceIte]; rfl
  · have hf := Bool.eq_false_iff.mpr h
    simp only [hf, Bool.false_eq_true, ↓reduceIte]; rfl

theorem proof_value (d : ℕ) :
    earlierFold (fun e h => if localCheck S e h then 1 else 0) d =
      if derivationCheck S d then 1 else 0 := by
  rw [derivationCheck_eq_local]
  rfl

theorem proofHistory_entry (d p : ℕ) :
    Seq.entry (proofHistory S d) p =
      if p < d then (if derivationCheck S p then 1 else 0) else 0 := by
  unfold proofHistory FiniteSequenceCoding.entry
  rw [FiniteSequenceCoding.history_identity]
  by_cases hp : p < d
  · simp only [List.getElem?_map, List.getElem?_range hp, Option.map_some, Option.getD_some,
      hp, ↓reduceIte]
    exact proof_value S p
  · simp [hp]

theorem proofHistory_positive (d p : ℕ) :
    0 < Seq.entry (proofHistory S d) p ↔ p < d ∧ derivationCheck S p = true := by
  rw [proofHistory_entry]
  by_cases hp : p < d
  · simp only [hp, ↓reduceIte, true_and]
    cases derivationCheck S p <;> decide
  · simp [hp]

theorem derivation_well_formed (d : ℕ) (hd : derivationCheck S d = true) :
    namedForm S 0 (proofConclusion d) = true ∧
      (Seq.decode (proofContext d)).all (namedForm S 0) = true := by
  rw [derivationCheck_eq_local] at hd
  unfold localCheck at hd
  simp only [Bool.and_eq_true] at hd
  exact ⟨hd.1.1.2, hd.1.2⟩

end Lemmatheca.ProofTheory.CodingFormalProofs
