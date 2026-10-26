import Lemmatheca.TuringDegrees.Joins

/-! The positive halting recognizer and finite-use counterexample in the questions. -/
namespace Lemmatheca.Entry.TuringDegrees

open Lemmatheca.ComputabilityTheory.TuringDegrees
open Lemmatheca.ComputabilityTheory.OracleComputation
open Lemmatheca.ComputabilityTheory.UniversalComputation

noncomputable section

def recognizerFunction (x : ℕ) : Part ℕ := (phi x x).map (fun _ => 1)

private theorem recognizer_has_code :
    ∃ r : Nat.Partrec.Code, Nat.Partrec.Code.eval r = recognizerFunction := by
  apply Nat.Partrec.Code.exists_code.mp
  exact Partrec.nat_iff.mp
    ((phi_recursive.comp Computable.id Computable.id).map (Computable.const 1).to₂)

def recognizerCode : Nat.Partrec.Code := Classical.choose recognizer_has_code

theorem recognizerCode_eval (x : ℕ) :
    Nat.Partrec.Code.eval recognizerCode x = (phi x x).map (fun _ => 1) := by
  exact congrFun (Classical.choose_spec recognizer_has_code) x

theorem recognizer_replacement_fails :
    ∃ x, x ∉ haltingDiagonal ∧
      Nat.Partrec.Code.eval recognizerCode x = Part.none ∧
      eval (∅ : Set ℕ) (subst (embed recognizerCode) .query) x = Part.none ∧
      eval haltingDiagonal .query x = Part.some 0 := by
  classical
  obtain ⟨x, hx⟩ := phi_complete Nat.Partrec.none
  have hnot : x ∉ haltingDiagonal := by simp [haltingDiagonal, hx]
  refine ⟨x, hnot, ?_, ?_, ?_⟩
  · simp [recognizerCode_eval, hx]
  · simp [subst, eval_embed, recognizerCode_eval, hx]
  · simp [eval, indicator, hnot]

theorem halting_query_trace (x : ℕ) :
    Derives .query x [(x, indicator (fun n => n ∈ haltingDiagonal) x)]
      (indicator (fun n => n ∈ haltingDiagonal) x) ∧
      Consistent haltingDiagonal [(x, indicator (fun n => n ∈ haltingDiagonal) x)] ∧
      useBound [(x, indicator (fun n => n ∈ haltingDiagonal) x)] = x + 1 := by
  classical
  refine ⟨Derives.query _ _ ?_, ?_, ?_⟩
  · simp only [indicator]
    split_ifs <;> simp
  · simp [Consistent]
  · simp [useBound, querySet]

def flipHaltingBit (u : ℕ) : Set ℕ :=
  {q | if q = u then q ∉ haltingDiagonal else q ∈ haltingDiagonal}

theorem halting_query_no_uniform_bound (u : ℕ) :
    (∀ q < u, indicator (fun n => n ∈ flipHaltingBit u) q =
      indicator (fun n => n ∈ haltingDiagonal) q) ∧
      eval (flipHaltingBit u) .query u ≠ eval haltingDiagonal .query u := by
  classical
  constructor
  · intro q hq
    have hne : q ≠ u := by omega
    simp [indicator, flipHaltingBit, hne]
  · by_cases h : u ∈ haltingDiagonal <;> simp [eval, indicator, flipHaltingBit, h]

theorem complement_sets_distinct (A : Set ℕ) : A ≠ Aᶜ := by
  intro h
  have hzero := Set.ext_iff.mp h 0
  simp only [Set.mem_compl_iff] at hzero
  tauto

end
end Lemmatheca.Entry.TuringDegrees
