import Lemmatheca.IncomparableTuringDegrees.Prefixes

/-! A short word cannot certify an unanswered query. -/
namespace Lemmatheca.Entry.IncomparableTuringDegrees

open Lemmatheca.ComputabilityTheory
open OracleComputation OracleProgramNumberings

noncomputable section

theorem unanswered_query :
    let u := FiniteSequenceCoding.code [0]
    IncomparableTuringDegrees.Realizes u (∅ : Set ℕ) ∧
      IncomparableTuringDegrees.Realizes u ({1} : Set ℕ) ∧
      phi ∅ 4 1 = Part.some 0 ∧ phi ({1} : Set ℕ) 4 1 = Part.some 1 ∧
      IncomparableTuringDegrees.certificateValue u 4 1 = 0 := by
  let u := FiniteSequenceCoding.code [0]
  have hlen : IncomparableTuringDegrees.wordLength u = 1 := by
    simp [u, IncomparableTuringDegrees.wordLength, FiniteSequenceCoding.length]
  have hr (A : Set ℕ) (hA : 0 ∉ A) : IncomparableTuringDegrees.Realizes u A := by
    intro q hq
    have he : q = 0 := by rw [hlen] at hq; omega
    subst q
    simp [u, IncomparableTuringDegrees.wordBit, PostsTheorem.beta,
      FiniteSequenceCoding.entry, UniversalComputation.indicator, hA]
  refine ⟨hr ∅ (by simp), hr {1} (by simp), ?_, ?_, ?_⟩
  · simp [phi, decodeCode, eval, UniversalComputation.indicator]
  · simp [phi, decodeCode, eval, UniversalComputation.indicator]
  · apply PostsTheorem.finiteValue_outside
    rw [hlen]

end
end Lemmatheca.Entry.IncomparableTuringDegrees
