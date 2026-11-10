import Lemmatheca.SuperlowBasisTheorem.Basis
import Lemmatheca.DominationAndHyperimmuneDegrees.Approximation
import Lemmatheca.ComputableTreesAndPaths.Examples

/-! Wrong answers still terminate, and superlow and hyperimmune-free choices differ. -/
namespace Lemmatheca.Entry.SuperlowBasisTheorem

open Lemmatheca.ComputabilityTheory
open SuperlowBasisTheorem LowBasisTheorem UniversalComputation OracleProgramNumberings
open ComputableTreesAndPaths HyperimmuneDegrees

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem empty_answer_history (δ : ℕ → ℕ) (n : ℕ) :
    FiniteSequenceCoding.decode (answerHistory δ ∅ n) = (List.range n).reverse := by
  induction n with
  | zero => simp [answerHistory, FiniteSequenceCoding.decode]
  | succ n ih =>
    have hd (l : ℕ) : FiniteSequenceCoding.decode (FiniteSequenceCoding.cons n l) =
        n :: FiniteSequenceCoding.decode l := by
      rw [← FiniteSequenceCoding.code_decode l, ← FiniteSequenceCoding.code_cons,
        FiniteSequenceCoding.decode_code, FiniteSequenceCoding.decode_code]
    simp only [answerHistory, Set.mem_empty_iff_false, ite_false, hd, ih,
      List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append]

theorem zero_program_excludes_level :
    ∃ m, ∀ u ∈ binaryLevel m,
      0 < IncomparableTuringDegrees.certificateValue u (constantIndex 0) (constantIndex 0) := by
  let i := constantIndex 0
  have ht : StrongReductions.AllOracleTotal (decodeCode i) := by
    intro C x
    change (OracleComputation.eval C (decodeCode (encodeCode (constantCode 0))) x).Dom
    rw [decode_encode, constant_eval]
    trivial
  obtain ⟨m, hm⟩ := StrongReductions.successful_level_exists i ht i
  refine ⟨m, ?_⟩
  intro u hu
  have hv := (binary_level_spec m u).mp hu
  have hl : FiniteSequenceCoding.decode u ∈ StrongReductions.binaryRows m :=
    ((StrongReductions.binaryRows_spec m).1 _).mpr hv
  have h := hm (FiniteSequenceCoding.decode u) hl
  simpa only [FiniteSequenceCoding.code_decode] using h

theorem wrong_answers_destroy_survival (δ : ℕ → ℕ) :
    ∃ m, EmptyLevel Lemmatheca.Entry.ComputableTreesAndPaths.fullTree (answerHistory δ ∅ (constantIndex 0 + 1)) m := by
  obtain ⟨m, hm⟩ := zero_program_excludes_level
  refine ⟨m, ?_⟩
  intro u hu hres
  have hz := hres.2 (constantIndex 0) (by rw [empty_answer_history]; simp)
  exact (Nat.ne_of_gt (hm u hu)) hz

theorem superlow_hyperimmune_free_computable (X : Set ℕ) (hX : Superlow X)
    (hf : HyperimmuneFree X) : ComputablePred (fun e => e ∈ X) := by
  exact hyperimmune_free_below_halting_computable X hf
    (LowSimpleSets.low_below_halting X (superlow_low X hX)).1

theorem no_common_basis_path (T : Set ℕ)
    (hn : ∀ X, Path T X → ¬ ComputablePred (fun e => e ∈ X)) :
    ¬ ∃ X, Path T X ∧ Superlow X ∧ HyperimmuneFree X := by
  rintro ⟨X, hX, hsuper, hfree⟩
  exact hn X hX (superlow_hyperimmune_free_computable X hsuper hfree)

end
end Lemmatheca.Entry.SuperlowBasisTheorem
