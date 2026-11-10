import Lemmatheca.CraigReaxiomatization.Reaxiomatization

/-! Empty input and the failure of a uniquely chosen padding decomposition. -/
namespace Lemmatheca.Entry.CraigReaxiomatization
open FirstOrder FirstOrder.Language
open Lemmatheca.ComputabilityTheory
open Lemmatheca.ComputabilityTheory.CraigReaxiomatization
open Lemmatheca.ProofTheory.CodingFormalProofs
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v
variable {L : Language.{u, v}} (S : EffectiveSignature L)
noncomputable section

theorem empty_snapshot (e : ℕ) (he : EffectiveEnumerations.indexSet e = ∅) (s : ℕ) :
    snapshot S e s = (⊤ : L.Sentence) := by
  have hc : stageCodes S e s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    have hm : c ∈ EffectiveEnumerations.indexSet e :=
      (EffectiveEnumerations.stage_union e c).mpr
        ⟨s, ((mem_stage_codes S e s c).mp hc).1⟩
    rw [he] at hm
    exact hm
  simp [snapshot, stageSentences, hc]

theorem empty_padded_axioms (e : ℕ) (he : EffectiveEnumerations.indexSet e = ∅) :
    paddedAxioms S e = Set.range (fun n => repeatConjunction (⊤ : L.Sentence) n) := by
  unfold paddedAxioms
  apply congrArg Set.range
  funext n
  rw [empty_snapshot S e he n]

theorem two_padding_descriptions (A : L.Sentence) :
    repeatConjunction A 1 = repeatConjunction (A ⊓ A) 0 := by
  rfl

theorem position_zero_misses_member (e : ℕ) (he : EffectiveEnumerations.indexSet e = ∅) :
    let A : L.Sentence := ⊤ ⊓ ⊤
    A ∈ paddedAxioms S e ∧ sentenceCode S A ≠ snapshotCode S e 0 := by
  dsimp only
  constructor
  · refine ⟨1, ?_⟩
    change repeatConjunction (snapshot S e 1) 1 = (⊤ : L.Sentence) ⊓ ⊤
    rw [empty_snapshot S e he 1]
    rfl
  · rw [snapshot_code_eq S e 0, empty_snapshot S e he 0]
    change andCode (sentenceCode S (⊤ : L.Sentence)) (sentenceCode S (⊤ : L.Sentence)) ≠
      sentenceCode S (⊤ : L.Sentence)
    exact Nat.ne_of_gt (left_lt_and_code _ _)

end
end Lemmatheca.Entry.CraigReaxiomatization
