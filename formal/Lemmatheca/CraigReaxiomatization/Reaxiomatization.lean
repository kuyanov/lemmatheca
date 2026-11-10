import Lemmatheca.CraigReaxiomatization.Padding

/-! The bounded all-padding-length scan and the actual equivalent axiom family. -/
namespace Lemmatheca.ComputabilityTheory.CraigReaxiomatization
open FirstOrder FirstOrder.Language
open Lemmatheca.ProofTheory.CodingFormalProofs
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.ModelTheory
universe u v
variable {L : Language.{u, v}} (S : EffectiveSignature L)
noncomputable section

def paddedAxioms (e : ℕ) : L.Theory :=
  Set.range (fun n => repeatConjunction (snapshot S e n) n)

def recognize (e z : ℕ) : Bool :=
  isSentence S z && (List.range (z + 1)).any
    (fun n => paddingCode n (snapshotCode S e n) == z)

theorem bounded_membership (e z : ℕ) :
    z ∈ codes S (paddedAxioms S e) ↔
      isSentence S z = true ∧ ∃ n ≤ z, paddingCode n (snapshotCode S e n) = z := by
  constructor
  · rintro ⟨A, ⟨n, rfl⟩, hcode⟩
    have hn : paddingCode n (snapshotCode S e n) = z := by
      rw [snapshot_code_eq, padding_code_eq]
      exact hcode
    refine ⟨(sentence_recognition_iff S z).mpr ⟨_, hcode⟩, n, ?_, hn⟩
    exact hn ▸ padding_bound n (snapshotCode S e n)
  · rintro ⟨_, n, _, hn⟩
    refine ⟨repeatConjunction (snapshot S e n) n, ⟨n, rfl⟩, ?_⟩
    rw [← padding_code_eq, ← snapshot_code_eq]
    exact hn

theorem recognize_computable : Computable₂ (recognize S) := by
  let step (p : ℕ × ℕ) (q : ℕ × Bool) : Bool :=
    q.2 || (paddingCode q.1 (snapshotCode S p.1 q.1) == p.2)
  have hp : Computable (fun q : (ℕ × ℕ) × (ℕ × Bool) =>
      paddingCode q.2.1 (snapshotCode S q.1.1 q.2.1)) :=
    padding_code_computable.comp (Computable.fst.comp Computable.snd)
    ((snapshot_code_computable S).comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd))
  have hs : Computable₂ step :=
    (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
      (Primrec.beq.to_comp.comp hp (Computable.snd.comp Computable.fst))).to₂
  have hc := Computable.nat_rec (Primrec.succ.to_comp.comp Computable.snd)
    (Computable.const false) hs
  have hi (e z k : ℕ) : Nat.rec false (fun n acc => step (e,z) (n,acc)) k =
      (List.range k).any (fun n => paddingCode n (snapshotCode S e n) == z) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [step, ih, List.range_succ]
  have ha := hc.of_eq (fun p => hi p.1 p.2 (p.2 + 1))
  exact Primrec.and.to_comp.comp ((primrec_isSentence S).to_comp.comp Computable.snd) ha

theorem recognize_correct (e z : ℕ) :
    recognize S e z = true ↔ z ∈ codes S (paddedAxioms S e) := by
  rw [bounded_membership]
  simp [recognize]

theorem padded_axioms_decidable (e : ℕ) : CodeDecidable S (paddedAxioms S e) := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨recognize S e, (recognize_computable S).comp (Computable.const e) Computable.id, ?_⟩
  funext z
  exact propext (recognize_correct S e z).symm

private theorem derive_from_axioms (sigData : EffectiveSignature L) (T U : L.Theory)
    (hTU : ∀ A ∈ T, Derives U A) (A : L.Sentence) (hA : Derives T A) : Derives U A := by
  let :=  effective_symbols_countable sigData
  apply Lemmatheca.MathematicalLogic.HenkinCompleteness.consequence_iff_derives.mp
  apply Theory.models_sentence_iff.mpr
  intro M
  have hmodel : M ⊨ T := ⟨fun B hB =>
    (Lemmatheca.MathematicalLogic.HenkinCompleteness.consequence_iff_derives.mpr
      (hTU B hB)).realize_sentence M⟩
  let :=  hmodel
  exact (Lemmatheca.MathematicalLogic.HenkinCompleteness.consequence_iff_derives.mpr hA).realize_sentence M

theorem padded_axiom_derivable (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) (A : L.Sentence)
    (hA : A ∈ paddedAxioms S e) : Derives T A := by
  obtain ⟨n, rfl⟩ := hA
  exact (padding_derivability T (snapshot S e n) n).mpr (snapshot_derivable S T e he n)

theorem original_axiom_derivable (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) (A : L.Sentence)
    (hA : A ∈ T) : Derives (paddedAxioms S e) A := by
  obtain ⟨n, hn⟩ := original_axiom_snapshot S T e he A hA
  have hF : Derives (paddedAxioms S e) (snapshot S e n) :=
    (padding_derivability _ _ n).mp (derives_assumption ⟨n, rfl⟩)
  apply derive_from_axioms S ({snapshot S e n} : L.Theory) (paddedAxioms S e) _ A hn
  intro B hB
  have hB' : B = snapshot S e n := Set.mem_singleton_iff.mp hB
  simpa only [hB'] using hF

theorem same_derivability (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) (A : L.Sentence) :
    Derives (paddedAxioms S e) A ↔ Derives T A := by
  exact ⟨derive_from_axioms S _ _ (padded_axiom_derivable S T e he) A,
    derive_from_axioms S _ _ (original_axiom_derivable S T e he) A⟩

theorem same_closure (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) :
    Theories.consequenceClosure (paddedAxioms S e) = Theories.consequenceClosure T := by
  let :=  effective_symbols_countable S
  ext A
  rw [Theories.mem_closure_iff_derives, Theories.mem_closure_iff_derives]
  exact same_derivability S T e he A

theorem same_models (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T)
    (M : Type*) [L.Structure M] [Nonempty M] :
    M ⊨ paddedAxioms S e ↔ M ⊨ T := by
  rw [← Theories.model_closure (paddedAxioms S e) M, same_closure S T e he,
    Theories.model_closure T M]

theorem craig_theorem (T : L.Theory) (hT : CodeEnumerable S T) :
    ∃ e, EffectiveEnumerations.indexSet e = codes S T ∧
      CodeDecidable S (paddedAxioms S e) ∧
      Theories.consequenceClosure (paddedAxioms S e) = Theories.consequenceClosure T := by
  obtain ⟨e, he⟩ := (UniversalComputation.enumerable_iff_index (codes S T)).mp hT
  have hindex : EffectiveEnumerations.indexSet e = codes S T := by
    ext n
    exact (he n).symm
  exact ⟨e, hindex, padded_axioms_decidable S e, same_closure S T e hindex⟩

theorem closed_theory_form (U : L.Theory) (hU : Theories.IsDeductivelyClosed U) :
    CodeEnumerable S U ↔ ∃ B : L.Theory, CodeDecidable S B ∧
      Theories.consequenceClosure B = U := by
  constructor
  · intro h
    obtain ⟨e, _, hd, he⟩ := craig_theorem S U h
    exact ⟨paddedAxioms S e, hd, he.trans hU⟩
  · rintro ⟨B, hd, he⟩
    apply (enumerable_theory_consequences S B hd.to_re).of_eq
    intro n
    rw [← he]
    change (∃ A, sentenceCode S A = n ∧ B ⊨ᵇ A) ↔
      ∃ A ∈ Theories.consequenceClosure B, sentenceCode S A = n
    simp only [Theories.consequenceClosure, Set.mem_ofPred_eq, and_comm]

end
end Lemmatheca.ComputabilityTheory.CraigReaxiomatization
