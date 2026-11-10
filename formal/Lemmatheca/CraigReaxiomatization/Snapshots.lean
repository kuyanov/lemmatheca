import Lemmatheca.EffectiveEnumerations.Stages
import Lemmatheca.EffectiveTheories.CertifiedProofSearch
import Lemmatheca.TheoriesAndAxiomatization.Theories

/-! The actual original-language sentence snapshots of an enumerable axiom set. -/
namespace Lemmatheca.ComputabilityTheory.CraigReaxiomatization
open FirstOrder FirstOrder.Language
open Lemmatheca.ProofTheory.CodingFormalProofs
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.ModelTheory
universe u v
variable {L : Language.{u, v}} (S : EffectiveSignature L)
noncomputable section
open Classical

def codes (T : L.Theory) : Set ℕ := {n | ∃ A ∈ T, sentenceCode S A = n}

def CodeDecidable (T : L.Theory) : Prop := ComputablePred (codes S T)

/-- Recognition supplies an actual sentence; invalid codes use the unused truth fallback. -/
def decodeSentence (c : ℕ) : L.Sentence :=
  if h : isSentence S c = true then Classical.choose ((sentence_recognition_iff S c).mp h)
  else ⊤

def stageCodes (e s : ℕ) : List ℕ :=
  (List.range s).filter (fun c => (EffectiveEnumerations.stageTest e s c == 1) && isSentence S c)

def stageSentences (e s : ℕ) : List L.Sentence :=
  (stageCodes S e s).map (decodeSentence S)

def snapshot (e s : ℕ) : L.Sentence :=
  (stageSentences S e s).foldl (· ⊓ ·) ⊤

def snapshotCode (e s : ℕ) : ℕ :=
  (stageCodes S e s).foldl andCode (impCode botCode botCode)

theorem decode_sentence_code (c : ℕ) (hc : isSentence S c = true) :
    sentenceCode S (decodeSentence S c) = c := by
  rw [decodeSentence, dite_eq_left hc]
  exact Classical.choose_spec ((sentence_recognition_iff S c).mp hc)

theorem mem_stage_codes (e s c : ℕ) :
    c ∈ stageCodes S e s ↔ c ∈ EffectiveEnumerations.stage e s ∧ isSentence S c = true := by
  simp only [stageCodes, List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  rw [(EffectiveEnumerations.stage_test_spec e s c).2]
  constructor
  · rintro ⟨_, hm, hs⟩
    exact ⟨hm, hs⟩
  · rintro ⟨hm, hs⟩
    exact ⟨hm.1, hm, hs⟩

theorem mem_stage_sentences (e s : ℕ) (A : L.Sentence) :
    A ∈ stageSentences S e s ↔ sentenceCode S A ∈ EffectiveEnumerations.stage e s := by
  rw [stageSentences, List.mem_map]
  constructor
  · rintro ⟨c, hc, hA⟩
    have hs := (mem_stage_codes S e s c).mp hc
    have hcode : sentenceCode S A = c := by
      rw [← hA]
      exact decode_sentence_code S c hs.2
    exact hcode.symm ▸ hs.1
  · intro hA
    have hs : isSentence S (sentenceCode S A) = true :=
      (sentence_recognition_iff S _).mpr ⟨A, rfl⟩
    refine ⟨sentenceCode S A, (mem_stage_codes S e s _).mpr ⟨hA, hs⟩, ?_⟩
    apply sentence_code_injective S
    exact decode_sentence_code S _ hs

theorem snapshot_code_eq (e s : ℕ) :
    snapshotCode S e s = sentenceCode S (snapshot S e s) := by
  have hfold : ∀ (D : List ℕ), (∀ c ∈ D, isSentence S c = true) →
      ∀ A : L.Sentence, D.foldl andCode (sentenceCode S A) =
        sentenceCode S ((D.map (decodeSentence S)).foldl (· ⊓ ·) A) := by
    intro D
    induction D with
    | nil => intro _ A; rfl
    | cons c D ih =>
      intro hD A
      simp only [List.foldl_cons, List.map_cons]
      have hc : andCode (sentenceCode S A) c =
          sentenceCode S (A ⊓ decodeSentence S c) := by
        change andCode (sentenceCode S A) c =
          andCode (sentenceCode S A) (sentenceCode S (decodeSentence S c))
        exact congrArg (andCode (sentenceCode S A)) (decode_sentence_code S c (hD c (by simp))).symm
      rw [hc]
      exact ih (fun d hd => hD d (List.mem_cons_of_mem c hd)) _
  change (stageCodes S e s).foldl andCode (sentenceCode S (⊤ : L.Sentence)) = _
  exact hfold _ (fun c hc => ((mem_stage_codes S e s c).mp hc).2) _

section
attribute [local irreducible] EffectiveEnumerations.stageTest isSentence andCode

theorem snapshot_code_computable : Computable₂ (snapshotCode S) := by
  have ht : Primrec (fun q : (ℕ × ℕ) × ℕ =>
      EffectiveEnumerations.stageTest q.1.1 q.1.2 q.2) :=
    EffectiveEnumerations.stage_test_primitive
  have hkeep : Primrec (fun q : (ℕ × ℕ) × ℕ =>
      (EffectiveEnumerations.stageTest q.1.1 q.1.2 q.2 == 1) && isSentence S q.2) :=
    by
      simpa only [Bool.beq_eq_decide_eq] using
        PrimitiveRecursiveAutomation.and (Primrec.eq.comp ht (Primrec.const 1)).decide
          ((primrec_isSentence S).comp Primrec.snd)
  have hstep : Primrec (fun q : (ℕ × ℕ) × (ℕ × List ℕ) =>
      cond ((EffectiveEnumerations.stageTest q.1.1 q.1.2 q.2.1 == 1) && isSentence S q.2.1)
        (q.2.1 :: q.2.2) q.2.2) :=
    Primrec.cond (hkeep.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hcodes : Primrec (fun q : ℕ × ℕ => stageCodes S q.1 q.2) :=
    (Primrec.list_foldr (Primrec.list_range.comp Primrec.snd) (Primrec.const []) hstep.to₂).of_eq
      (fun q => by
        simpa only [stageCodes] using (List.filter_eq_foldr
          (fun c => (EffectiveEnumerations.stageTest q.1 q.2 c == 1) && isSentence S c)
          (List.range q.2)).symm)
  have hand : Primrec₂ andCode := by
    unfold Primrec₂ andCode negCode impCode botCode
    fun_prop
  have hcons : Primrec₂ (fun (_ : ℕ × ℕ) (q : ℕ × ℕ) => andCode q.1 q.2) :=
    hand.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hfold : Primrec (fun q : ℕ × ℕ => snapshotCode S q.1 q.2) :=
    Primrec.list_foldl hcodes (Primrec.const (impCode botCode botCode)) hcons
  exact hfold.to_comp

end

private theorem proof_foldl_intro (Γ : Finset L.Sentence) (D : List L.Sentence)
    (A : L.Sentence) (hA : Proof L Γ A) (hD : ∀ B ∈ D, B ∈ Γ) :
    Proof L Γ (D.foldl (· ⊓ ·) A) := by
  induction D generalizing A with
  | nil => exact hA
  | cons B D ih =>
    exact ih (A ⊓ B) (.conjIntro hA (.assumption (hD B (by simp))))
      (fun C hC => hD C (List.mem_cons_of_mem B hC))

private theorem proof_foldl_left (Γ : Finset L.Sentence) (D : List L.Sentence)
    (A : L.Sentence) (h : Proof L Γ (D.foldl (· ⊓ ·) A)) : Proof L Γ A := by
  induction D generalizing A with
  | nil => exact h
  | cons B D ih => exact .conjElimLeft (ih (A ⊓ B) h)

private theorem proof_foldl_member (Γ : Finset L.Sentence) (D : List L.Sentence)
    (A B : L.Sentence) (hB : B ∈ D) (h : Proof L Γ (D.foldl (· ⊓ ·) A)) :
    Proof L Γ B := by
  induction D generalizing A with
  | nil => simp at hB
  | cons C D ih =>
    rcases List.mem_cons.mp hB with rfl | hB
    · exact .conjElimRight (proof_foldl_left Γ D (A ⊓ B) h)
    · exact ih (A ⊓ C) hB h

private theorem derives_through_axioms (S : EffectiveSignature L) {T U : L.Theory} {A : L.Sentence}
    (hall : ∀ B ∈ T, Derives U B) (h : Derives T A) : Derives U A := by
  let := effective_symbols_countable S
  apply Lemmatheca.MathematicalLogic.HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  exact derives_sound h (default : Empty → M) (fun B hB =>
    derives_sound (hall B hB) (default : Empty → M)
      (fun C hC => Theory.realize_sentence_of_mem U hC))

theorem snapshot_derivable (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) (s : ℕ) :
    Derives T (snapshot S e s) := by
  let Γ : Finset L.Sentence := (stageSentences S e s).toFinset
  have hΓ : (↑Γ : L.Theory) ⊆ T := by
    intro A hA
    have hm : sentenceCode S A ∈ EffectiveEnumerations.indexSet e :=
      (EffectiveEnumerations.stage_union e _).mpr
        ⟨s, (mem_stage_sentences S e s A).mp (List.mem_toFinset.mp hA)⟩
    rw [he] at hm
    obtain ⟨B, hB, hcode⟩ := hm
    exact sentence_code_injective S hcode ▸ hB
  refine ⟨Γ, hΓ, ?_⟩
  apply proof_foldl_intro Γ (stageSentences S e s) ⊤
  · change Proof L Γ ((⊥ : L.Sentence).imp ⊥)
    exact .impIntro (.assumption (by simp))
  · intro A hA
    exact List.mem_toFinset.mpr hA

theorem original_axiom_snapshot (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) (A : L.Sentence) (hA : A ∈ T) :
    ∃ s, Derives ({snapshot S e s} : L.Theory) A := by
  have hc : sentenceCode S A ∈ EffectiveEnumerations.indexSet e := by
    rw [he]
    exact ⟨A, hA, rfl⟩
  obtain ⟨s, hs⟩ := (EffectiveEnumerations.stage_union e _).mp hc
  have hm := (mem_stage_sentences S e s A).mpr hs
  refine ⟨s, {snapshot S e s}, by simp, ?_⟩
  exact proof_foldl_member {snapshot S e s} (stageSentences S e s) ⊤ A hm
    (.assumption (by simp [snapshot]))

theorem snapshot_same_derivability (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) (A : L.Sentence) :
    Derives (Set.range (snapshot S e)) A ↔ Derives T A := by
  constructor
  · intro h
    apply derives_through_axioms S (T := Set.range (snapshot S e)) (U := T) _ h
    rintro B ⟨s, rfl⟩
    exact snapshot_derivable S T e he s
  · intro h
    apply derives_through_axioms S (T := T) (U := Set.range (snapshot S e)) _ h
    intro B hB
    obtain ⟨s, hs⟩ := original_axiom_snapshot S T e he B hB
    apply derives_mono hs
    intro C hC
    have heq : C = snapshot S e s := Set.mem_singleton_iff.mp hC
    exact ⟨s, heq.symm⟩

theorem snapshot_same_closure (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T) :
    Theories.consequenceClosure (Set.range (snapshot S e)) = Theories.consequenceClosure T := by
  let := effective_symbols_countable S
  ext A
  rw [Theories.mem_closure_iff_derives, Theories.mem_closure_iff_derives,
    snapshot_same_derivability S T e he A]

theorem snapshot_same_models (T : L.Theory) (e : ℕ)
    (he : EffectiveEnumerations.indexSet e = codes S T)
    (M : Type*) [L.Structure M] [Nonempty M] :
    M ⊨ Set.range (snapshot S e) ↔ M ⊨ T := by
  rw [← Theories.model_closure (Set.range (snapshot S e)) M,
    snapshot_same_closure S T e he, Theories.model_closure T M]

end
end Lemmatheca.ComputabilityTheory.CraigReaxiomatization
