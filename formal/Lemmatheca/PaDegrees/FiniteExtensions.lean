import Lemmatheca.PaDegrees.Basic
import Lemmatheca.ComputablyInseparableSets.NegativeSearch

set_option autoImplicit false

namespace Lemmatheca.ComputabilityTheory.PaDegrees

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ProofTheory
open ArithmeticTheories FirstOrderProofs CodingFormalProofs ArithmeticProofPredicates
open UniversalComputation TuringDegrees OracleComputation EffectivelyClosedClassesAndDnc
open ComputableSeparation

noncomputable section

def ValidSentenceList (L : ℕ) : Prop :=
  ∀ a ∈ Seq.decode L, isSentence arithmeticSignature a = true

def finiteTheory (L : ℕ) : language.Theory :=
  PA ∪ {A | sentenceCode arithmeticSignature A ∈ Seq.decode L}

def appendSentence (L a : ℕ) : ℕ := Seq.append L (Seq.code [a])

/-- Axiom certificates are tagged PA certificates or positions in the extra list. -/
def finiteAxiomCertificate (L a s : ℕ) : Bool :=
  isSentence arithmeticSignature a &&
    (if s.unpair.1 = 0 then paAxiomCertificate a s.unpair.2
    else if s.unpair.1 = 1 then
      decide (s.unpair.2 < Seq.length L) && decide (Seq.entry L s.unpair.2 = a)
    else false)

def badProof (L p : ℕ) : Bool :=
  certificateCheck arithmeticSignature (finiteAxiomCertificate L) p botCode

theorem append_sentence_primitive : Primrec₂ appendSentence := by
  unfold Primrec₂ appendSentence Seq.append
  fun_prop

theorem finite_axiom_certificate_primitive :
    Primrec (fun z : ℕ × (ℕ × ℕ) => finiteAxiomCertificate z.1 z.2.1 z.2.2) := by
  classical
  have hL : Primrec (fun z : ℕ × (ℕ × ℕ) => z.1) := Primrec.fst
  have ha : Primrec (fun z : ℕ × (ℕ × ℕ) => z.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun z : ℕ × (ℕ × ℕ) => z.2.2) := Primrec.snd.comp Primrec.snd
  have htag := Primrec.fst.comp (Primrec.unpair.comp hs)
  have hw := Primrec.snd.comp (Primrec.unpair.comp hs)
  have hvalid := (primrec_isSentence arithmeticSignature).comp ha
  have hPA := paAxiomCertificate_primitive.comp ha hw
  have hlist := (Primrec.dom_bool₂ Bool.and).comp
    (Primrec.nat_lt.comp hw (FiniteSequenceCoding.primrec_length.comp hL)).decide
    (Primrec.eq.comp (FiniteSequenceCoding.primrec_entry.comp hL hw) ha).decide
  exact (Primrec.dom_bool₂ Bool.and).comp hvalid
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hPA
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hlist (Primrec.const false)))

theorem finite_axiom_certificate_theory (L : ℕ) :
    theory arithmeticSignature (finiteAxiomCertificate L) = finiteTheory L := by
  classical
  ext A
  let a := sentenceCode arithmeticSignature A
  have hv : isSentence arithmeticSignature a = true :=
    (sentence_recognition_iff arithmeticSignature a).mpr ⟨A, rfl⟩
  change (∃ s, finiteAxiomCertificate L a s = true) ↔ A ∈ PA ∨ a ∈ Seq.decode L
  constructor
  · rintro ⟨s, hs⟩
    unfold finiteAxiomCertificate at hs
    simp only [hv, Bool.true_and] at hs
    split at hs
    · have hA : A ∈ theory arithmeticSignature paAxiomCertificate := ⟨s.unpair.2, hs⟩
      rw [paAxiomCertificate_theory] at hA
      exact Or.inl hA
    · split at hs
      · right
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
        have hi : s.unpair.2 < (Seq.decode L).length := hs.1
        have he : (Seq.decode L)[s.unpair.2] = a := by
          simpa only [Seq.entry, List.getElem?_eq_getElem hi, Option.getD_some] using hs.2
        exact he ▸ List.getElem_mem hi
      · simp at hs
  · rintro (hA | hA)
    · have hm : A ∈ theory arithmeticSignature paAxiomCertificate := by
        rw [paAxiomCertificate_theory]
        exact hA
      obtain ⟨s, hs⟩ := hm
      exact ⟨Nat.pair 0 s, by simp [finiteAxiomCertificate, hv, a, hs]⟩
    · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hA
      exact ⟨Nat.pair 1 i, by
        simp [finiteAxiomCertificate, hv, Seq.length, Seq.entry, hi, he]⟩

attribute [local irreducible] finiteAxiomCertificate

@[fun_prop] private theorem finite_axiom_comp {α : Type*} [Primcodable α]
    {L a s : α → ℕ} (hL : Primrec L) (ha : Primrec a) (hs : Primrec s) :
    Primrec (fun x => finiteAxiomCertificate (L x) (a x) (s x)) :=
  finite_axiom_certificate_primitive.comp (hL.pair (ha.pair hs))

/-- Joint dependence on the list parameter is retained through the entire proof scan. -/
theorem bad_proof_primitive : Primrec₂ badProof := by
  have hd : Primrec (fun z : ℕ × ℕ => (Seq.decode z.2)[0]?.getD 0) := by fun_prop
  have hw : Primrec (fun z : ℕ × ℕ => Seq.decode ((Seq.decode z.2)[1]?.getD 0)) := by fun_prop
  have hg : Primrec (fun z : ℕ × ℕ => Seq.decode (proofContext ((Seq.decode z.2)[0]?.getD 0))) := by
    unfold proofContext
    fun_prop
  have hcell : Primrec (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      isSentence arithmeticSignature z.2.1 && finiteAxiomCertificate z.1.1 z.2.1 z.2.2) := by
    fun_prop
  have hchecks : Primrec (fun z : ℕ × ℕ =>
      ((Seq.decode (proofContext ((Seq.decode z.2)[0]?.getD 0))).zip
        (Seq.decode ((Seq.decode z.2)[1]?.getD 0))).all
        (fun aw => isSentence arithmeticSignature aw.1 && finiteAxiomCertificate z.1 aw.1 aw.2)) :=
    PrimitiveRecursiveAutomation.listAll (PrimitiveRecursiveAutomation.listZip hg hw) hcell
  have hfirst : Primrec (fun z : ℕ × ℕ =>
      decide ((Seq.decode z.2).length = 2) && derivationCheck arithmeticSignature ((Seq.decode z.2)[0]?.getD 0) &&
      decide (proofConclusion ((Seq.decode z.2)[0]?.getD 0) = botCode) && isSentence arithmeticSignature botCode &&
      decide ((Seq.decode (proofContext ((Seq.decode z.2)[0]?.getD 0))).length =
        (Seq.decode ((Seq.decode z.2)[1]?.getD 0)).length)) := by
    unfold proofConclusion proofContext
    fun_prop
  exact (Primrec.dom_bool₂ Bool.and).comp hfirst hchecks

theorem bad_proof_correct (L : ℕ) :
    (∃ p, badProof L p = true) ↔ Derives (finiteTheory L) ⊥ := by
  change (∃ p, certificateCheck arithmeticSignature (finiteAxiomCertificate L) p
    (sentenceCode arithmeticSignature (⊥ : language.Sentence)) = true) ↔ _
  rw [certificate_iff_derives, finite_axiom_certificate_theory]

attribute [local irreducible] badProof

def positiveFailure (w p : ℕ) : Prop :=
  badProof (appendSentence w.unpair.1 w.unpair.2) p = true

def negativeFailure (w p : ℕ) : Prop :=
  badProof (appendSentence w.unpair.1 (negCode w.unpair.2)) p = true

def contradictionRace (w : ℕ) : Part ℕ := negativeRace positiveFailure negativeFailure w

theorem contradiction_race_partial : Nat.Partrec contradictionRace := by
  classical
  have hc : Primrec (fun p : ℕ × ℕ => p.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have ha : Primrec (fun p : ℕ × ℕ => p.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hneg : Primrec negCode := by unfold negCode impCode botCode; fun_prop
  apply negativeRace_partial
  · exact Primrec.eq.comp (bad_proof_primitive.comp
      (append_sentence_primitive.comp hc ha) Primrec.snd) (Primrec.const true)
  · exact Primrec.eq.comp (bad_proof_primitive.comp
      (append_sentence_primitive.comp hc (hneg.comp ha)) Primrec.snd) (Primrec.const true)

def ContradictionProgramIndex (v : ℕ) : Prop :=
  ∀ w z, phi v (Nat.pair w z) = contradictionRace w

theorem contradiction_program_index_exists : ∃ v, ContradictionProgramIndex v := by
  have hp : Partrec₂ (fun (w _z : ℕ) => contradictionRace w) :=
    (Partrec.nat_iff.mpr contradiction_race_partial).comp Computable.fst
  obtain ⟨v, hv⟩ := phi_complete (Partrec₂.unpaired'.mpr hp)
  exact ⟨v, fun w z => by
    simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hv (Nat.pair w z)⟩

def contradictionProgramIndex : ℕ := Classical.choose contradiction_program_index_exists

def contradictionIndex (L a : ℕ) : ℕ :=
  specialize contradictionProgramIndex (Nat.pair L a)

theorem contradiction_index_primitive : Primrec₂ contradictionIndex := by
  exact specialize_primitive.comp (Primrec.const contradictionProgramIndex)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd)

theorem contradiction_index_eval (L a z : ℕ) :
    phi (contradictionIndex L a) z = contradictionRace (Nat.pair L a) := by
  rw [contradictionIndex, specialize_eval]
  exact Classical.choose_spec contradiction_program_index_exists (Nat.pair L a) z

theorem contradiction_race_stage (L a p : ℕ)
    (hp : p ∈ raceStage positiveFailure negativeFailure (Nat.pair L a)) :
    contradictionRace (Nat.pair L a) = Part.some
      (if badProof (appendSentence L a) p = true then 0 else 1) := by
  simpa only [contradictionRace, positiveFailure, Nat.unpair_pair] using
    negativeRace_at_stage positiveFailure negativeFailure (Nat.pair L a) p hp

theorem contradiction_race_domain (L a : ℕ) :
    (contradictionRace (Nat.pair L a)).Dom ↔
      ¬ Consistent (finiteTheory (appendSentence L a)) ∨
      ¬ Consistent (finiteTheory (appendSentence L (negCode a))) := by
  rw [contradictionRace, negativeRace_domain]
  simp only [positiveFailure, negativeFailure, Nat.unpair_pair, bad_proof_correct,
    FirstOrderProofs.Consistent, not_not]

def signedChoice (a b : ℕ) : ℕ := if b = 0 then a else negCode a

theorem signed_choice_primitive : Primrec₂ signedChoice := by
  unfold Primrec₂ signedChoice negCode impCode botCode
  simp only [← Bool.cond_decide]
  fun_prop

private theorem finite_theory_append (L : ℕ) (A : language.Sentence) :
    finiteTheory (appendSentence L (sentenceCode arithmeticSignature A)) = insert A (finiteTheory L) := by
  classical
  ext B
  simp only [finiteTheory, Set.mem_union, Set.mem_ofPred_eq, appendSentence, Seq.append,
    FiniteSequenceCoding.decode_code, List.mem_append, List.mem_singleton,
    (sentence_code_injective arithmeticSignature).eq_iff, Set.mem_insert_iff]
  tauto

private theorem consistent_one_side (L : ℕ) (hL : Consistent (finiteTheory L))
    (A : language.Sentence) :
    Consistent (finiteTheory (appendSentence L (sentenceCode arithmeticSignature A))) ∨
      Consistent (finiteTheory (appendSentence L (negCode (sentenceCode arithmeticSignature A)))) := by
  classical
  by_cases hp : Consistent (finiteTheory (appendSentence L (sentenceCode arithmeticSignature A)))
  · exact Or.inl hp
  right
  have hbot : Derives (insert A (finiteTheory L)) ⊥ := by
    rw [← finite_theory_append]
    exact Classical.not_not.mp hp
  have hn : Derives (finiteTheory L) A.not := derives_imp_iff.mpr hbot
  rw [negation_code, finite_theory_append]
  intro hbad
  apply hL
  simpa only [Set.union_self] using derives_cut hn hbad

private theorem race_only_left (R S : ℕ → ℕ → Prop) (x : ℕ)
    (hex : ∃ k, R x k) (hno : ∀ k, ¬ S x k) : negativeRace R S x = Part.some 0 := by
  classical
  let k := Nat.find hex
  have hk : k ∈ raceStage R S x := (raceStage_spec R S x k).mpr
    ⟨Or.inl (Nat.find_spec hex), fun i hi => ⟨Nat.find_min hex hi, hno i⟩⟩
  have hr : R x k := Nat.find_spec hex
  simpa only [hr, ↓reduceIte] using negativeRace_at_stage R S x k hk

private theorem race_only_right (R S : ℕ → ℕ → Prop) (x : ℕ)
    (hno : ∀ k, ¬ R x k) (hex : ∃ k, S x k) : negativeRace R S x = Part.some 1 := by
  classical
  let k := Nat.find hex
  have hk : k ∈ raceStage R S x := (raceStage_spec R S x k).mpr
    ⟨Or.inr (Nat.find_spec hex), fun i hi => ⟨hno i, Nat.find_min hex hi⟩⟩
  simpa only [hno k, ↓reduceIte] using negativeRace_at_stage R S x k hk

theorem safe_choice (D : Set ℕ) (hD : D ∈ binaryDNCClass) (L : ℕ)
    (hL : Consistent (finiteTheory L)) (A : language.Sentence) :
    Consistent (finiteTheory (appendSentence L
      (signedChoice (sentenceCode arithmeticSignature A)
        (indicator (fun e => e ∈ D) (contradictionIndex L (sentenceCode arithmeticSignature A)))))) := by
  classical
  let a := sentenceCode arithmeticSignature A
  let q := contradictionIndex L a
  change Consistent (finiteTheory (appendSentence L
    (signedChoice a (indicator (fun e => e ∈ D) q))))
  by_cases hm : q ∈ D
  · simp only [indicator, hm, ↓reduceIte, signedChoice, Nat.one_ne_zero]
    by_contra hn
    have hp := (consistent_one_side L hL A).resolve_right hn
    have hno (k : ℕ) : ¬ positiveFailure (Nat.pair L a) k := by
      intro hk
      apply hp
      exact (bad_proof_correct _).mp ⟨k, by simpa only [positiveFailure, Nat.unpair_pair] using hk⟩
    have hex : ∃ k, negativeFailure (Nat.pair L a) k := by
      simpa only [negativeFailure, Nat.unpair_pair] using
        (bad_proof_correct _).mpr (Classical.not_not.mp hn)
    have hv := race_only_right positiveFailure negativeFailure (Nat.pair L a) hno hex
    have hrun : 1 ∈ phi q q := by
      rw [contradiction_index_eval]
      exact Part.eq_some_iff.mp hv
    exact hD q 1 hrun (by simp [indicator, hm])
  · simp only [indicator, hm, ↓reduceIte, signedChoice]
    by_contra hp
    have hn := (consistent_one_side L hL A).resolve_left hp
    have hex : ∃ k, positiveFailure (Nat.pair L a) k := by
      simpa only [positiveFailure, Nat.unpair_pair] using
        (bad_proof_correct _).mpr (Classical.not_not.mp hp)
    have hno (k : ℕ) : ¬ negativeFailure (Nat.pair L a) k := by
      intro hk
      apply hn
      exact (bad_proof_correct _).mp ⟨k, by simpa only [negativeFailure, Nat.unpair_pair] using hk⟩
    have hv := race_only_left positiveFailure negativeFailure (Nat.pair L a) hex hno
    have hrun : 0 ∈ phi q q := by
      rw [contradiction_index_eval]
      exact Part.eq_some_iff.mp hv
    exact hD q 0 hrun (by simp [indicator, hm])

end
end Lemmatheca.ComputabilityTheory.PaDegrees
