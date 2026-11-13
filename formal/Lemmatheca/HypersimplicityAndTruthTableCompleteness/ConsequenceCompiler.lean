import Lemmatheca.HypersimplicityAndTruthTableCompleteness.TruthTableFormulas
import Lemmatheca.ProductiveAndCreativeSets.Productivity

namespace Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.PropositionalCompactness
open UniversalComputation EffectiveEnumerations

/-- The original shared formula theory of positive membership facts. -/
def positiveTheory (A : Set ℕ) : Theory ℕ := PropFormula.atom '' A

def codeTheory (premises : List ℕ) : Theory ℕ := readFormula '' {c | c ∈ premises}

def positiveConsequence (A : Set ℕ) (premises : List ℕ) (conclusion : ℕ) : Prop :=
  TheoryEntails (positiveTheory A ∪ codeTheory premises) (readFormula conclusion)

noncomputable def stageFacts (a s : ℕ) : List ℕ :=
  (List.range s).filter (fun i => stageTest a s i == 1)

noncomputable def consequenceRecognizer (theta : ℕ → ℕ) (a prefixCodeInput e : ℕ) : Part ℕ :=
  (Nat.rfind (fun s => Part.some
    (finiteConsequenceTest (stageFacts a s) (FiniteSequenceCoding.decode prefixCodeInput) (theta e)))).map
      (fun _ => 0)

def ConsequenceRecognizerIndex (theta : ℕ → ℕ) (a v : ℕ) : Prop :=
  ∀ prefixCodeInput e, phi v (Nat.pair prefixCodeInput e) = consequenceRecognizer theta a prefixCodeInput e

def consequenceCompiler (v prefixCodeInput : ℕ) : ℕ := specialize v prefixCodeInput

private theorem stage_facts_primitive (a : ℕ) : Primrec (stageFacts a) := by
  classical
  have ht : PrimrecPred (fun p : ℕ × ℕ => stageTest a p.1 p.2 = 1) :=
    Primrec.eq.comp (stage_test_primitive.comp
      (((Primrec.const a).pair Primrec.fst).pair Primrec.snd)) (Primrec.const 1)
  have hf := Primrec.listFilterMap Primrec.list_range
    (Primrec.ite ht (Primrec.option_some_iff.mpr Primrec.snd) (Primrec.const none)).to₂
  apply hf.of_eq
  intro s
  simp only [stageFacts, ← List.filterMap_eq_filter]
  congr 1
  funext i
  simp only [Option.guard, beq_iff_eq]

private theorem stage_facts_mem (a s i : ℕ) : i ∈ stageFacts a s ↔ i ∈ stage a s := by
  simp only [stageFacts, List.mem_filter, List.mem_range, beq_iff_eq,
    (stage_test_spec a s i).2]
  exact and_iff_right_of_imp (fun h => h.1)

private theorem models_codes (v : Valuation ℕ) (A : Set ℕ) (premises : List ℕ) :
    ModelsTheory v (positiveTheory A ∪ codeTheory premises) ↔
      (∀ i ∈ A, v i = true) ∧ ∀ c ∈ premises, Satisfies v (readFormula c) := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (.atom i) (Or.inl ⟨i, hi, rfl⟩)
    · intro c hc
      exact h (readFormula c) (Or.inr ⟨c, hc, rfl⟩)
  · rintro ⟨ha, hp⟩ φ (hφ | hφ)
    · obtain ⟨i, hi, rfl⟩ := hφ
      exact ha i hi
    · obtain ⟨c, hc, rfl⟩ := hφ
      exact hp c hc

private theorem finite_stage_consequence (a : ℕ) (premises : List ℕ) (conclusion : ℕ)
    (h : positiveConsequence (indexSet a) premises conclusion) :
    ∃ s, TheoryEntails (positiveTheory (stage a s) ∪ codeTheory premises) (readFormula conclusion) := by
  classical
  obtain ⟨Δ, hΔ, hent⟩ := (finite_semantic_support _ _).mp h
  have hcover : ∃ s, ∀ φ ∈ Δ, φ ∈ positiveTheory (stage a s) ∪ codeTheory premises := by
    clear hent
    revert hΔ
    induction Δ using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert φ Δ hnot ih =>
      intro hΔ
      obtain ⟨s, hs⟩ := ih (fun ψ hψ => hΔ (Finset.mem_insert_of_mem hψ))
      rcases hΔ (Finset.mem_insert_self _ _) with hφ | hφ
      · obtain ⟨i, hi, rfl⟩ := hφ
        obtain ⟨t, ht⟩ := (stage_union a i).mp hi
        refine ⟨max s t, ?_⟩
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact Or.inl ⟨i, stage_monotone a (le_max_right s t) ht, rfl⟩
        · rcases hs ψ hψ with hpos | hcode
          · obtain ⟨j, hj, rfl⟩ := hpos
            exact Or.inl ⟨j, stage_monotone a (le_max_left s t) hj, rfl⟩
          · exact Or.inr hcode
      · refine ⟨s, ?_⟩
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact Or.inr hφ
        · exact hs ψ hψ
  obtain ⟨s, hs⟩ := hcover
  exact ⟨s, fun v hv => hent v (fun φ hφ => hv φ (hs φ hφ))⟩

attribute [local irreducible] finiteConsequenceTest

theorem consequence_recognizer_partial (theta : ℕ → ℕ) (htheta : Computable theta) (a : ℕ) :
    Partrec₂ (consequenceRecognizer theta a) := by
  have hf : Computable (fun p : (ℕ × ℕ) × ℕ => stageFacts a p.2) :=
    (stage_facts_primitive a).to_comp.comp Computable.snd
  have hp : Computable (fun p : (ℕ × ℕ) × ℕ => FiniteSequenceCoding.decode p.1.1) :=
    (Primrec.ofNat (List ℕ)).to_comp.comp (Computable.fst.comp Computable.fst)
  have hc : Computable (fun p : (ℕ × ℕ) × ℕ => theta p.1.2) :=
    htheta.comp (Computable.snd.comp Computable.fst)
  have hinput : Computable (fun p : (ℕ × ℕ) × ℕ =>
      ((stageFacts a p.2, FiniteSequenceCoding.decode p.1.1), theta p.1.2)) :=
    (hf.pair hp).pair hc
  have htest : Computable (fun p : (ℕ × ℕ) × ℕ =>
      finiteConsequenceTest (stageFacts a p.2) (FiniteSequenceCoding.decode p.1.1) (theta p.1.2)) :=
    finite_consequence_primitive.to_comp.comp hinput
  have htest2 : Partrec₂ (fun (p : ℕ × ℕ) (s : ℕ) => Part.some
      (finiteConsequenceTest (stageFacts a s) (FiniteSequenceCoding.decode p.1) (theta p.2))) :=
    htest.partrec.to₂
  have hsearch : Partrec (fun p : ℕ × ℕ => Nat.rfind (fun s => Part.some
      (finiteConsequenceTest (stageFacts a s) (FiniteSequenceCoding.decode p.1) (theta p.2)))) :=
    Partrec.rfind htest2
  have hzero : Computable₂ (fun (_p : ℕ × ℕ) (_s : ℕ) => (0 : ℕ)) := (Computable.const 0).to₂
  exact (hsearch.map hzero).to₂

theorem consequence_recognizer_domain (theta : ℕ → ℕ)
    (htheta : ∀ e, validCode (theta e) = true) (a : ℕ) (premises : List ℕ)
    (hp : ∀ c ∈ premises, validCode c = true) (e : ℕ) :
    (consequenceRecognizer theta a (FiniteSequenceCoding.code premises) e).Dom ↔
      positiveConsequence (indexSet a) premises (theta e) := by
  change (Nat.rfind (fun s => Part.some
    (finiteConsequenceTest (stageFacts a s) (FiniteSequenceCoding.decode (FiniteSequenceCoding.code premises))
      (theta e)))).Dom ↔ _
  rw [FiniteSequenceCoding.decode_code]
  have hsearch : (Nat.rfind (fun s => Part.some
      (finiteConsequenceTest (stageFacts a s) premises (theta e)))).Dom ↔
      ∃ s, finiteConsequenceTest (stageFacts a s) premises (theta e) = true := by
    constructor
    · intro hd
      obtain ⟨s, hs, _⟩ := Nat.rfind_dom.mp hd
      exact ⟨s, by simpa using hs⟩
    · rintro ⟨s, hs⟩
      exact Nat.rfind_dom.mpr ⟨s, by simpa using hs, fun _ => trivial⟩
  rw [hsearch]
  constructor
  · rintro ⟨s, hs⟩ v hv
    obtain ⟨ha, hl⟩ := (models_codes v (indexSet a) premises).mp hv
    apply (finite_consequence_correct _ _ _ hp (htheta e)).mp hs v
    · intro i hi
      exact ha i ((stage_union a i).mpr ⟨s, (stage_facts_mem a s i).mp hi⟩)
    · exact hl
  · intro h
    obtain ⟨s, hs⟩ := finite_stage_consequence a premises (theta e) h
    refine ⟨s, (finite_consequence_correct _ _ _ hp (htheta e)).mpr ?_⟩
    intro v ha hl
    apply hs v
    apply (models_codes v (stage a s) premises).mpr
    exact ⟨fun i hi => ha i ((stage_facts_mem a s i).mpr hi), hl⟩

theorem consequence_recognizer_index (theta : ℕ → ℕ) (htheta : Computable theta) (a : ℕ) :
    ∃ v, ConsequenceRecognizerIndex theta a v := by
  have hjoint : Nat.Partrec (fun z : ℕ => consequenceRecognizer theta a z.unpair.1 z.unpair.2) :=
    Partrec.nat_iff.mp ((consequence_recognizer_partial theta htheta a).comp
      (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair))
  obtain ⟨v, hv⟩ := phi_complete hjoint
  refine ⟨v, fun l e => ?_⟩
  simpa only [Nat.unpair_pair] using congrFun hv (Nat.pair l e)

theorem consequence_compiler_primitive (v : ℕ) : Primrec (consequenceCompiler v) := by
  exact specialize_primitive.comp (Primrec.const v) Primrec.id

theorem consequence_compiler_domain (theta : ℕ → ℕ)
    (htheta : ∀ e, validCode (theta e) = true) (a v : ℕ)
    (hv : ConsequenceRecognizerIndex theta a v) (premises : List ℕ)
    (hp : ∀ c ∈ premises, validCode c = true) :
    indexSet (consequenceCompiler v (FiniteSequenceCoding.code premises)) =
      {e | positiveConsequence (indexSet a) premises (theta e)} := by
  ext e
  change (phi (specialize v (FiniteSequenceCoding.code premises)) e).Dom ↔ _
  rw [specialize_eval, hv]
  exact consequence_recognizer_domain theta htheta a premises hp e
end Lemmatheca.ComputabilityTheory.HypersimplicityAndTruthTableCompleteness
