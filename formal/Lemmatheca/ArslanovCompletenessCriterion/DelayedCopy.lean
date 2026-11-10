import Lemmatheca.ArslanovCompletenessCriterion.Approximation
import Lemmatheca.UniformSelfReference.Uniform

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion

open UniversalComputation OracleComputation
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

def haltingSearch (n : ℕ) : Part ℕ :=
  Nat.rfind (fun s => Part.some (decide (LimitComputability.haltingTest s n = 1)))

def firstEntry (n : ℕ) (hn : n ∈ haltingDiagonal) : ℕ :=
  Nat.find (((LimitComputability.halting_stage_data).2.2.2.2.1 n).mp hn)

theorem first_entry_spec (n : ℕ) (hn : n ∈ haltingDiagonal) :
    n ∈ LimitComputability.haltingStage (firstEntry n hn) ∧
      ∀ s < firstEntry n hn, n ∉ LimitComputability.haltingStage s := by
  have hex : ∃ s, n ∈ LimitComputability.haltingStage s :=
    (LimitComputability.halting_stage_data.2.2.2.2.1 n).mp hn
  change n ∈ LimitComputability.haltingStage (Nat.find hex) ∧
    ∀ s < Nat.find hex, n ∉ LimitComputability.haltingStage s
  exact ⟨Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩

theorem halting_search_partial : Partrec haltingSearch := by
  have hp : Computable₂ (fun (n s : ℕ) => decide (LimitComputability.haltingTest s n = 1)) :=
    (Primrec.eq.decide.to_comp.comp
      (LimitComputability.halting_stage_data.1.to_comp.comp Computable.snd Computable.fst)
      (Computable.const 1)).to₂
  exact Partrec.rfind hp.partrec₂

theorem halting_search_eval (n : ℕ) (hn : n ∈ haltingDiagonal) :
    haltingSearch n = Part.some (firstEntry n hn) := by
  apply Part.eq_some_iff.mpr
  rw [haltingSearch, Nat.mem_rfind]
  refine ⟨?_, ?_⟩
  · have ht := (LimitComputability.halting_stage_data.2.2.1 _ _).mpr (first_entry_spec n hn).1
    simp [ht]
  · intro s hs
    have ht : LimitComputability.haltingTest s n ≠ 1 := fun h =>
      (first_entry_spec n hn).2 s hs ((LimitComputability.halting_stage_data.2.2.1 _ _).mp h)
    simp [ht]

theorem halting_search_none (n : ℕ) (hn : n ∉ haltingDiagonal) :
    haltingSearch n = Part.none := by
  apply Part.eq_none_iff.mpr
  intro v hv
  have hs := Nat.rfind_spec hv
  have ht : LimitComputability.haltingTest v n = 1 := by simpa using hs
  exact hn ((LimitComputability.halting_stage_data.2.2.2.2.1 n).mpr
    ⟨v, (LimitComputability.halting_stage_data.2.2.1 v n).mp ht⟩)

def delayedCopy (a e z n x : ℕ) : Part ℕ :=
  (haltingSearch n).bind (fun s => phi (approximation a e s z) x)

-- Input ((a,e),(z,(n,x))) retains both supplied indices.
def delayedInput (w : ℕ) : Part ℕ :=
  delayedCopy w.unpair.1.unpair.1 w.unpair.1.unpair.2 w.unpair.2.unpair.1
    w.unpair.2.unpair.2.unpair.1 w.unpair.2.unpair.2.unpair.2

theorem delayed_input_partial : Nat.Partrec delayedInput := by
  have hn : Computable (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp
      (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))))
  have hs : Partrec (fun w : ℕ => haltingSearch w.unpair.2.unpair.2.unpair.1) :=
    halting_search_partial.comp hn
  have hL : Computable (fun p : ℕ × ℕ => p.1.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.fst)
  have hR : Computable (fun p : ℕ × ℕ => p.1.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp Computable.fst)
  have ha : Computable (fun p : ℕ × ℕ => p.1.unpair.1.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp hL)
  have he : Computable (fun p : ℕ × ℕ => p.1.unpair.1.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp hL)
  have hz : Computable (fun p : ℕ × ℕ => p.1.unpair.2.unpair.1) :=
    Computable.fst.comp (Computable.unpair.comp hR)
  have hRR : Computable (fun p : ℕ × ℕ => p.1.unpair.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp hR)
  have hx : Computable (fun p : ℕ × ℕ => p.1.unpair.2.unpair.2.unpair.2) :=
    Computable.snd.comp (Computable.unpair.comp hRR)
  have harg : Computable (fun p : ℕ × ℕ =>
      ((p.1.unpair.1.unpair.1,p.1.unpair.1.unpair.2),(p.2,p.1.unpair.2.unpair.1))) :=
    (ha.pair he).pair (Computable.snd.pair hz)
  have hh := phi_recursive.comp (approximation_primitive.to_comp.comp harg) hx
  exact Partrec.nat_iff.mp (hs.bind hh.to₂)

def delayedMaster : ℕ := Classical.choose (phi_complete delayed_input_partial)

def copyFamilyIndex (a e : ℕ) : ℕ := specialize delayedMaster (Nat.pair a e)

theorem delayed_master_eval (a e z n x : ℕ) :
    phi delayedMaster (Nat.pair (Nat.pair a e) (Nat.pair z (Nat.pair n x))) =
      delayedCopy a e z n x := by
  simpa only [delayedMaster, delayedInput, Nat.unpair_pair] using
    congrFun (Classical.choose_spec (phi_complete delayed_input_partial))
      (Nat.pair (Nat.pair a e) (Nat.pair z (Nat.pair n x)))

theorem copy_family_eval (a e z n x : ℕ) :
    phi (copyFamilyIndex a e) (Nat.pair z (Nat.pair n x)) = delayedCopy a e z n x := by
  rw [copyFamilyIndex, specialize_eval, delayed_master_eval]

def copyAuxiliary (a e : ℕ) : ℕ :=
  Classical.choose (UniformSelfReference.specified_partial_family_selector
    (copyFamilyIndex a e) (copy_family_eval a e))

def copySelector (a e n : ℕ) : ℕ :=
  UniformSelfReference.selector (RecursionTheorem.selfSpecialize (copyAuxiliary a e)) n

theorem copy_selector_primitive (a e : ℕ) : Primrec (copySelector a e) := by
  exact (Classical.choose_spec (UniformSelfReference.specified_partial_family_selector
    (copyFamilyIndex a e) (copy_family_eval a e))).2.1

theorem copy_selector_eval (a e n x : ℕ) :
    phi (copySelector a e n) x = delayedCopy a e (copySelector a e n) n x := by
  exact (Classical.choose_spec (UniformSelfReference.specified_partial_family_selector
    (copyFamilyIndex a e) (copy_family_eval a e))).2.2 n x

theorem copy_index_eval (a e n : ℕ) (hn : n ∈ haltingDiagonal) (x : ℕ) :
    phi (copySelector a e n) x =
      phi (approximation a e (firstEntry n hn) (copySelector a e n)) x := by
  rw [copy_selector_eval, delayedCopy, halting_search_eval n hn, Part.bind_some]

theorem copy_index_empty (a e n : ℕ) (hn : n ∉ haltingDiagonal) :
    EffectiveEnumerations.indexSet (copySelector a e n) = ∅ := by
  ext x
  change (phi (copySelector a e n) x).Dom ↔ False
  rw [copy_selector_eval, delayedCopy, halting_search_none n hn, Part.bind_none]
  simp

theorem late_entry_fixed_point (A : Set ℕ) (a e : ℕ) (f : ℕ → ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (he : ∀ n, OracleProgramNumberings.phi A e n = Part.some (f n))
    (n : ℕ) (hn : n ∈ haltingDiagonal)
    (hle : modulus A a e ht (copySelector a e n) ≤ firstEntry n hn) :
    EffectiveEnumerations.indexSet (copySelector a e n) =
      EffectiveEnumerations.indexSet (f (copySelector a e n)) := by
  have hi := approximation_modulus A a e f ht ha he (copySelector a e n) (firstEntry n hn) hle
  ext x
  change (phi (copySelector a e n) x).Dom ↔ (phi (f (copySelector a e n)) x).Dom
  rw [copy_index_eval a e n hn x, hi]

theorem disagreement_entry_bound (A : Set ℕ) (a e : ℕ) (f : ℕ → ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (he : ∀ n, OracleProgramNumberings.phi A e n = Part.some (f n))
    (hdis : ∀ n (hn : n ∈ haltingDiagonal),
      approximation a e (firstEntry n hn) (copySelector a e n) ≠ f (copySelector a e n)) :
    ∀ n (hn : n ∈ haltingDiagonal), firstEntry n hn < modulus A a e ht (copySelector a e n) := by
  intro n hn
  by_contra h
  have hle : modulus A a e ht (copySelector a e n) ≤ firstEntry n hn := by omega
  exact hdis n hn (approximation_modulus A a e f ht ha he _ _ hle)

theorem fpf_entry_bound (A : Set ℕ) (a e : ℕ) (f : ℕ → ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (he : ∀ n, OracleProgramNumberings.phi A e n = Part.some (f n)) (hf : FPF f) :
    ∀ n (hn : n ∈ haltingDiagonal), firstEntry n hn < modulus A a e ht (copySelector a e n) := by
  intro n hn
  by_contra h
  have hle : modulus A a e ht (copySelector a e n) ≤ firstEntry n hn := by omega
  exact hf (copySelector a e n) (late_entry_fixed_point A a e f ht ha he n hn hle).symm

theorem entry_bound_decides (A : Set ℕ) (a e : ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (hb : ∀ n (hn : n ∈ haltingDiagonal), firstEntry n hn < modulus A a e ht (copySelector a e n))
    (n : ℕ) :
    n ∈ haltingDiagonal ↔
      n ∈ LimitComputability.haltingStage (modulus A a e ht (copySelector a e n)) := by
  constructor
  · intro hn
    exact LimitComputability.halting_stage_data.2.2.2.1 (Nat.le_of_lt (hb n hn))
      (first_entry_spec n hn).1
  · intro hs
    exact (LimitComputability.halting_stage_data.2.2.2.2.1 n).mpr ⟨_, hs⟩

def haltingDecisionInput (w : ℕ) : ℕ := LimitComputability.haltingTest w.unpair.2 w.unpair.1

theorem halting_decision_input_primitive : Primrec haltingDecisionInput := by
  exact LimitComputability.halting_stage_data.1.comp
    (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair)

def haltingDecisionCode (a e : ℕ) : Code :=
  .comp (embed (ordinaryProgram haltingDecisionInput halting_decision_input_primitive.to_comp))
    (.pair OracleProgramNumberings.identityCode
      (.comp (modulusCode a e)
        (embed (ordinaryProgram (copySelector a e) (copy_selector_primitive a e).to_comp))))

theorem halting_decision_eval (A : Set ℕ) (a e : ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (hb : ∀ n (hn : n ∈ haltingDiagonal), firstEntry n hn < modulus A a e ht (copySelector a e n))
    (n : ℕ) : eval A (haltingDecisionCode a e) n = Part.some (indicator haltingDiagonal n) := by
  have hh : eval A (embed (ordinaryProgram (copySelector a e)
      (copy_selector_primitive a e).to_comp)) n = Part.some (copySelector a e n) := by
    rw [eval_embed, BusyBeaverFunctions.ordinaryProgram_eval]
  have hm : eval A (.comp (modulusCode a e)
      (embed (ordinaryProgram (copySelector a e) (copy_selector_primitive a e).to_comp))) n =
      Part.some (modulus A a e ht (copySelector a e n)) := by
    change (eval A (embed (ordinaryProgram (copySelector a e)
      (copy_selector_primitive a e).to_comp)) n).bind _ = _
    rw [hh, Part.bind_some, modulus_code_eval A a e ht ha]
  have hp : eval A (.pair OracleProgramNumberings.identityCode
      (.comp (modulusCode a e)
        (embed (ordinaryProgram (copySelector a e) (copy_selector_primitive a e).to_comp)))) n =
      Part.some (Nat.pair n (modulus A a e ht (copySelector a e n))) := by
    change (eval A OracleProgramNumberings.identityCode n).bind _ = _
    rw [OracleProgramNumberings.identity_eval, Part.bind_some, hm, Part.map_some]
  change (eval A (.pair OracleProgramNumberings.identityCode
    (.comp (modulusCode a e)
      (embed (ordinaryProgram (copySelector a e) (copy_selector_primitive a e).to_comp)))) n).bind _ = _
  rw [hp, Part.bind_some, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval]
  simp only [haltingDecisionInput, Nat.unpair_pair]
  change Part.some (if n ∈ LimitComputability.haltingStage
    (modulus A a e ht (copySelector a e n)) then 1 else 0) =
    Part.some (if n ∈ haltingDiagonal then 1 else 0)
  simp only [← entry_bound_decides A a e ht hb n]

theorem fpf_halting_reduction (A : Set ℕ) (a e : ℕ) (f : ℕ → ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (he : ∀ n, OracleProgramNumberings.phi A e n = Part.some (f n)) (hf : FPF f) :
    TuringDegrees.Reduces (haltingDecisionCode a e) haltingDiagonal A := by
  intro n
  simpa only [Membership.mem, Set.Mem] using
    halting_decision_eval A a e ht ha (fpf_entry_bound A a e f ht ha he hf) n

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
