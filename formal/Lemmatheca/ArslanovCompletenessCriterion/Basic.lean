import Lemmatheca.DominationAndHyperimmuneDegrees.HyperimmuneFree
import Lemmatheca.ArithmeticDefinability.Selection
import Lemmatheca.RiceShapiroTheorem.Fragments
import Lemmatheca.BusyBeaverFunctions.FunctionOracles
import Lemmatheca.TuringJump.Recoding

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion

open UniversalComputation OracleComputation
open RiceShapiroTheorem
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section

def FPF (f : ℕ → ℕ) : Prop :=
  ∀ i, EffectiveEnumerations.indexSet (f i) ≠ EffectiveEnumerations.indexSet i

def ComputesFPF (A : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, PartialComputable A (fun n => Part.some (f n)) ∧ FPF f

theorem not_computable_fpf (f : ℕ → ℕ) (hf : Computable f) : ¬ FPF f := by
  intro h
  obtain ⟨i, hi⟩ := RecursionTheorem.transformer_fixed_point hf
  apply h i
  ext x
  change (phi (f i) x).Dom ↔ (phi i x).Dom
  rw [hi x]

def singletonIndex (v : ℕ) : ℕ := fragmentIndex (pairListCode [(v,0)])

theorem singleton_index_primitive : Primrec singletonIndex := by
  apply fragmentIndex_primitive.comp
  exact (Primrec.encode.comp (Primrec.list_cons.comp
    (Primrec₂.natPair.comp Primrec.id (Primrec.const 0)) (Primrec.const []))).of_eq
      (fun _ => rfl)

theorem singleton_index_domain (v : ℕ) :
    EffectiveEnumerations.indexSet (singletonIndex v) = {v} := by
  ext x
  change (phi (singletonIndex v) x).Dom ↔ x = v
  rw [singletonIndex, fragmentIndex_eval]
  by_cases h : x = v <;> simp [fragment, pairList_code, tableFunction, Part.ofOption, h]

def haltingFPF (i : ℕ) : ℕ := by
  classical
  exact if TuringJump.ordinaryFreeze i 0 ∈ haltingDiagonal
    then fragmentIndex (pairListCode []) else singletonIndex 0

def haltingQueryInput (i : ℕ) : ℕ := TuringJump.ordinaryFreeze i 0

theorem halting_query_input_primitive : Primrec haltingQueryInput := by
  exact TuringJump.ordinary_freeze_primitive.comp Primrec.id (Primrec.const 0)

def haltingBranch (b : ℕ) : ℕ :=
  if b = 1 then fragmentIndex (pairListCode []) else singletonIndex 0

theorem halting_branch_primitive : Primrec haltingBranch := by
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1))
    (Primrec.const _) (Primrec.const _)

def haltingFPFCode : Code :=
  .comp (embed (ordinaryProgram haltingBranch halting_branch_primitive.to_comp))
    (.comp .query (embed (ordinaryProgram haltingQueryInput halting_query_input_primitive.to_comp)))

theorem halting_fpf_eval (i : ℕ) :
    eval haltingDiagonal haltingFPFCode i = Part.some (haltingFPF i) := by
  simp only [haltingFPFCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
    Part.bind_some]
  by_cases h : TuringJump.ordinaryFreeze i 0 ∈ haltingDiagonal <;>
    simp [haltingBranch, haltingQueryInput, haltingFPF, indicator, h]

theorem halting_fpf : FPF haltingFPF := by
  intro i heq
  have hz : TuringJump.ordinaryFreeze i 0 ∈ haltingDiagonal ↔
      0 ∈ EffectiveEnumerations.indexSet i := by
    change (phi (TuringJump.ordinaryFreeze i 0) (TuringJump.ordinaryFreeze i 0)).Dom ↔
      (phi i 0).Dom
    rw [TuringJump.ordinary_freeze_eval]
  have he := Set.ext_iff.mp heq 0
  by_cases h : TuringJump.ordinaryFreeze i 0 ∈ haltingDiagonal
  · have hi := hz.mp h
    have hn : 0 ∉ EffectiveEnumerations.indexSet (haltingFPF i) := by
      change ¬ (phi (haltingFPF i) 0).Dom
      simp [haltingFPF, h, fragmentIndex_eval, empty_fragment.2, RicesTheorem.bottom]
    exact hn (he.mpr hi)
  · have hi : 0 ∉ EffectiveEnumerations.indexSet i := fun hi => h (hz.mpr hi)
    have hn : 0 ∈ EffectiveEnumerations.indexSet (haltingFPF i) := by
      simp [haltingFPF, h, singleton_index_domain]
    exact hi (he.mp hn)

theorem halting_fpf_substitution (A : Set ℕ) (c : Code)
    (hc : TuringDegrees.Reduces c haltingDiagonal A) (i : ℕ) :
    eval A (subst c haltingFPFCode) i = Part.some (haltingFPF i) := by
  rw [subst_eval haltingDiagonal A c hc, halting_fpf_eval]

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
