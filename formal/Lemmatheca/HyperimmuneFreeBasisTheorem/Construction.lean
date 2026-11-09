import Lemmatheca.HyperimmuneFreeBasisTheorem.OutputBound

set_option autoImplicit false
namespace Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
open ComputableTreesAndPaths IncomparableTuringDegrees UniversalComputation
open LowBasisTheorem HyperimmuneDegrees PaDegrees
noncomputable section
local instance hfbConstructionPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The supplied decider is run on the very same word, then finite tests are added. -/
def restrictedDecision (t l u : ℕ) : Part ℕ :=
  (phi t u).map fun b => if b = 1 ∧
    ∀ j ∈ FiniteSequenceCoding.decode l, certificateValue u j j = 0 then 1 else 0

theorem restricted_decision_partial :
    Nat.Partrec (fun z => restrictedDecision z.unpair.1.unpair.1
      z.unpair.1.unpair.2 z.unpair.2) := by
  have hzero : PrimrecRel (fun j u : ℕ => certificateValue u j j = 0) :=
    Primrec.eq.comp
      (certificate_primitive.comp ((Primrec.snd.pair Primrec.fst).pair Primrec.fst))
      (Primrec.const 0)
  have hall : PrimrecPred (fun p : ℕ × ℕ =>
      ∀ j ∈ FiniteSequenceCoding.decode p.1, certificateValue p.2 j j = 0) :=
    hzero.forall_mem_list.comp ((Primrec.ofNat (List ℕ)).comp Primrec.fst) Primrec.snd
  have ht : Primrec (fun z : ℕ => z.unpair.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hl : Primrec (fun z : ℕ => z.unpair.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hu : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hp : Partrec (fun z : ℕ => phi z.unpair.1.unpair.1 z.unpair.2) :=
    phi_recursive.comp ht.to_comp hu.to_comp
  have htest : PrimrecPred (fun p : ℕ × ℕ => p.2 = 1 ∧
      ∀ j ∈ FiniteSequenceCoding.decode p.1.unpair.1.unpair.2,
        certificateValue p.1.unpair.2 j j = 0) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 1)).and
      (hall.comp ((hl.comp Primrec.fst).pair (hu.comp Primrec.fst)))
  have hout : Computable₂ (fun z b : ℕ => if b = 1 ∧
      ∀ j ∈ FiniteSequenceCoding.decode z.unpair.1.unpair.2,
        certificateValue z.unpair.2 j j = 0 then (1 : ℕ) else 0) :=
    (Primrec.ite htest (Primrec.const 1) (Primrec.const 0)).to_comp.to₂
  exact Partrec.nat_iff.mp (hp.map hout)

theorem restriction_master_exists :
    ∃ r, ∀ t l u, phi r (Nat.pair (Nat.pair t l) u) = restrictedDecision t l u := by
  obtain ⟨r, hr⟩ := phi_complete restricted_decision_partial
  refine ⟨r, fun t l u => ?_⟩
  have h := congrFun hr (Nat.pair (Nat.pair t l) u)
  simpa only [Nat.unpair_pair] using h

def restrictionMaster : ℕ := Classical.choose restriction_master_exists

def restrictedIndex (t l : ℕ) : ℕ := specialize restrictionMaster (Nat.pair t l)

theorem restricted_index_primitive : Primrec₂ restrictedIndex := by
  exact (specialize_primitive.comp (Primrec.const restrictionMaster) Primrec₂.natPair).to₂

theorem restricted_index_eval (t l u : ℕ) :
    phi (restrictedIndex t l) u = restrictedDecision t l u := by
  rw [restrictedIndex, specialize_eval]
  exact Classical.choose_spec restriction_master_exists t l u

theorem restricted_index_decides (T : Set ℕ) (t : ℕ) (ht : TreeDeciderIndex t T) (l : ℕ) :
    TreeDeciderIndex (restrictedIndex t l) (restricted T l) := by
  intro u
  rw [restricted_index_eval, restrictedDecision, ht u, Part.map_some]
  apply congrArg Part.some
  by_cases hu : u ∈ T <;>
    simp [indicator, restricted, hu]

def HasDivergenceExtension (T : Set ℕ) (l e : ℕ) : Prop :=
  ∃ x, ∃ A, Path (restricted T (FiniteSequenceCoding.cons (TuringJump.freeze e x) l)) A

def selectedInput (T : Set ℕ) (l e : ℕ) : ℕ :=
  if h : HasDivergenceExtension T l e then Nat.find h else 0

def restrictionHistory (T : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => let l := restrictionHistory T e
      if HasDivergenceExtension T l e then
        FiniteSequenceCoding.cons (TuringJump.freeze e (selectedInput T l e)) l else l

def stageTree (T : Set ℕ) (e : ℕ) : Set ℕ := restricted T (restrictionHistory T e)

theorem selected_input_spec (T : Set ℕ) (l e : ℕ) (h : HasDivergenceExtension T l e) :
    (∃ A, Path (restricted T (FiniteSequenceCoding.cons
      (TuringJump.freeze e (selectedInput T l e)) l)) A) ∧
    ∀ x < selectedInput T l e, ¬ ∃ A,
      Path (restricted T (FiniteSequenceCoding.cons (TuringJump.freeze e x) l)) A := by
  simp only [selectedInput, dite_eq_left h]
  exact ⟨Nat.find_spec h, fun x hx => Nat.find_min h hx⟩

theorem restriction_addition (T : Set ℕ) (l e x : ℕ) :
    restricted T (FiniteSequenceCoding.cons (TuringJump.freeze e x) l) =
      divergenceTree (restricted T l) e x := by
  have hd : FiniteSequenceCoding.decode (FiniteSequenceCoding.cons (TuringJump.freeze e x) l) =
      TuringJump.freeze e x :: FiniteSequenceCoding.decode l := by
    rw [← FiniteSequenceCoding.code_decode l, ← FiniteSequenceCoding.code_cons,
      FiniteSequenceCoding.decode_code, FiniteSequenceCoding.decode_code]
  ext u
  simp [divergenceTree, restricted, hd, and_left_comm, and_comm]

theorem history_survival (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hne : ∃ A, Path T A) :
    (∀ e, IsBinaryTree (stageTree T e) ∧
      ComputablePred (fun u => u ∈ stageTree T e) ∧ ∃ A, Path (stageTree T e) A) ∧
    ∀ e, stageTree T (e + 1) ⊆ stageTree T e := by
  have hn : ∀ e, stageTree T (e + 1) ⊆ stageTree T e := by
    intro e
    by_cases h : HasDivergenceExtension T (restrictionHistory T e) e
    · simp only [stageTree, restrictionHistory, h, ↓reduceIte]
      exact (restricted_subsets T _ _).1
    · simp only [stageTree, restrictionHistory, h, ↓reduceIte]
      exact Set.Subset.refl _
  have hpaths : ∀ e, ∃ A, Path (stageTree T e) A := by
    intro e
    induction e with
    | zero => simpa only [stageTree, restrictionHistory, restricted_zero] using hne
    | succ e ih =>
      by_cases h : HasDivergenceExtension T (restrictionHistory T e) e
      · simpa only [stageTree, restrictionHistory, h, ↓reduceIte] using
          (selected_input_spec T (restrictionHistory T e) e h).1
      · simpa only [stageTree, restrictionHistory, h, ↓reduceIte] using ih
  refine ⟨fun e => ⟨restricted_tree T hT _, ?_, hpaths e⟩, hn⟩
  exact (((restricted_computable T hc).decide.comp
    ((Computable.const (restrictionHistory T e)).pair Computable.id)).computablePred).of_eq
      (fun u => by simp [stageTree])

theorem stage_alternatives (T : Set ℕ) (hT : IsBinaryTree T)
    (t : ℕ) (ht : TreeDeciderIndex t T) (e : ℕ) :
    (HasDivergenceExtension T (restrictionHistory T e) e ∧
      stageTree T (e + 1) = divergenceTree (stageTree T e) e
        (selectedInput T (restrictionHistory T e) e) ∧
      ∀ A, Path (stageTree T (e + 1)) A →
        ¬ (OracleProgramNumberings.phi A e (selectedInput T (restrictionHistory T e) e)).Dom) ∨
    (¬ HasDivergenceExtension T (restrictionHistory T e) e ∧
      stageTree T (e + 1) = stageTree T e ∧
      ClassBound (stageTree T e) (restrictedIndex t (restrictionHistory T e)) e) := by
  by_cases h : HasDivergenceExtension T (restrictionHistory T e) e
  · left
    have he : stageTree T (e + 1) = divergenceTree (stageTree T e) e
        (selectedInput T (restrictionHistory T e) e) := by
      simp only [stageTree, restrictionHistory, h, ↓reduceIte]
      exact restriction_addition T _ _ _
    refine ⟨h, he, fun A hA => ?_⟩
    rw [he] at hA
    exact (divergence_paths _ _ _ _).mp hA |>.2
  · right
    refine ⟨h, ?_, uniform_output_bound (stageTree T e) (restricted_tree T hT _)
      (restrictedIndex t (restrictionHistory T e)) (restricted_index_decides T t ht _) e ?_⟩
    · simp only [stageTree, restrictionHistory, h, ↓reduceIte]
    · intro A hA x
      by_contra hd
      apply h
      refine ⟨x, A, ?_⟩
      rw [restriction_addition]
      exact (divergence_paths _ _ _ _).mpr ⟨hA, hd⟩

theorem common_path (T : Set ℕ) (hT : IsBinaryTree T)
    (hc : ComputablePred (fun u => u ∈ T)) (hne : ∃ A, Path T A) :
    ∃ A, ∀ e, Path (stageTree T e) A := by
  obtain ⟨hs, hn⟩ := history_survival T hT hc hne
  exact (nested_levels (stageTree T) (fun e => (hs e).1) hn
    (fun e => (all_levels_path _ (hs e).1).mpr (hs e).2.2)).2.2

end
end Lemmatheca.ComputabilityTheory.HyperimmuneFreeBasisTheorem
