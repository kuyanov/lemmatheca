import Lemmatheca.PropositionalWeakExcludedMiddle.Frames
import Lemmatheca.PropositionalWeakExcludedMiddle.Inference
import Lemmatheca.IntuitionisticPropositionalKripkeMorphisms.Examples

/-! All formulas, fixed matching models, and the strictness counterexamples. -/
namespace Lemmatheca.Entry.PropositionalWeakExcludedMiddle
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.ProofTheory.Intuitionistic
open Extensions WeakExcludedMiddle Kripke
open Lemmatheca.Entry.IntuitionisticKripkeSemantics
open Lemmatheca.Entry.IntuitionisticPropositionalKripkeMorphisms

local instance wemExamplesForkNonempty : Nonempty ForkWorld := ⟨.root⟩

theorem chain_schema_valid (A : PropFormula ℕ) : FrameValid Bool (wem A) := by
  have hr : ∀ w : Bool, false ≤ w := by intro w; cases w <;> decide
  have ht : ∃ t : Bool, ∀ w : Bool, w ≤ t := by
    exact ⟨true, fun w => by cases w <;> decide⟩
  exact (finite_rooted_wem_iff_greatest false hr).mpr ht A

theorem not_intuitionistic_wem :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives ∅ (wem (.atom (0 : ℕ))) := by
  intro h
  apply (fork_frame_failure (0 : ℕ)).2.2.2
  intro M w
  exact sound h M w (by intro B hB; exact hB.elim)

theorem not_kc_excluded_middle :
    ¬ SchemaConsequence axioms ∅ (.disj (.atom (0 : ℕ)) (.neg (.atom 0))) := by
  intro h
  apply chain_not_excluded_middle (0 : ℕ)
  have hS : ∀ B ∈ (axioms : Set (PropFormula ℕ)), FrameValid Bool B := by
    intro B hB
    obtain ⟨A, rfl⟩ := hB
    exact chain_schema_valid A
  exact schemaConsequence_sound axioms ∅ _ hS h (chainModel 0) false
    (by intro B hB; exact hB.elim)

theorem natural_directed_no_greatest :
    DirectedFutureCones ℕ ∧ ¬ ∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  constructor
  · intro _ u v _ _
    exact ⟨max u v, le_max_left u v, le_max_right u v⟩
  · rintro ⟨n, hn⟩
    exact Nat.not_succ_le_self n (hn (n + 1))

theorem natural_schema_valid (A : PropFormula ℕ) : FrameValid ℕ (wem A) := by
  exact frame_wem_iff_directed.mpr natural_directed_no_greatest.1 A

theorem matching_fork_schema_truth (p : ℕ) (A : PropFormula ℕ) :
    ∀ w : ForkWorld, Forces (forkModel p p) w (wem A) := by
  exact boundedMorphism_all_worlds_preimage (forkModel p p) (chainModel p) collapse
    (collapse_bounded p) (wem A) (chain_schema_valid A (chainModel p))

theorem fork_not_directed : ¬ DirectedFutureCones ForkWorld := by
  intro h
  obtain ⟨z, hl, hr⟩ := h .root .left .right (Or.inl rfl) (Or.inl rfl)
  rcases hl with hbad | hl
  · cases hbad
  rcases hr with hbad | hr
  · cases hbad
  cases hl.trans hr.symm

end Lemmatheca.Entry.PropositionalWeakExcludedMiddle
