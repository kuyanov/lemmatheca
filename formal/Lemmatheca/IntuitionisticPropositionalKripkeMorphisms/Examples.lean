import Lemmatheca.IntuitionisticPropositionalKripkeMorphisms.Morphisms
import Lemmatheca.IntuitionisticKripkeSemantics.Examples

/-! The actual fork-to-chain map and both failure examples in the shared models. -/
namespace Lemmatheca.Entry.IntuitionisticPropositionalKripkeMorphisms

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic.Kripke
open Lemmatheca.Entry.IntuitionisticKripkeSemantics

universe u
variable {α : Type u}

local instance morphismForkNonempty : Nonempty ForkWorld := ⟨.root⟩

/-- Root maps to zero, and both leaves map to one. -/
def collapse : ForkWorld → Bool
  | .root => false
  | .left | .right => true

theorem collapse_bounded (p : α) :
    IsBoundedMorphism (forkModel p p) (chainModel p) collapse := by
  constructor
  · constructor
    · intro a b hab
      rcases hab with h | h
      · subst a
        cases b <;> decide
      · subst b
        exact le_rfl
    · intro a x hax
      cases a <;> cases x
      · exact ⟨.root, le_rfl, rfl⟩
      · exact ⟨.left, Or.inl rfl, rfl⟩
      · exact False.elim ((show ¬ ((true : Bool) ≤ false) by decide) hax)
      · exact ⟨.left, le_rfl, rfl⟩
      · exact False.elim ((show ¬ ((true : Bool) ≤ false) by decide) hax)
      · exact ⟨.right, le_rfl, rfl⟩
  · intro a q
    cases a <;> simp [collapse, forkModel, chainModel]

theorem collapse_surjective : Function.Surjective collapse := by
  intro x
  cases x
  · exact ⟨.root, rfl⟩
  · exact ⟨.left, rfl⟩

theorem collapse_not_injective : ¬ Function.Injective collapse := by
  intro h
  have heq : ForkWorld.left = .right := h rfl
  cases heq

/-- The literal constant function has forth and atoms, but fails back at the upper world. -/
theorem missing_back_conditions (p : α) :
    Monotone (fun _ : PUnit.{1} => (false : Bool)) ∧
      (∀ (a : PUnit.{1}) (q : α),
        (singleton.{u, 0} (fun _ : α => false)).valuation a q ↔ (chainModel p).valuation false q) ∧
      ¬ IsBoundedFrameMap (fun _ : PUnit.{1} => (false : Bool)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b _
    exact le_rfl
  · intro a q
    simp [Lemmatheca.ProofTheory.Intuitionistic.Kripke.singleton, chainModel]
  · intro h
    obtain ⟨b, _, hb⟩ := h.back PUnit.unit true (by decide)
    cases hb

/-- This is validity for all persistent valuations, not just the displayed chain model. -/
theorem chain_frame_weak_excluded_middle (p : α) :
    FrameValid Bool (.disj (.neg (.atom p)) (.neg (.neg (.atom p)))) := by
  classical
  intro M a
  by_cases hp : M.valuation true p
  · right
    intro z _ hn
    exact hn true (by cases z <;> decide) hp
  · left
    intro z _ hz
    exact hp (M.persistent (by cases z <;> decide) p hz)

/-- Only the left leaf verifies the specified atom. -/
def oneBranchFork (p : α) : Model α ForkWorld where
  world_nonempty := ⟨.root⟩
  valuation
    | .left, q => q = p
    | _, _ => False
  persistent {a b} h q hq := by
    rcases h with h | h
    · subst a
      exact hq.elim
    · subst b
      exact hq

theorem fork_frame_failure (p : α) :
    ¬ Forces (oneBranchFork p) .root (.neg (.atom p)) ∧
      Forces (oneBranchFork p) .right (.neg (.atom p)) ∧
      ¬ Forces (oneBranchFork p) .root (.neg (.neg (.atom p))) ∧
      ¬ FrameValid ForkWorld (.disj (.neg (.atom p)) (.neg (.neg (.atom p)))) := by
  have hn : ¬ Forces (oneBranchFork p) .root (.neg (.atom p)) := by
    intro h
    exact h .left (Or.inl rfl) rfl
  have hr : Forces (oneBranchFork p) .right (.neg (.atom p)) := by
    intro z hz hp
    rcases hz with h | h
    · cases h
    · subst z
      exact hp
  have hnn : ¬ Forces (oneBranchFork p) .root (.neg (.neg (.atom p))) := by
    intro h
    exact h .right (Or.inl rfl) hr
  refine ⟨hn, hr, hnn, ?_⟩
  intro h
  rcases h (oneBranchFork p) .root with h | h
  · exact hn h
  · exact hnn h

/-- No target model can supply this valuation through the actual collapse function. -/
theorem oneBranch_not_pullback (p : α) :
    ¬ ∃ N : Model α Bool, ∀ (a : ForkWorld) (q : α),
      (oneBranchFork p).valuation a q ↔ N.valuation (collapse a) q := by
  rintro ⟨N, h⟩
  have hleft : N.valuation true p := (h .left p).mp rfl
  have hright : (oneBranchFork p).valuation .right p := (h .right p).mpr hleft
  exact hright

end Lemmatheca.Entry.IntuitionisticPropositionalKripkeMorphisms
