import Lemmatheca.IntuitionisticPropositionalDisjunctionProperty.Properties

namespace Lemmatheca.Entry.IntuitionisticPropositionalDisjunctionProperty

open Lemmatheca.MathematicalLogic.Propositional.PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open DisjunctionProperty

/-- Disjunction choice fails with an ordinary disjunctive open assumption. -/
theorem ordinary_assumptions :
    Derives {disj (atom 0) (atom 1)} (disj (atom 0) (atom 1)) ∧
      ¬ Derives {disj (atom 0) (atom 1)} (atom 0) ∧
      ¬ Derives {disj (atom 0) (atom 1)} (atom 1) := by
  refine ⟨.assumption (by simp), ?_, ?_⟩
  · intro h
    have hf : false = true := boolean_sound h (fun n => decide (n = 1)) (by
      intro B hB
      rcases hB with rfl
      decide)
    cases hf
  · intro h
    have hf : false = true := boolean_sound h (fun n => decide (n = 0)) (by
      intro B hB
      rcases hB with rfl
      decide)
    cases hf


/-- The exact four worlds of the counterexample: root, q leaf, r leaf, and p leaf. -/
inductive ForkWorld
  | root | u | v | t
  deriving DecidableEq

/-- Root-to-leaf reachability and reflexivity, with no further comparisons. -/
def forkLE (x y : ForkWorld) : Prop := x = .root ∨ x = y

instance forkPreorder : Preorder ForkWorld where
  le := forkLE
  le_refl _ := Or.inr rfl
  le_trans _ _ _ hxy hyz := by
    rcases hxy with h | h
    · exact Or.inl h
    · subst_vars
      exact hyz

/-- Every unnamed atom is false, and each leaf verifies only its indicated atom. -/
def threeLeafModel : Kripke.Model ℕ ForkWorld where
  world_nonempty := ⟨.root⟩
  valuation
    | .root, _ => False
    | .u, p => p = 1
    | .v, p => p = 2
    | .t, p => p = 0
  persistent {x y} h p hp := by
    rcases h with h | h
    · subst x
      exact hp.elim
    · subst y
      exact hp

/-- The future-world negation cases used in the Harrop countermodel. -/
theorem root_leaf_negations :
    ¬ Kripke.Forces threeLeafModel .root (neg (atom 0)) ∧
      Kripke.Forces threeLeafModel .u (neg (atom 0)) ∧
      Kripke.Forces threeLeafModel .v (neg (atom 0)) ∧
      ¬ Kripke.Forces threeLeafModel .t (neg (atom 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact h .t (Or.inl rfl) rfl
  · intro z hz hp
    change forkLE .u z at hz
    rcases hz with h | h
    · cases h
    · subst z
      exact (by decide : (0 : ℕ) ≠ 1) hp
  · intro z hz hp
    change forkLE .v z at hz
    rcases hz with h | h
    · cases h
    · subst z
      exact (by decide : (0 : ℕ) ≠ 2) hp
  · intro h
    exact h .t le_rfl rfl


/-- The root forces the displayed premise but fails the precise displayed conclusion. -/
theorem harrop_countermodel :
    Kripke.Forces threeLeafModel .root (harropPremise (atom 0) (atom 1) (atom 2)) ∧
      ¬ Kripke.Forces threeLeafModel .root (harropConclusion (atom 0) (atom 1) (atom 2)) := by
  have hn := root_leaf_negations
  constructor
  · intro z _ hz
    cases z with
    | root => exact (hn.1 hz).elim
    | u => exact Or.inl rfl
    | v => exact Or.inr rfl
    | t => exact (hn.2.2.2 hz).elim
  · rintro (h | h)
    · exact (by decide : (1 : ℕ) ≠ 2) (h .v (Or.inl rfl) hn.2.2.1)
    · exact (by decide : (2 : ℕ) ≠ 1) (h .u (Or.inl rfl) hn.2.1)


theorem harrop_not_derivable :
    ¬ DerivableRule (harropPremise (atom 0) (atom 1) (atom 2))
      (harropConclusion (atom 0) (atom 1) (atom 2)) := by
  intro hd
  have hc := harrop_countermodel
  apply hc.2
  exact Kripke.sound hd threeLeafModel .root (by
    intro D hD
    rcases hD with rfl
    exact hc.1)


/-- An unrestricted antecedent gives a theorem premise and a nontheorem conclusion. -/
theorem unrestricted_antecedent :
    Derives ∅ (impl (disj (atom 1) (atom 2)) (disj (atom 1) (atom 2))) ∧
      ¬ Derives ∅
        (disj (impl (disj (atom 1) (atom 2)) (atom 1))
          (impl (disj (atom 1) (atom 2)) (atom 2))) := by
  refine ⟨identity _, ?_⟩
  intro hd
  have hf := Kripke.sound hd threeLeafModel .root (by
    intro D hD
    cases hD)
  rcases hf with h | h
  · exact (by decide : (1 : ℕ) ≠ 2) (h .v (Or.inl rfl) (Or.inr rfl))
  · exact (by decide : (2 : ℕ) ≠ 1) (h .u (Or.inl rfl) (Or.inl rfl))


end Lemmatheca.Entry.IntuitionisticPropositionalDisjunctionProperty
