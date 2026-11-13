import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction
import Mathlib.Order.Basic

/-! Persistent Kripke models and native-formula forcing for intuitionistic logic. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Kripke

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v

/-- A nonempty preordered frame with a persistent propositional atom valuation. -/
structure Model (α : Type u) (W : Type v) [Preorder W] where
  world_nonempty : Nonempty W
  valuation : W → α → Prop
  persistent : ∀ {w z : W}, w ≤ z → ∀ p, valuation w p → valuation z p

variable {α : Type u} {W : Type v} [Preorder W]

/-- Forcing on the actual shared propositional syntax, including native negation. -/
def Forces (M : Model α W) (w : W) : PropFormula α → Prop
  | .atom p => M.valuation w p
  | .falsum => False
  | .neg A => ∀ z, w ≤ z → ¬ Forces M z A
  | .conj A B => Forces M w A ∧ Forces M w B
  | .disj A B => Forces M w A ∨ Forces M w B
  | .impl A B => ∀ z, w ≤ z → Forces M z A → Forces M z B

/-- A world forces a possibly infinite set when it forces each allowed premise. -/
def ForcesContext (M : Model α W) (w : W) (Γ : Set (PropFormula α)) : Prop :=
  ∀ A ∈ Γ, Forces M w A

/-- A specified model and world witness a failed consequence. -/
def Countermodel (M : Model α W) (w : W) (Γ : Set (PropFormula α))
    (A : PropFormula α) : Prop := ForcesContext M w Γ ∧ ¬ Forces M w A

/-- Consequence over all nonempty preordered models in a fixed world universe. -/
def Entails (Γ : Set (PropFormula α)) (A : PropFormula α) : Prop :=
  ∀ (X : Type v) [Preorder X] (M : Model α X) (w : X),
    ForcesContext M w Γ → Forces M w A

/-- A formula is valid when no assumptions are required for its consequence. -/
def Valid (A : PropFormula α) : Prop := Entails.{u, v} (∅ : Set (PropFormula α)) A

theorem forces_mono (M : Model α W) (A : PropFormula α) {w z : W}
    (hwz : w ≤ z) (hA : Forces M w A) : Forces M z A := by
  induction A generalizing w z with
  | atom p => exact M.persistent hwz p hA
  | falsum => exact hA.elim
  | neg A _ =>
      intro t hzt
      exact hA t (le_trans hwz hzt)
  | conj A B ihA ihB => exact ⟨ihA hwz hA.1, ihB hwz hA.2⟩
  | disj A B ihA ihB => exact hA.imp (ihA hwz) (ihB hwz)
  | impl A B _ _ =>
      intro t hzt
      exact hA t (le_trans hwz hzt)

theorem forces_neg_iff_imp_falsum (M : Model α W) (w : W) (A : PropFormula α) :
    Forces M w (neg A) ↔ Forces M w (impl A falsum) := by
  rfl

theorem forces_neg_not (M : Model α W) (w : W) (A : PropFormula α)
    (h : Forces M w (neg A)) : ¬ Forces M w A := by
  exact h w le_rfl

theorem forces_double_neg_iff (M : Model α W) (w : W) (A : PropFormula α) :
    Forces M w (neg (neg A)) ↔ ∀ z, w ≤ z → ∃ t, z ≤ t ∧ Forces M t A := by
  classical
  constructor
  · intro h z hwz
    by_contra hn
    apply h z hwz
    intro t hzt ht
    exact hn ⟨t, hzt, ht⟩
  · intro h z hwz hn
    obtain ⟨t, hzt, ht⟩ := h z hwz
    exact hn t hzt ht

/-- Soundness at the specified world, with exactly the native ND premise set. -/
theorem sound {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : Lemmatheca.ProofTheory.Intuitionistic.Derives Γ A)
    (M : Model α W) (w : W) (hΓ : ForcesContext M w Γ) : Forces M w A := by
  induction h generalizing w with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact ⟨ihA w hΓ, ihB w hΓ⟩
  | conjElimLeft _ ih => exact (ih w hΓ).1
  | conjElimRight _ ih => exact (ih w hΓ).2
  | disjIntroLeft _ ih => exact Or.inl (ih w hΓ)
  | disjIntroRight _ ih => exact Or.inr (ih w hΓ)
  | disjElim _ _ _ ihAB ihA ihB =>
      rcases ihAB w hΓ with hA | hB
      · apply ihA w
        intro D hD
        rcases Set.mem_insert_iff.mp hD with rfl | hD
        · exact hA
        · exact hΓ D hD
      · apply ihB w
        intro D hD
        rcases Set.mem_insert_iff.mp hD with rfl | hD
        · exact hB
        · exact hΓ D hD
  | implIntro _ ih =>
      intro z hwz hA
      apply ih z
      intro D hD
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · exact hA
      · exact forces_mono M D hwz (hΓ D hD)
  | implElim _ _ ihAB ihA => exact ihAB w hΓ w le_rfl (ihA w hΓ)
  | negIntro _ ih =>
      intro z hwz hA
      apply ih z
      intro D hD
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · exact hA
      · exact forces_mono M D hwz (hΓ D hD)
  | negElim _ _ ihA ihN => exact ihN w hΓ w le_rfl (ihA w hΓ)
  | falsumElim _ ih => exact (ih w hΓ).elim

theorem countermodel_not_derivable (M : Model α W) (w : W)
    (Γ : Set (PropFormula α)) (A : PropFormula α) (h : Countermodel M w Γ A) :
    ¬ Lemmatheca.ProofTheory.Intuitionistic.Derives Γ A := by
  intro hd
  exact h.2 (sound hd M w h.1)

end Lemmatheca.ProofTheory.Intuitionistic.Kripke
