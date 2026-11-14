import Lemmatheca.MinimalPropositionalLogic.Deduction
import Lemmatheca.IntuitionisticKripkeSemantics.Models

/-! Abnormal-world semantics for the native minimal propositional calculus. -/
namespace Lemmatheca.ProofTheory.Minimal.Kripke
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u v

/-- Persistent atoms and an independently persistent interpretation of falsum. -/
structure Model (α : Type u) (W : Type v) [Preorder W] where
  valuation : W → α → Prop
  persistent : ∀ {w z : W}, w ≤ z → ∀ p, valuation w p → valuation z p
  abnormal : W → Prop
  abnormal_persistent : ∀ {w z : W}, w ≤ z → abnormal w → abnormal z

variable {α : Type u} {W : Type v} [Preorder W]

/-- Minimal forcing interprets negation as implication to the abnormal upset. -/
def Forces (M : Model α W) (w : W) : PropFormula α → Prop
  | .atom p => M.valuation w p
  | .falsum => M.abnormal w
  | .neg A => ∀ z, w ≤ z → Forces M z A → M.abnormal z
  | .conj A B => Forces M w A ∧ Forces M w B
  | .disj A B => Forces M w A ∨ Forces M w B
  | .impl A B => ∀ z, w ≤ z → Forces M z A → Forces M z B

def ForcesContext (M : Model α W) (w : W) (Γ : Set (PropFormula α)) : Prop :=
  ∀ A ∈ Γ, Forces M w A

def Countermodel (M : Model α W) (w : W) (Γ : Set (PropFormula α))
    (A : PropFormula α) : Prop := ForcesContext M w Γ ∧ ¬ Forces M w A

/-- An ordinary intuitionistic model is a minimal model with no abnormal worlds. -/
def ofIntuitionistic (M : Intuitionistic.Kripke.Model α W) : Model α W where
  valuation := M.valuation
  persistent := M.persistent
  abnormal := fun _ => False
  abnormal_persistent := fun _ h => h.elim

theorem forces_ofIntuitionistic (M : Intuitionistic.Kripke.Model α W)
    (w : W) (A : PropFormula α) :
    Forces (ofIntuitionistic M) w A ↔ Intuitionistic.Kripke.Forces M w A := by
  induction A generalizing w <;>
    simp_all [Forces, ofIntuitionistic, Intuitionistic.Kripke.Forces]


theorem forces_mono (M : Model α W) (A : PropFormula α) {w z : W}
    (hwz : w ≤ z) (hA : Forces M w A) : Forces M z A := by
  induction A generalizing w z with
  | atom p => exact M.persistent hwz p hA
  | falsum => exact M.abnormal_persistent hwz hA
  | neg A _ =>
      intro t hzt
      exact hA t (le_trans hwz hzt)
  | conj A B ihA ihB => exact ⟨ihA hwz hA.1, ihB hwz hA.2⟩
  | disj A B ihA ihB => exact hA.imp (ihA hwz) (ihB hwz)
  | impl A B _ _ =>
      intro t hzt
      exact hA t (le_trans hwz hzt)


theorem sound {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : Minimal.Derives Γ A) (M : Model α W) (w : W)
    (hΓ : ForcesContext M w Γ) : Forces M w A := by
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


theorem countermodel_not_derivable (M : Model α W) (w : W)
    (Γ : Set (PropFormula α)) (A : PropFormula α) (h : Countermodel M w Γ A) :
    ¬ Minimal.Derives Γ A := by
  intro hd
  exact h.2 (sound hd M w h.1)


end Lemmatheca.ProofTheory.Minimal.Kripke
