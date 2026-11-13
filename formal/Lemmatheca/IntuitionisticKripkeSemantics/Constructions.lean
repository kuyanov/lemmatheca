import Lemmatheca.IntuitionisticKripkeSemantics.Models

namespace Lemmatheca.ProofTheory.Intuitionistic.Kripke

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u u' v
variable {α : Type u} {β : Type u'} {W : Type v} [Preorder W]

/-- The new atom at a world is forced exactly when its specified image formula is. -/
def substitute (M : Model β W) (σ : α → PropFormula β) : Model α W where
  world_nonempty := M.world_nonempty
  valuation w p := Forces M w (σ p)
  persistent h p hp := forces_mono M (σ p) h hp

theorem substitute_forcing (M : Model β W) (σ : α → PropFormula β)
    (w : W) (A : PropFormula α) :
    Forces (substitute M σ) w A ↔ Forces M w (subst σ A) := by
  induction A generalizing w with
  | atom p => rfl
  | falsum => rfl
  | neg A ih => simp only [Forces, subst, ih]
  | conj A B ihA ihB => simp only [Forces, subst, ihA, ihB]
  | disj A B ihA ihB => simp only [Forces, subst, ihA, ihB]
  | impl A B ihA ihB => simp only [Forces, subst, ihA, ihB]

/-- Restrict to the actual upward cone of the supplied world. -/
def generated (M : Model α W) (w : W) : Model α {z : W // w ≤ z} where
  world_nonempty := ⟨⟨w, le_rfl⟩⟩
  valuation z p := M.valuation z.1 p
  persistent h p hp := M.persistent h p hp

theorem generated_forcing (M : Model α W) (w : W)
    (z : {z : W // w ≤ z}) (A : PropFormula α) :
    Forces (generated M w) z A ↔ Forces M z.1 A := by
  induction A generalizing z with
  | atom p => rfl
  | falsum => rfl
  | neg A ih =>
      constructor
      · intro h t hzt ht
        exact h ⟨t, le_trans z.property hzt⟩ hzt ((ih _).mpr ht)
      · intro h t hzt ht
        exact h t.1 hzt ((ih t).mp ht)
  | conj A B ihA ihB => simp only [Forces, ihA, ihB]
  | disj A B ihA ihB => simp only [Forces, ihA, ihB]
  | impl A B ihA ihB =>
      constructor
      · intro h t hzt ht
        exact (ihB _).mp (h ⟨t, le_trans z.property hzt⟩ hzt ((ihA _).mpr ht))
      · intro h t hzt ht
        exact (ihB t).mpr (h t.1 hzt ((ihA t).mp ht))

theorem generated_countermodel (M : Model α W) (w : W)
    (Γ : Set (PropFormula α)) (A : PropFormula α) (h : Countermodel M w Γ A) :
    Countermodel (generated M w) ⟨w, le_rfl⟩ Γ A := by
  constructor
  · intro B hB
    exact (generated_forcing M w ⟨w, le_rfl⟩ B).mpr (h.1 B hB)
  · intro hA
    exact h.2 ((generated_forcing M w ⟨w, le_rfl⟩ A).mp hA)

/-- The specified Boolean valuation interpreted on a one-element frame. -/
def singleton (b : α → Bool) : Model α PUnit.{v + 1} where
  world_nonempty := ⟨PUnit.unit⟩
  valuation _ p := b p = true
  persistent _ _ hp := hp

theorem singleton_forcing (b : α → Bool) (A : PropFormula α) :
    Forces (singleton.{u, v} b) PUnit.unit A ↔ eval b A = true := by
  induction A with
  | atom p => rfl
  | falsum => simp [Forces, eval]
  | neg A ih =>
      have hn : Forces (singleton.{u, v} b) PUnit.unit (neg A) ↔
          ¬ Forces (singleton.{u, v} b) PUnit.unit A := by
        constructor
        · exact forces_neg_not _ _ _
        · intro h z _ hz
          cases z
          exact h hz
      rw [hn, ih]
      simp [eval]
  | conj A B ihA ihB => simp only [Forces, eval, Bool.and_eq_true, ihA, ihB]
  | disj A B ihA ihB => simp only [Forces, eval, Bool.or_eq_true, ihA, ihB]
  | impl A B ihA ihB =>
      have hi : Forces (singleton.{u, v} b) PUnit.unit (impl A B) ↔
          (Forces (singleton.{u, v} b) PUnit.unit A →
            Forces (singleton.{u, v} b) PUnit.unit B) := by
        constructor
        · intro h
          exact h PUnit.unit le_rfl
        · intro h z _ hz
          cases z
          exact h hz
      rw [hi, ihA, ihB]
      simp only [eval]
      cases eval b A <;> cases eval b B <;> decide

/-- Every model with a sole world recovers a Boolean valuation with exact atom values. -/
theorem one_world_valuation [Subsingleton W] (M : Model α W) (w : W) :
    ∃ b : α → Bool, (∀ p, b p = true ↔ M.valuation w p) ∧
      ∀ A : PropFormula α, Forces M w A ↔ eval b A = true := by
  classical
  let b : α → Bool := fun p => decide (M.valuation w p)
  refine ⟨b, ?_, ?_⟩
  · intro p
    simp [b]
  · intro A
    induction A with
    | atom p => simp [Forces, eval, b]
    | falsum => simp [Forces, eval]
    | neg A ih =>
        have hn : Forces M w (neg A) ↔ ¬ Forces M w A := by
          constructor
          · intro h
            exact h w le_rfl
          · intro h z _ hz
            have hzw : z = w := Subsingleton.elim z w
            subst z
            exact h hz
        rw [hn, ih]
        simp [eval]
    | conj A B ihA ihB => simp only [Forces, eval, Bool.and_eq_true, ihA, ihB]
    | disj A B ihA ihB => simp only [Forces, eval, Bool.or_eq_true, ihA, ihB]
    | impl A B ihA ihB =>
        have hi : Forces M w (impl A B) ↔ (Forces M w A → Forces M w B) := by
          constructor
          · intro h
            exact h w le_rfl
          · intro h z _ hz
            have hzw : z = w := Subsingleton.elim z w
            subst z
            exact h hz
        rw [hi, ihA, ihB]
        simp only [eval]
        cases eval b A <;> cases eval b B <;> decide

theorem valid_boolean (A : PropFormula α) (h : Valid.{u, v} A) :
    Tautology A := by
  intro b
  apply (singleton_forcing.{u, v} b A).mp
  apply h PUnit.{v + 1} (singleton.{u, v} b) PUnit.unit
  intro B hB
  exact hB.elim

end Lemmatheca.ProofTheory.Intuitionistic.Kripke
