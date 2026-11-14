import Lemmatheca.PropositionalWeakExcludedMiddle.Schemas
import Mathlib.Order.Bounds.Basic

/-! Directedness is local to a future cone, and validity ranges over all valuations. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.WeakExcludedMiddle
open Lemmatheca.MathematicalLogic.Propositional
open Kripke
universe u v

def ConeDirected {W : Type v} [Preorder W] (w : W) : Prop :=
  ∀ u v : W, w ≤ u → w ≤ v → ∃ z : W, u ≤ z ∧ v ≤ z

def DirectedFutureCones (W : Type v) [Preorder W] : Prop := ∀ w : W, ConeDirected w

theorem directed_cone_forces_wem {α : Type u} {W : Type v} [Preorder W]
    (M : Model α W) (w : W) (h : ConeDirected w) (A : PropFormula α) :
    Forces M w (wem A) := by
  classical
  by_cases hex : ∃ u : W, w ≤ u ∧ Forces M u A
  · obtain ⟨u, hwu, hu⟩ := hex
    apply Or.inr
    apply (forces_double_neg_iff M w A).mpr
    intro v hwv
    obtain ⟨z, huz, hvz⟩ := h u v hwu hwv
    exact ⟨z, hvz, forces_mono M A huz hu⟩
  · apply Or.inl
    intro u hwu hu
    exact hex ⟨u, hwu, hu⟩

/-- Only atom zero is verified, exactly on the specified world's upward cone. -/
def upsetModel {W : Type v} [Preorder W] [Nonempty W] (u : W) : Model ℕ W where
  world_nonempty := inferInstance
  valuation x p := p = 0 ∧ u ≤ x
  persistent hxy _ hp := ⟨hp.1, le_trans hp.2 hxy⟩

theorem nonjoining_countervaluation {W : Type v} [Preorder W] [Nonempty W]
    (w u v : W) (hwu : w ≤ u) (hwv : w ≤ v)
    (hno : ¬ ∃ z : W, u ≤ z ∧ v ≤ z) :
    Forces (upsetModel u) u (.atom 0) ∧
      ¬ Forces (upsetModel u) w (.neg (.atom 0)) ∧
      Forces (upsetModel u) v (.neg (.atom 0)) ∧
      ¬ Forces (upsetModel u) w (.neg (.neg (.atom 0))) ∧
      ¬ Forces (upsetModel u) w (wem (.atom 0)) := by
  have hu : Forces (upsetModel u) u (.atom 0) := ⟨rfl, le_rfl⟩
  have hnot : ¬ Forces (upsetModel u) w (.neg (.atom 0)) := by
    intro h
    exact h u hwu hu
  have hv : Forces (upsetModel u) v (.neg (.atom 0)) := by
    intro z hvz hz
    exact hno ⟨z, hz.2, hvz⟩
  have hnn : ¬ Forces (upsetModel u) w (.neg (.neg (.atom 0))) := by
    intro h
    exact h v hwv hv
  exact ⟨hu, hnot, hv, hnn, fun h => h.elim hnot hnn⟩

theorem frame_wem_iff_directed {W : Type v} [Preorder W] [Nonempty W] :
    (∀ A : PropFormula ℕ, FrameValid W (wem A)) ↔ DirectedFutureCones W := by
  classical
  constructor
  · intro h w u v hwu hwv
    by_contra hn
    exact (nonjoining_countervaluation w u v hwu hwv hn).2.2.2.2
      (h (.atom 0) (upsetModel u) w)
  · intro h A M w
    exact directed_cone_forces_wem M w (h w) A

theorem frame_atom_wem_iff_directed {W : Type v} [Preorder W] [Nonempty W] :
    FrameValid W (wem (.atom (0 : ℕ))) ↔ DirectedFutureCones W := by
  classical
  constructor
  · intro h w u v hwu hwv
    by_contra hn
    exact (nonjoining_countervaluation w u v hwu hwv hn).2.2.2.2 (h (upsetModel u) w)
  · intro h
    exact frame_wem_iff_directed.mpr h (.atom 0)

theorem finite_rooted_directed_iff_greatest {W : Type v} [PartialOrder W] [Finite W]
    (r : W) (hr : ∀ w : W, r ≤ w) :
    DirectedFutureCones W ↔ ∃ t : W, ∀ w : W, w ≤ t := by
  classical
  constructor
  · intro h
    let := Fintype.ofFinite W
    have hb (s : Finset W) : ∃ t : W, ∀ w ∈ s, w ≤ t := by
      induction s using Finset.induction_on with
      | empty => exact ⟨r, by simp⟩
      | @insert a s _ ih =>
          obtain ⟨t, ht⟩ := ih
          obtain ⟨z, htz, haz⟩ := h r t a (hr t) (hr a)
          refine ⟨z, ?_⟩
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact haz
          · exact le_trans (ht w hw) htz
    obtain ⟨t, ht⟩ := hb Finset.univ
    exact ⟨t, fun w => ht w (Finset.mem_univ w)⟩
  · rintro ⟨t, ht⟩ _ u v _ _
    exact ⟨t, ht u, ht v⟩

theorem finite_rooted_wem_iff_greatest {W : Type v} [PartialOrder W] [Finite W] [Nonempty W]
    (r : W) (hr : ∀ w : W, r ≤ w) :
    (∀ A : PropFormula ℕ, FrameValid W (wem A)) ↔ ∃ t : W, ∀ w : W, w ≤ t := by
  exact frame_wem_iff_directed.trans (finite_rooted_directed_iff_greatest r hr)

end Lemmatheca.ProofTheory.Intuitionistic.WeakExcludedMiddle
