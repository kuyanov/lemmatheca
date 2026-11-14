import Lemmatheca.PropositionalDummettLinearity.Schemas
import Lemmatheca.PropositionalWeakExcludedMiddle.Frames

/-! Every pair of futures of a fixed world must be comparable; unrelated components need not be. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Dummett
open Lemmatheca.MathematicalLogic.Propositional
open Kripke
universe u v

def ConeLinear {W : Type v} [Preorder W] (w : W) : Prop :=
  ∀ u v : W, w ≤ u → w ≤ v → u ≤ v ∨ v ≤ u

def LocallyLinear (W : Type v) [Preorder W] : Prop := ∀ w : W, ConeLinear w

/-- The two numbered atoms have the supplied upward cones; all other atoms are false. -/
def twoUpsetModel {W : Type v} [Preorder W] [Nonempty W] (u v : W) : Model ℕ W where
  world_nonempty := inferInstance
  valuation x p := (p = 0 ∧ u ≤ x) ∨ (p = 1 ∧ v ≤ x)
  persistent hxy _ hp := hp.imp (fun h => ⟨h.1, le_trans h.2 hxy⟩)
    (fun h => ⟨h.1, le_trans h.2 hxy⟩)

theorem linear_cone_forces_linearity {α : Type u} {W : Type v} [Preorder W]
    (M : Model α W) (w : W) (h : ConeLinear w) (A B : PropFormula α) :
    Forces M w (linearity A B) := by
  classical
  by_cases hAB : Forces M w (.impl A B)
  · exact Or.inl hAB
  · apply Or.inr
    have hex : ∃ u : W, w ≤ u ∧ Forces M u A ∧ ¬ Forces M u B := by
      by_contra hn
      apply hAB
      intro u hwu hu
      by_contra hb
      exact hn ⟨u, hwu, hu, hb⟩
    obtain ⟨u, hwu, hu, hnot⟩ := hex
    intro v hwv hv
    rcases h u v hwu hwv with huv | hvu
    · exact forces_mono M A huv hu
    · exact (hnot (forces_mono M B hvu hv)).elim

theorem incomparable_countervaluation {W : Type v} [Preorder W] [Nonempty W]
    (w u v : W) (hwu : w ≤ u) (hwv : w ≤ v) (hnotuv : ¬ u ≤ v) (hnotvu : ¬ v ≤ u) :
    Forces (twoUpsetModel u v) u (.atom 0) ∧
      ¬ Forces (twoUpsetModel u v) u (.atom 1) ∧
      Forces (twoUpsetModel u v) v (.atom 1) ∧
      ¬ Forces (twoUpsetModel u v) v (.atom 0) ∧
      ¬ Forces (twoUpsetModel u v) w (.impl (.atom 0) (.atom 1)) ∧
      ¬ Forces (twoUpsetModel u v) w (.impl (.atom 1) (.atom 0)) ∧
      ¬ Forces (twoUpsetModel u v) w (linearity (.atom 0) (.atom 1)) := by
  have hu : Forces (twoUpsetModel u v) u (.atom 0) := Or.inl ⟨rfl, le_rfl⟩
  have hv : Forces (twoUpsetModel u v) v (.atom 1) := Or.inr ⟨rfl, le_rfl⟩
  have hun : ¬ Forces (twoUpsetModel u v) u (.atom 1) := by
    rintro (h | h)
    · exact (by decide : (1 : ℕ) ≠ 0) h.1
    · exact hnotvu h.2
  have hvn : ¬ Forces (twoUpsetModel u v) v (.atom 0) := by
    rintro (h | h)
    · exact hnotuv h.2
    · exact (by decide : (0 : ℕ) ≠ 1) h.1
  have hab : ¬ Forces (twoUpsetModel u v) w (.impl (.atom 0) (.atom 1)) :=
    fun h => hun (h u hwu hu)
  have hba : ¬ Forces (twoUpsetModel u v) w (.impl (.atom 1) (.atom 0)) :=
    fun h => hvn (h v hwv hv)
  exact ⟨hu, hun, hv, hvn, hab, hba, fun h => h.elim hab hba⟩

theorem frame_linearity_iff_local {W : Type v} [Preorder W] [Nonempty W] :
    (∀ A B : PropFormula ℕ, FrameValid W (linearity A B)) ↔ LocallyLinear W := by
  classical
  constructor
  · intro h w u v hwu hwv
    by_contra hn
    have huv : ¬ u ≤ v := fun huv => hn (Or.inl huv)
    have hvu : ¬ v ≤ u := fun hvu => hn (Or.inr hvu)
    exact (incomparable_countervaluation w u v hwu hwv huv hvu).2.2.2.2.2.2
      (h (.atom 0) (.atom 1) (twoUpsetModel u v) w)
  · intro h A B M w
    exact linear_cone_forces_linearity M w (h w) A B

theorem frame_two_atom_linearity_iff_local {W : Type v} [Preorder W] [Nonempty W] :
    FrameValid W (linearity (.atom (0 : ℕ)) (.atom 1)) ↔ LocallyLinear W := by
  classical
  constructor
  · intro h w u v hwu hwv
    by_contra hn
    have huv : ¬ u ≤ v := fun huv => hn (Or.inl huv)
    have hvu : ¬ v ≤ u := fun hvu => hn (Or.inr hvu)
    exact (incomparable_countervaluation w u v hwu hwv huv hvu).2.2.2.2.2.2
      (h (twoUpsetModel u v) w)
  · intro h
    exact frame_linearity_iff_local.mpr h (.atom 0) (.atom 1)

theorem rooted_local_iff_global {W : Type v} [Preorder W]
    (r : W) (hr : ∀ w : W, r ≤ w) :
    LocallyLinear W ↔ ∀ u v : W, u ≤ v ∨ v ≤ u := by
  constructor
  · intro h u v
    exact h r u v (hr u) (hr v)
  · intro h _ u v _ _
    exact h u v

end Lemmatheca.ProofTheory.Intuitionistic.Dummett
