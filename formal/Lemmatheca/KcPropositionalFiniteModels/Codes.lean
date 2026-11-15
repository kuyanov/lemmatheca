import Lemmatheca.KcPropositionalFiniteModels.Countermodels
import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Codes

namespace Lemmatheca.ProofTheory.Intuitionistic.KCFiniteModels

open Lemmatheca.MathematicalLogic.Propositional
open Kripke
open FiniteModels

/-- All conditions concern the supplied relation table, never the numerical Fin order. -/
def RootedTop {n : ℕ} (r : RelationCode n) (root top : Fin n) : Prop :=
  (∀ j, r root j = true) ∧
  (∀ j, r j top = true) ∧
  (∀ j k, r j k = true → r k j = true → j = k)

instance rootedTopDecidable {n : ℕ} (r : RelationCode n) (root top : Fin n) :
    Decidable (RootedTop r root top) := by
  unfold RootedTop
  infer_instance

def rootedTop {n : ℕ} (r : RelationCode n) (root top : Fin n) : Bool :=
  decide (RootedTop r root top)

theorem rootedTop_correct {n : ℕ} (r : RelationCode n) (root top : Fin n) :
    rootedTop r root top = true ↔ RootedTop r root top := by
  simp [rootedTop]

/-- This extends exactly the already established coded preorder. -/
@[instance_reducible] def codePartialOrder {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S)
    (h : Admissible r v) (root top : Fin n) (hc : RootedTop r root top) :
    PartialOrder (Fin n) where
  toPreorder := codePreorder r v h
  le_antisymm _ _ hij hji := hc.2.2 _ _ hij hji

theorem code_endpoints {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S)
    (h : Admissible r v) (root top : Fin n) (hc : RootedTop r root top) :
    (∀ j : Fin n, @LE.le (Fin n) (codePreorder r v h).toLE root j) ∧
    (∀ j : Fin n, @LE.le (Fin n) (codePreorder r v h).toLE j top) := by
  exact ⟨hc.1, hc.2.1⟩

theorem code_forces_wem {n : ℕ} {S : Finset ℕ}
    (r : RelationCode n) (v : ValuationCode n S) (hn : 0 < n)
    (h : Admissible r v) (root top : Fin n) (hc : RootedTop r root top)
    (i : Fin n) (A : Formula) :
    @Forces ℕ (Fin n) (codePreorder r v h) (codeModel r v hn h) i
      (WeakExcludedMiddle.wem A) := by
  exact @greatest_world_wem (Fin n) (codePreorder r v h)
    (codeModel r v hn h) top hc.2.1 i A

theorem presentation_rootedTop {W : Type u} [PartialOrder W] {n : ℕ}
    (b : Fin n ≃ W) (root top : W)
    (hr : ∀ w : W, root ≤ w) (ht : ∀ w : W, w ≤ top) :
    RootedTop (presentRelation b) (b.symm root) (b.symm top) := by
  classical
  simp only [RootedTop, presentRelation, decide_eq_true_eq, Equiv.apply_symm_apply]
  refine ⟨fun j => hr (b j), fun j => ht (b j), ?_⟩
  intro j k hjk hkj
  exact b.injective (le_antisymm hjk hkj)

end Lemmatheca.ProofTheory.Intuitionistic.KCFiniteModels
