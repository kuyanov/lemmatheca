import Lemmatheca.IntuitionisticPropositionalFiniteModelProperty.Traces
import Lemmatheca.IntuitionisticKripkeSemantics.Constructions
import Lemmatheca.PropositionalProofs.Deduction
import Mathlib.Order.Preorder.Finite

/-! Maximal-world Boolean evaluation and Glivenko in the actual numbered-atom language. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Glivenko

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v
variable {α : Type u} {W : Type v} [PartialOrder W]

/-- One Boolean valuation simultaneously describes every native formula at the maximal world. -/
theorem maximal_boolean_valuation (M : Kripke.Model α W) (t : W) (ht : IsMax t) :
    ∃ b : α → Bool, (∀ p, b p = true ↔ M.valuation t p) ∧
      ∀ A : PropFormula α, Kripke.Forces M t A ↔ eval b A = true := by
  let : Subsingleton {z : W // t ≤ z} := ⟨by
    intro x y
    apply Subtype.ext
    have hx : x.val = t := le_antisymm (ht x.property) x.property
    have hy : y.val = t := le_antisymm (ht y.property) y.property
    exact hx.trans hy.symm⟩
  obtain ⟨b, hb, hAll⟩ :=
    Kripke.one_world_valuation (Kripke.generated M t) ⟨t, le_rfl⟩
  refine ⟨b, hb, ?_⟩
  intro A
  exact (Kripke.generated_forcing M t ⟨t, le_rfl⟩ A).symm.trans (hAll A)

/-- Every finite-world future has a maximal Boolean extension satisfying the classical theorem. -/
theorem finite_double_negation [Finite W] (A : PropFormula ℕ)
    (h : Lemmatheca.MathematicalLogic.Propositional.Derives ∅ A)
    (M : Kripke.Model ℕ W) (w : W) :
    Kripke.Forces M w (neg (neg A)) := by
  classical
  apply (Kripke.forces_double_neg_iff M w A).mpr
  intro z _
  obtain ⟨t, hzt, ht⟩ :=
    (Set.toFinite (Set.univ : Set W)).exists_le_maximal (Set.mem_univ z)
  have hmax : IsMax t := by
    intro u htu
    exact ht.2 (Set.mem_univ u) htu
  obtain ⟨b, _, hBool⟩ := maximal_boolean_valuation M t hmax
  refine ⟨t, hzt, (hBool A).mpr ?_⟩
  exact derives_sound h b (by
    intro B hB
    simp at hB)

/-- The finite-model semantic argument precedes all use of the negative translation. -/
theorem glivenko (A : PropFormula ℕ) :
    Lemmatheca.MathematicalLogic.Propositional.Derives ∅ A ↔
      Derives ∅ (neg (neg A)) := by
  constructor
  · intro h
    apply (FiniteModels.finite_poset_valid_iff (neg (neg A))).mp
    intro V r f M w
    let : PartialOrder V := r
    let : Fintype V := f
    exact finite_double_negation A h M w
  · intro h
    apply Lemmatheca.MathematicalLogic.Propositional.derives_complete
    intro b _
    have hv := boolean_sound h b (by
      intro B hB
      exact hB.elim)
    simpa [Satisfies, eval] using hv

end Lemmatheca.ProofTheory.Intuitionistic.Glivenko
