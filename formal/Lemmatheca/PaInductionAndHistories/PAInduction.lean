import Lemmatheca.PaInductionAndHistories.PAOrderedArithmetic
import Lemmatheca.PaInductionAndHistories.PAChineseRemainder
import Mathlib.ModelTheory.Definability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory

/-! Induction for predicates defined by arithmetic formulas with parameters.
Finite parameter extraction is essential: induction is never assumed for
arbitrary external subsets of a nonstandard model. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
noncomputable section
universe u

theorem definable_predicate_formula {M : Type u} [language.Structure M]
    (P : M → Prop) (hP : Set.univ.Definable₁ language {x | P x}) :
    ∃ k : ℕ, ∃ φ : language.Formula (Fin k ⊕ Unit), ∃ v : Fin k → M,
      ∀ y, φ.Realize (extend v y) ↔ P y := by
  obtain ⟨A, _, hA⟩ := Set.definable_iff_finitely_definable.mp hP
  obtain ⟨ψ, hψ⟩ := Set.definable_iff_exists_formula_sum.mp hA
  let k := Fintype.card A
  let e : A ≃ Fin k := Fintype.equivFin A
  let φ : language.Formula (Fin k ⊕ Unit) :=
    ψ.relabel (Sum.map e (fun _ : Fin 1 => ()))
  let v : Fin k → M := fun i => (e.symm i).val
  have hφ (y : M) : φ.Realize (extend v y) ↔ P y := by
    have he := Set.ext_iff.mp hψ (fun _ : Fin 1 => y)
    change P y ↔ ψ.Realize (Sum.elim (↑) (fun _ => y)) at he
    dsimp only [φ]
    rw [Formula.realize_relabel]
    have hv : extend v y ∘ Sum.map e (fun _ : Fin 1 => ()) =
        Sum.elim (↑) (fun _ : Fin 1 => y) := by
      funext i
      cases i with
      | inl i => simp [extend, v]
      | inr i => rfl
    rw [hv]
    exact he.symm
  exact ⟨k, φ, v, hφ⟩

theorem definable_induction {M : Type u} [language.Structure M] [M ⊨ PA]
    (P : M → Prop) (hP : Set.univ.Definable₁ language {x | P x})
    (hz : P (zeroValue M)) (hs : ∀ x, P x → P (succValue M x)) : ∀ x, P x := by
  obtain ⟨_, φ, v, hφ⟩ := definable_predicate_formula P hP
  exact formula_induction φ v P hφ hz hs

theorem definable_strong_induction {M : Type u} [language.Structure M] [M ⊨ PA]
    (P : M → Prop) (hP : Set.univ.Definable₁ language {x | P x})
    (hs : ∀ x, (∀ y, leValue M (succValue M y) x → P y) → P x) : ∀ x, P x := by
  obtain ⟨_, φ, v, hφ⟩ := definable_predicate_formula P hP
  intro x
  by_contra hx
  have hex : ∃ y, φ.not.Realize (extend v y) :=
    ⟨x, Formula.realize_not.mpr (fun h => hx ((hφ x).mp h))⟩
  obtain ⟨y, hy, hmin⟩ := least_witness_model φ.not v hex
  have hn : ¬ P y := fun hp => (Formula.realize_not.mp hy) ((hφ y).mpr hp)
  apply hn
  apply hs y
  intro z hz
  by_contra hnot
  exact hmin z hz (Formula.realize_not.mpr (fun h => hnot ((hφ z).mp h)))

end
end Lemmatheca.ProofTheory.PAComputations
