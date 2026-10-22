import Lemmatheca.FirstOrderNormalForms.FirstOrderNormalForms
import Mathlib.ModelTheory.Substructures
import Mathlib.ModelTheory.Complexity

/-! The atomic and literal criteria for ordinary structure embeddings. -/

namespace Lemmatheca.ModelTheory.ElementarySubmodels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderNormalForms

universe u v w w'
variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

theorem embedding_iff_atomic_agreement (f : M → N) :
    (∃ e : M ↪[L] N, (e : M → N) = f) ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)), φ.IsAtomic →
        ∀ a : Fin n → M, φ.Realize a ↔ φ.Realize (f ∘ a) := by
  constructor
  · rintro ⟨e, rfl⟩ n φ hφ a
    simpa only [Formula.Realize, Unique.eq_default] using
      (hφ.isQF.realize_embedding e (v := a) (xs := default)).symm
  · intro ha
    have hf : Function.Injective f := by
      intro a b hab
      have h := (ha 2 ((Term.var (0 : Fin 2)).equal (.var 1))
        (.equal _ _) ![a, b]).mpr
      simpa using h (by simpa using hab)
    refine ⟨{ toFun := f, inj' := hf, map_fun' := ?_, map_rel' := ?_ }, rfl⟩
    · intro n g a
      have h := (ha (n + 1) (Formula.graph g) (Formula.isAtomic_graph g)
        (Fin.cons (Structure.funMap g a) a)).mp (Formula.realize_graph.mpr rfl)
      rw [Fin.comp_cons, Formula.realize_graph] at h
      exact h.symm
    · intro n r a
      exact (ha n (.rel r (fun i => .var (.inl i))) (.rel r _) a).symm

theorem embedding_iff_preserves_literals (f : M → N) :
    (∃ e : M ↪[L] N, (e : M → N) = f) ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)), IsLiteral φ →
        ∀ a : Fin n → M, φ.Realize a → φ.Realize (f ∘ a) := by
  rw [embedding_iff_atomic_agreement]
  constructor
  · intro h n φ hφ a ha
    rcases hφ with hφ | ⟨ψ, hψ, rfl⟩
    · exact (h n φ hφ a).mp ha
    · exact fun hb => ha ((h n ψ hψ a).mpr hb)
  · intro h n φ hφ a
    refine ⟨h n φ (Or.inl hφ) a, ?_⟩
    intro hb
    by_contra ha
    exact (h n φ.not (Or.inr ⟨φ, hφ, rfl⟩) a ha) hb

end Lemmatheca.ModelTheory.ElementarySubmodels
