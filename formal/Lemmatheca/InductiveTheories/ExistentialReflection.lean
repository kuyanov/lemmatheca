import Mathlib.ModelTheory.Complexity

/-! Existential reflection along a supplied ordinary embedding. -/
namespace Lemmatheca.ModelTheory.ModelCompleteness
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u, v}}

/-- Existential truth is reflected along the specified embedding, with finite parameters. -/
def ExistentiallyClosedEmbedding {M : Type*} {N : Type*} [L.Structure M]
    [L.Structure N] (f : M ↪[L] N) : Prop :=
  ∀ (n : ℕ) (φ : L.Formula (Fin n)), φ.IsExistential →
    ∀ a : Fin n → M, φ.Realize (f ∘ a) → φ.Realize a

end Lemmatheca.ModelTheory.ModelCompleteness
