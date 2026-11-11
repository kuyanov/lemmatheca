import Lemmatheca.ArslanovCompletenessCriterion.Basic
import Lemmatheca.UniformSelfReference.Uniform
import Lemmatheca.ComputablyInseparableSets.NegativeSearch

namespace Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization

open UniversalComputation EffectiveEnumerations

/-- The partial condition only constrains defined outputs. -/
def PartialFPF (δ : ℕ → Part ℕ) : Prop :=
  ∀ e j, j ∈ δ e → indexSet j ≠ indexSet e

def Totalizes (ψ : ℕ → Part ℕ) (f : ℕ → ℕ) : Prop :=
  Computable f ∧ ∀ n j, j ∈ ψ n → indexSet (f n) = indexSet j

def Avoids (δ ψ : ℕ → Part ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n, ¬ (ψ n).Dom → ¬ (δ (f n)).Dom

def TotalizesAvoiding (δ ψ : ℕ → Part ℕ) (f : ℕ → ℕ) : Prop :=
  Totalizes ψ f ∧ Avoids δ ψ f

theorem partial_fpf_total (f : ℕ → ℕ) :
    PartialFPF (fun n => Part.some (f n)) ↔ ArslanovCompletenessCriterion.FPF f := by
  constructor
  · intro h e
    exact h e (f e) (Part.mem_some _)
  · intro h e j hj
    have he : j = f e := Part.mem_some_iff.mp hj
    subst j
    exact h e

end Lemmatheca.ComputabilityTheory.AntiDiagonalNormalization
