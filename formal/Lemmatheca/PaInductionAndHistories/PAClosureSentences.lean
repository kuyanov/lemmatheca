import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Universal closure and totality sentences used by the PA induction and history arguments. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section
universe u

/-- Universal closure, independent of a particular finite-variable enumeration. -/
def allClose {α : Type} [Fintype α] (φ : language.Formula α) : language.Sentence :=
  (φ.relabel (Sum.inr : α → Empty ⊕ α)).iAlls α

theorem realize_allClose {α : Type} [Fintype α] {M : Type u}
    [language.Structure M] (φ : language.Formula α) :
    M ⊨ allClose φ ↔ ∀ x : α → M, φ.Realize x := by
  simp only [allClose, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr]

/-- The actual sentence asserting totality and uniqueness at all internal inputs. -/
def totalUnique {n : ℕ} (φ : language.Formula (Fin n ⊕ Unit)) : language.Sentence :=
  let compare : language.Formula ((Fin n ⊕ Unit) ⊕ Unit) :=
    (graphAt φ (fun i => .var (.inl (.inl i))) (.var (.inr ()))).imp
      ((Term.var (.inr ())).equal (.var (.inl (.inr ()))))
  allClose ((φ ⊓ compare.iAlls Unit).iExs Unit)

theorem realize_totalUnique {n : ℕ} {M : Type u} [language.Structure M]
    (φ : language.Formula (Fin n ⊕ Unit)) :
    M ⊨ totalUnique φ ↔ ∀ x : Fin n → M, ∃! y, φ.Realize (extend x y) := by
  simp only [totalUnique, realize_allClose, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    realize_graphAt, Term.realize_var, Formula.realize_equal,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h x
    obtain ⟨y, hy, huniq⟩ := h x
    refine ⟨y (), ?_, ?_⟩
    · convert hy using 1
      congr 1
    · intro z hz
      exact huniq (fun _ => z) hz
  · intro h x
    obtain ⟨y, hy, huniq⟩ := h x
    exact ⟨fun _ => y, hy, fun z hz => huniq (z ()) hz⟩

def PAEquivalent {α : Type} [Fintype α] (φ ψ : language.Formula α) : Prop :=
  Derives PA (allClose (φ.iff ψ))

end
end Lemmatheca.ProofTheory.PAComputations
