import Lemmatheca.IntuitionisticPropositionalProofInterpolation.Extraction

/-! Native consequences are existential assertions: the existing native
Derives family is Prop-valued, while supplied sequent trees return actual data. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Interpolation
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

theorem Packet.native_factors {L R : Finset (PropFormula α)} {C : PropFormula α}
    (w : Packet L R C) :
    Intuitionistic.Derives (L : Set (PropFormula α)) w.middle ∧
      Intuitionistic.Derives ((insert w.middle R : Finset (PropFormula α)) : Set (PropFormula α)) C := by
  exact ⟨w.left.to_natural, w.right.to_natural⟩

/-- Existence only; no Type-valued packet is selected from native derivability. -/
theorem native_interpolation (A B : PropFormula α)
    (h : Intuitionistic.Derives ({A} : Set (PropFormula α)) B) :
    ∃ I : PropFormula α,
      Intuitionistic.Derives ({A} : Set (PropFormula α)) I ∧
      Intuitionistic.Derives ({I} : Set (PropFormula α)) B ∧
      atoms I ⊆ atoms A ∩ atoms B := by
  have hn : Intuitionistic.Derives (({A} : Finset (PropFormula α)) : Set (PropFormula α)) B := by
    simpa only [Finset.coe_singleton] using h
  obtain ⟨p⟩ := CutFree.from_natural hn
  let w := extract p ({A} : Finset (PropFormula α)) ∅ (by simp [Covers])
  refine ⟨w.middle, ?_, ?_, ?_⟩
  · simpa only [Finset.coe_singleton] using w.native_factors.1
  · simpa using w.native_factors.2
  · simpa [contextAtoms] using w.support

end Lemmatheca.ProofTheory.Intuitionistic.Interpolation
