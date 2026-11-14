import Lemmatheca.IntuitionisticPropositionalCutElimination.Translations

/-! Actual native formula and cut-free proof data for a single-succedent split. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Interpolation
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

/-- The atom-free native abbreviation, without adding a constructor. -/
def topFormula : PropFormula α := .impl .falsum .falsum

/-- Covering permits overlap and extra allowed assumptions. -/
def Covers (Γ L R : Finset (PropFormula α)) : Prop := Γ ⊆ L ∪ R

/-- The actual middle formula and both existing single-conclusion proof trees. -/
structure Packet (L R : Finset (PropFormula α)) (C : PropFormula α) where
  middle : PropFormula α
  left : CutFree.Proof L middle
  right : CutFree.Proof (insert middle R) C
  support : atoms middle ⊆ contextAtoms L ∩ (contextAtoms R ∪ atoms C)

theorem Packet.support_empty {L R : Finset (PropFormula α)} {C : PropFormula α}
    (w : Packet L R C) (h : Disjoint (contextAtoms L) (contextAtoms R ∪ atoms C)) :
    atoms w.middle = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact Finset.disjoint_left.mp h (Finset.mem_inter.mp (w.support ha)).1 (Finset.mem_inter.mp (w.support ha)).2

end Lemmatheca.ProofTheory.Intuitionistic.Interpolation
