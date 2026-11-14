import Lemmatheca.IntuitionisticPropositionalProofInterpolation.Native
import Lemmatheca.IntuitionisticPropositionalCutElimination.Examples

/-! The identical supplied implication proof under two splits, and exact
atom-free packets at falsum and overlapping antecedents. -/
namespace Lemmatheca.Entry.IntuitionisticPropositionalProofInterpolation
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic.Interpolation
universe u
variable {α : Type u} [DecidableEq α]
noncomputable section

def leftPacket (p q : α) : Packet {impl (atom p) (atom q)} {atom p} (atom q) :=
  extract (Lemmatheca.Entry.IntuitionisticPropositionalCutElimination.modusPonens (atom p) (atom q))
    {impl (atom p) (atom q)} {atom p} (by simp [Covers, Finset.subset_iff])

def rightPacket (p q : α) : Packet {atom p} {impl (atom p) (atom q)} (atom q) :=
  extract (Lemmatheca.Entry.IntuitionisticPropositionalCutElimination.modusPonens (atom p) (atom q))
    {atom p} {impl (atom p) (atom q)} (by simp [Covers])

theorem leftPacket_middle (p q : α) :
    (leftPacket p q).middle = impl (atom p) (atom q) := by
  simp [leftPacket, extract, Lemmatheca.Entry.IntuitionisticPropositionalCutElimination.modusPonens,
    implLeftCase, atomCase, Lemmatheca.ProofTheory.Intuitionistic.CutFree.Proof.identity]

theorem rightPacket_middle (p q : α) (h : p ≠ q) :
    (rightPacket p q).middle = conj (atom p) topFormula := by
  simp [rightPacket, extract, Lemmatheca.Entry.IntuitionisticPropositionalCutElimination.modusPonens,
    implRightSideCase, atomCase, Lemmatheca.ProofTheory.Intuitionistic.CutFree.Proof.identity, Ne.symm h]

def bottomPacket (C : PropFormula α) : Packet {falsum} ∅ C :=
  falsumCase {falsum} ∅ C (by simp)

theorem bottomPacket_middle (C : PropFormula α) :
    (bottomPacket C).middle = falsum := by
  simp [bottomPacket, falsumCase]

def topPacket (p : α) : Packet {atom p} ∅ (topFormula : PropFormula α) where
  middle := topFormula
  left := by exact .implRight (.falsumLeft (by simp))
  right := by exact .identity _ (by simp)
  support := by simp [topFormula, atoms]

def overlapBottomPacket (C : PropFormula α) : Packet {falsum} {falsum} C :=
  falsumCase {falsum} {falsum} C (by simp)

theorem overlapBottomPacket_middle (C : PropFormula α) :
    (overlapBottomPacket C).middle = falsum := by
  simp [overlapBottomPacket, falsumCase]

def overlapTopPacket (C : PropFormula α) : Packet {falsum} {falsum} C where
  middle := topFormula
  left := by exact .falsumLeft (by simp)
  right := by exact .falsumLeft (by simp)
  support := by simp [topFormula, atoms]

theorem overlap_middle_ne (C : PropFormula α) :
    (overlapBottomPacket C).middle ≠ (overlapTopPacket C).middle := by
  simp [overlapBottomPacket_middle, overlapTopPacket, topFormula]

end
end Lemmatheca.Entry.IntuitionisticPropositionalProofInterpolation
