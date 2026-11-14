import Lemmatheca.IntuitionisticPropositionalProofInterpolation.Packet

/-! Each case pins its native middle formula transparently. Both actual factor
trees and their atom bounds follow the retained-rule Maehara construction. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Interpolation
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u
variable {α : Type u} [DecidableEq α]

noncomputable section

private theorem atoms_mem_context {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (hA : A ∈ Γ) : atoms A ⊆ contextAtoms Γ := by
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨A,hA,ha⟩

@[simp] private theorem context_insert (A : PropFormula α) (Γ : Finset (PropFormula α)) :
    contextAtoms (insert A Γ) = atoms A ∪ contextAtoms Γ := by simp [contextAtoms]

private theorem absorb {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (h : atoms A ⊆ contextAtoms Γ) : contextAtoms (insert A Γ) = contextAtoms Γ := by
  rw [context_insert,Finset.union_eq_right.mpr h]

private theorem binary_atoms {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (h : atoms A ∪ atoms B ⊆ contextAtoms Γ) :
    contextAtoms (insert A (insert B Γ)) = contextAtoms Γ := by
  rw [context_insert,context_insert,← Finset.union_assoc,Finset.union_eq_right.mpr h]

private def topProof (Γ : Finset (PropFormula α)) : CutFree.Proof Γ (topFormula : PropFormula α) :=
  .implRight (.falsumLeft (Finset.mem_insert_self _ _))

private def projectLeft {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (h : conj A B ∈ Γ) : CutFree.Proof Γ A :=
  .conjLeft h (CutFree.Proof.identity A (by simp))

private def projectRight {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (h : conj A B ∈ Γ) : CutFree.Proof Γ B :=
  .conjLeft h (CutFree.Proof.identity B (by simp))

private def pasteSame {Γ : Finset (PropFormula α)} {A C : PropFormula α}
    (p : CutFree.Proof Γ A) (q : CutFree.Proof (insert A Γ) C) : CutFree.Proof Γ C :=
  (Finset.union_self Γ) ▸ p.cut q

private def throughLeft {Γ : Finset (PropFormula α)} {A B C : PropFormula α}
    (p : CutFree.Proof (insert A Γ) C) : CutFree.Proof (insert (conj A B) Γ) C :=
  pasteSame (projectLeft (Finset.mem_insert_self _ _))
    (p.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))

private def throughRight {Γ : Finset (PropFormula α)} {A B C : PropFormula α}
    (p : CutFree.Proof (insert B Γ) C) : CutFree.Proof (insert (conj A B) Γ) C :=
  pasteSame (projectRight (Finset.mem_insert_self _ _))
    (p.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))

def atomCase (L R : Finset (PropFormula α)) (a : α)
    (h : atom a ∈ L ∪ R) : Packet L R (atom a) :=
  if ha : atom a ∈ L then
    { middle := atom a
      left := .atom ha
      right := .atom (Finset.mem_insert_self _ _)
      support := by
        intro x hx
        have he : x = a := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_inter.mpr ⟨atoms_mem_context ha (by simp [atoms]),Finset.mem_union_right _ (by simp [atoms])⟩ }
  else
    { middle := topFormula
      left := topProof L
      right := .atom (Finset.mem_insert_of_mem ((Finset.mem_union.mp h).resolve_left ha))
      support := by simp [topFormula,atoms] }

def falsumCase (L R : Finset (PropFormula α)) (C : PropFormula α)
    (h : falsum ∈ L ∪ R) : Packet L R C :=
  if hb : falsum ∈ L then
    { middle := falsum
      left := .falsumLeft hb
      right := .falsumLeft (Finset.mem_insert_self _ _)
      support := by simp [atoms] }
  else
    { middle := topFormula
      left := topProof L
      right := .falsumLeft (Finset.mem_insert_of_mem ((Finset.mem_union.mp h).resolve_left hb))
      support := by simp [topFormula,atoms] }

def conjLeftCase {L R : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : conj A B ∈ L) (w : Packet (insert A (insert B L)) R C) : Packet L R C where
  middle := w.middle
  left := .conjLeft h w.left
  right := w.right
  support := by
    simpa only [binary_atoms (atoms_mem_context h)] using w.support

def conjRightSideCase {L R : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : conj A B ∈ R) (w : Packet L (insert A (insert B R)) C) : Packet L R C where
  middle := w.middle
  left := w.left
  right := by
    apply CutFree.Proof.conjLeft (Finset.mem_insert_of_mem h)
    simpa only [Finset.insert_comm] using w.right
  support := by
    simpa only [binary_atoms (atoms_mem_context h)] using w.support

def conjRightCase {L R : Finset (PropFormula α)} {A B : PropFormula α}
    (wa : Packet L R A) (wb : Packet L R B) : Packet L R (conj A B) where
  middle := conj wa.middle wb.middle
  left := .conjRight wa.left wb.left
  right := .conjRight (throughLeft wa.right) (throughRight wb.right)
  support := by
    intro x hx
    rcases Finset.mem_union.mp hx with ha | hb
    · have hs := wa.support ha
      simp only [Finset.mem_inter,Finset.mem_union,atoms] at hs ⊢
      tauto
    · have hs := wb.support hb
      simp only [Finset.mem_inter,Finset.mem_union,atoms] at hs ⊢
      tauto

def disjRightLeftCase {L R : Finset (PropFormula α)} {A B : PropFormula α}
    (w : Packet L R A) : Packet L R (disj A B) where
  middle := w.middle
  left := w.left
  right := .disjRightLeft w.right
  support := by
    intro x hx
    have hs := w.support hx
    simp only [Finset.mem_inter,Finset.mem_union,atoms] at hs ⊢
    tauto

def disjRightRightCase {L R : Finset (PropFormula α)} {A B : PropFormula α}
    (w : Packet L R B) : Packet L R (disj A B) where
  middle := w.middle
  left := w.left
  right := .disjRightRight w.right
  support := by
    intro x hx
    have hs := w.support hx
    simp only [Finset.mem_inter,Finset.mem_union,atoms] at hs ⊢
    tauto

def disjLeftCase {L R : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : disj A B ∈ L) (wa : Packet (insert A L) R C) (wb : Packet (insert B L) R C) :
    Packet L R C where
  middle := disj wa.middle wb.middle
  left := .disjLeft h (.disjRightLeft wa.left) (.disjRightRight wb.left)
  right := .disjLeft (Finset.mem_insert_self _ _)
    (wa.right.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
    (wb.right.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
  support := by
    have ha := absorb (Finset.subset_union_left.trans (atoms_mem_context h))
    have hb := absorb (Finset.subset_union_right.trans (atoms_mem_context h))
    intro x hx
    rcases Finset.mem_union.mp hx with hj | hk
    · simpa only [ha] using wa.support hj
    · simpa only [hb] using wb.support hk

def disjRightSideCase {L R : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : disj A B ∈ R) (wa : Packet L (insert A R) C) (wb : Packet L (insert B R) C) :
    Packet L R C where
  middle := conj wa.middle wb.middle
  left := .conjRight wa.left wb.left
  right := by
    apply CutFree.Proof.disjLeft (Finset.mem_insert_of_mem h)
    · simpa only [Finset.insert_comm] using throughLeft (B := wb.middle) wa.right
    · simpa only [Finset.insert_comm] using throughRight (A := wa.middle) wb.right
  support := by
    have ha := absorb (Finset.subset_union_left.trans (atoms_mem_context h))
    have hb := absorb (Finset.subset_union_right.trans (atoms_mem_context h))
    intro x hx
    rcases Finset.mem_union.mp hx with hj | hk
    · simpa only [ha] using wa.support hj
    · simpa only [hb] using wb.support hk

/-- The antecedent packet has the reversed sides R|L and conclusion A. -/
def implLeftCase {L R : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : impl A B ∈ L) (wa : Packet R L A) (wb : Packet (insert B L) R C) :
    Packet L R C where
  middle := impl wa.middle wb.middle
  left := by
    apply CutFree.Proof.implRight
    apply CutFree.Proof.implLeft (Finset.mem_insert_of_mem h) wa.right
    simpa only [Finset.insert_comm] using wb.left.weaken (Finset.subset_insert wa.middle _)
  right := .implLeft (Finset.mem_insert_self _ _)
    (wa.left.weaken (Finset.subset_insert _ _))
    (wb.right.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
  support := by
    have ha : atoms A ⊆ contextAtoms L := Finset.subset_union_left.trans (atoms_mem_context h)
    have hb : atoms B ⊆ contextAtoms L := Finset.subset_union_right.trans (atoms_mem_context h)
    intro x hx
    rcases Finset.mem_union.mp hx with hj | hk
    · have hs := Finset.mem_inter.mp (wa.support hj)
      rcases hs with ⟨hr,hl⟩
      exact Finset.mem_inter.mpr ⟨(Finset.mem_union.mp hl).elim id (fun hx => ha hx),Finset.mem_union_left _ hr⟩
    · simpa only [absorb hb] using wb.support hk

def implRightSideCase {L R : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : impl A B ∈ R) (wa : Packet L R A) (wb : Packet L (insert B R) C) :
    Packet L R C where
  middle := conj wa.middle wb.middle
  left := .conjRight wa.left wb.left
  right := by
    apply CutFree.Proof.implLeft (Finset.mem_insert_of_mem h) (throughLeft wa.right)
    simpa only [Finset.insert_comm] using throughRight (A := wa.middle) wb.right
  support := by
    have ha : atoms A ⊆ contextAtoms R := Finset.subset_union_left.trans (atoms_mem_context h)
    have hb : atoms B ⊆ contextAtoms R := Finset.subset_union_right.trans (atoms_mem_context h)
    intro x hx
    rcases Finset.mem_union.mp hx with hj | hk
    · have hs := Finset.mem_inter.mp (wa.support hj)
      exact Finset.mem_inter.mpr ⟨hs.1,Finset.mem_union_left _ ((Finset.mem_union.mp hs.2).elim id (fun hx => ha hx))⟩
    · simpa only [absorb hb] using wb.support hk

def negLeftCase {L R : Finset (PropFormula α)} {A C : PropFormula α}
    (h : neg A ∈ L) (w : Packet R L A) : Packet L R C where
  middle := neg w.middle
  left := .negRight (.negLeft (Finset.mem_insert_of_mem h) w.right)
  right := .negLeft (Finset.mem_insert_self _ _) (w.left.weaken (Finset.subset_insert _ _))
  support := by
    have ha : atoms A ⊆ contextAtoms L := by simpa only [atoms] using atoms_mem_context h
    intro x hx
    have hs := Finset.mem_inter.mp (w.support hx)
    exact Finset.mem_inter.mpr ⟨(Finset.mem_union.mp hs.2).elim id (fun hx => ha hx),Finset.mem_union_left _ hs.1⟩

def negRightSideCase {L R : Finset (PropFormula α)} {A C : PropFormula α}
    (h : neg A ∈ R) (w : Packet L R A) : Packet L R C where
  middle := w.middle
  left := w.left
  right := .negLeft (Finset.mem_insert_of_mem h) w.right
  support := by
    have ha : atoms A ⊆ contextAtoms R := by simpa only [atoms] using atoms_mem_context h
    intro x hx
    have hs := Finset.mem_inter.mp (w.support hx)
    exact Finset.mem_inter.mpr ⟨hs.1,Finset.mem_union_left _ ((Finset.mem_union.mp hs.2).elim id (fun hx => ha hx))⟩

def implRightCase {L R : Finset (PropFormula α)} {A B : PropFormula α}
    (w : Packet L (insert A R) B) : Packet L R (impl A B) where
  middle := w.middle
  left := w.left
  right := by
    apply CutFree.Proof.implRight
    simpa only [Finset.insert_comm] using w.right
  support := by
    intro x hx
    have hs := w.support hx
    simp only [context_insert,atoms,Finset.mem_inter,Finset.mem_union] at hs ⊢
    tauto

def negRightCase {L R : Finset (PropFormula α)} {A : PropFormula α}
    (w : Packet L (insert A R) falsum) : Packet L R (neg A) where
  middle := w.middle
  left := w.left
  right := by
    apply CutFree.Proof.negRight
    simpa only [Finset.insert_comm] using w.right
  support := by
    intro x hx
    have hs := w.support hx
    simp only [context_insert,atoms,Finset.union_empty,Finset.mem_inter,Finset.mem_union] at hs ⊢
    tauto

end
end Lemmatheca.ProofTheory.Intuitionistic.Interpolation
