import Lemmatheca.IntuitionisticPropositionalSequents.Translations
import Lemmatheca.IntuitionisticPropositionalDeduction.Expansion

/-! Genuine cut-free certificates on the native constructive syntax. Left
principals are retained. There is no cut or weakening constructor. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.CutFree

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

inductive Proof : Finset (PropFormula α) → PropFormula α → Type u
  | atom {Γ a} : atom a ∈ Γ → Proof Γ (atom a)
  | falsumLeft {Γ C} : falsum ∈ Γ → Proof Γ C
  | conjLeft {Γ A B C} : conj A B ∈ Γ → Proof (insert A (insert B Γ)) C → Proof Γ C
  | conjRight {Γ A B} : Proof Γ A → Proof Γ B → Proof Γ (conj A B)
  | disjLeft {Γ A B C} : disj A B ∈ Γ → Proof (insert A Γ) C →
      Proof (insert B Γ) C → Proof Γ C
  | disjRightLeft {Γ A B} : Proof Γ A → Proof Γ (disj A B)
  | disjRightRight {Γ A B} : Proof Γ B → Proof Γ (disj A B)
  | implLeft {Γ A B C} : impl A B ∈ Γ → Proof Γ A → Proof (insert B Γ) C → Proof Γ C
  | implRight {Γ A B} : Proof (insert A Γ) B → Proof Γ (impl A B)
  | negLeft {Γ A C} : neg A ∈ Γ → Proof Γ A → Proof Γ C
  | negRight {Γ A} : Proof (insert A Γ) falsum → Proof Γ (neg A)

/-- Transport a certificate along inclusion of its allowed assumptions. -/
def Proof.weaken {Γ Δ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) (hΓ : Γ ⊆ Δ) : Proof Δ A :=
  match p with
  | .atom h => .atom (hΓ h)
  | .falsumLeft h => .falsumLeft (hΓ h)
  | .conjLeft h q => .conjLeft (hΓ h)
      (q.weaken (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hΓ)))
  | .conjRight p q => .conjRight (p.weaken hΓ) (q.weaken hΓ)
  | .disjLeft h p q => .disjLeft (hΓ h)
      (p.weaken (Finset.insert_subset_insert _ hΓ))
      (q.weaken (Finset.insert_subset_insert _ hΓ))
  | .disjRightLeft p => .disjRightLeft (p.weaken hΓ)
  | .disjRightRight p => .disjRightRight (p.weaken hΓ)
  | .implLeft h p q => .implLeft (hΓ h) (p.weaken hΓ)
      (q.weaken (Finset.insert_subset_insert _ hΓ))
  | .implRight p => .implRight (p.weaken (Finset.insert_subset_insert _ hΓ))
  | .negLeft h p => .negLeft (hΓ h) (p.weaken hΓ)
  | .negRight p => .negRight (p.weaken (Finset.insert_subset_insert _ hΓ))

/-- Compound identity is derived from atomic identity and the primitive rules. -/
def Proof.identity {Γ : Finset (PropFormula α)} (A : PropFormula α)
    (hA : A ∈ Γ) : Proof Γ A :=
  match A with
  | .atom _ => .atom hA
  | .falsum => .falsumLeft hA
  | .conj X Y => .conjLeft hA
      (.conjRight (Proof.identity X (by simp)) (Proof.identity Y (by simp)))
  | .disj X Y => .disjLeft hA
      (.disjRightLeft (Proof.identity X (by simp)))
      (.disjRightRight (Proof.identity Y (by simp)))
  | .impl X Y => .implRight
      (.implLeft (A := X) (B := Y) (Finset.mem_insert_of_mem hA)
        (Proof.identity X (by simp)) (Proof.identity Y (by simp)))
  | .neg X => .negRight
      (.negLeft (Finset.mem_insert_of_mem hA) (Proof.identity X (by simp)))

/-- Falsum elimination is a transformation of cut-free trees. -/
def Proof.explode {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : Proof Γ falsum) : Proof Γ C :=
  match p with
  | .falsumLeft h => .falsumLeft h
  | .conjLeft h q => .conjLeft h q.explode
  | .disjLeft h p q => .disjLeft h p.explode q.explode
  | .implLeft h p q => .implLeft h p q.explode
  | .negLeft h q => .negLeft h q

def Proof.invertConj {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (p : Proof Γ (conj A B)) : Proof Γ A × Proof Γ B :=
  match p with
  | .falsumLeft h => ⟨.falsumLeft h, .falsumLeft h⟩
  | .conjRight p q => ⟨p, q⟩
  | .conjLeft h q =>
      let ab := q.invertConj
      ⟨.conjLeft h ab.1, .conjLeft h ab.2⟩
  | .disjLeft h p q =>
      let ab := p.invertConj
      let cd := q.invertConj
      ⟨.disjLeft h ab.1 cd.1, .disjLeft h ab.2 cd.2⟩
  | .implLeft h p q =>
      let ab := q.invertConj
      ⟨.implLeft h p ab.1, .implLeft h p ab.2⟩
  | .negLeft h q => ⟨.negLeft h q, .negLeft h q⟩

def Proof.invertImpl {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (p : Proof Γ (impl A B)) : Proof (insert A Γ) B :=
  match p with
  | .falsumLeft h => .falsumLeft (Finset.mem_insert_of_mem h)
  | .implRight q => q
  | .conjLeft h q =>
      .conjLeft (Finset.mem_insert_of_mem h)
        (by simpa only [Finset.insert_comm] using q.invertImpl)
  | .disjLeft h p q =>
      .disjLeft (Finset.mem_insert_of_mem h)
        (by simpa only [Finset.insert_comm] using p.invertImpl)
        (by simpa only [Finset.insert_comm] using q.invertImpl)
  | .implLeft h p q =>
      .implLeft (Finset.mem_insert_of_mem h) (p.weaken (Finset.subset_insert _ _))
        (by simpa only [Finset.insert_comm] using q.invertImpl)
  | .negLeft h q =>
      .negLeft (Finset.mem_insert_of_mem h) (q.weaken (Finset.subset_insert _ _))

def Proof.invertNeg {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ (neg A)) : Proof (insert A Γ) falsum :=
  match p with
  | .falsumLeft h => .falsumLeft (Finset.mem_insert_of_mem h)
  | .negRight q => q
  | .conjLeft h q =>
      .conjLeft (Finset.mem_insert_of_mem h)
        (by simpa only [Finset.insert_comm] using q.invertNeg)
  | .disjLeft h p q =>
      .disjLeft (Finset.mem_insert_of_mem h)
        (by simpa only [Finset.insert_comm] using p.invertNeg)
        (by simpa only [Finset.insert_comm] using q.invertNeg)
  | .implLeft h p q =>
      .implLeft (Finset.mem_insert_of_mem h) (p.weaken (Finset.subset_insert _ _))
        (by simpa only [Finset.insert_comm] using q.invertNeg)
  | .negLeft h q =>
      .negLeft (Finset.mem_insert_of_mem h) (q.weaken (Finset.subset_insert _ _))

end Lemmatheca.ProofTheory.Intuitionistic.CutFree
