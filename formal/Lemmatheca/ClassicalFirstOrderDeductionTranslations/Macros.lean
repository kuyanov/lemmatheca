import Lemmatheca.ClassicalFirstOrderDeductionTranslations.Syntax

/-! Actual derived rules for the exact small-syntax abbreviations. -/
namespace Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {c e : Bool}
noncomputable section
local instance macrosFullFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (Formula K δ) := Classical.decEq _
local instance macrosSmallFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (K.Formula δ) := Classical.decEq _

/-- Implication to falsum, distinct from the primitive full negation constructor. -/
def codeNeg {n} (A : BF L α n) : BF L α n := .impl A .falsum
/-- The exact included small conjunction abbreviation. -/
def codeConj {n} (A B : BF L α n) : BF L α n := codeNeg (.impl A (codeNeg B))
/-- The exact included small disjunction abbreviation. -/
def codeDisj {n} (A B : BF L α n) : BF L α n := .impl (codeNeg A) B
/-- The exact included small existential abbreviation. -/
def codeEx {n} (B : BF L α (n+1)) : BF L α n := codeNeg (.all (codeNeg B))

open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction (Derivation)

private def useBranch {Γ Δ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α}
    {A C : Formula L α} (q : Derivation c e L (insert A Γ) C)
    (p : Derivation c e L Δ A) (hΓ : Γ ⊆ Δ) : Derivation c e L Δ C :=
  q.replace fun B hB => by
    by_cases hBA : B = A
    · subst B; exact p
    · exact .assumption (hΓ ((Finset.mem_insert.mp hB).resolve_left hBA))

namespace Raw
variable {Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α} {A B C : Formula L α}

def negToCode (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (.neg A)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (codeNeg A) := by
  exact .impIntro (.negElim (.assumption (Finset.mem_insert_self _ _))
    (p.weaken (Finset.subset_insert _ _)))
def codeToNeg (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (codeNeg A)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (.neg A) := by
  exact .negIntro (.impElim (p.weaken (Finset.subset_insert _ _))
    (.assumption (Finset.mem_insert_self _ _)))

def conjIntro (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ A) (q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ B) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (codeConj A B) := by
  apply Derivation.impIntro
  exact .impElim (.impElim (.assumption (Finset.mem_insert_self _ _))
    (p.weaken (Finset.subset_insert _ _))) (q.weaken (Finset.subset_insert _ _))
def conjLeft (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ (codeConj A B)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ A := by
  apply Derivation.classicalContradiction rfl
  have h : Derivation true e L (insert (.neg A) Γ) (.impl A (codeNeg B)) := by
    apply Derivation.impIntro
    apply Derivation.impIntro
    exact .negElim (A := A) (.assumption (by simp)) (.assumption (by simp))
  exact .impElim (p.weaken (Finset.subset_insert _ _)) h
def conjRight (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ (codeConj A B)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ B := by
  apply Derivation.classicalContradiction rfl
  have h : Derivation true e L (insert (.neg B) Γ) (.impl A (codeNeg B)) := by
    apply Derivation.impIntro
    apply Derivation.impIntro
    exact .negElim (A := B) (.assumption (by simp)) (.assumption (by simp))
  exact .impElim (p.weaken (Finset.subset_insert _ _)) h

def disjLeft (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (codeDisj A B) := by
  apply Derivation.impIntro
  exact .falsumElim (.impElim (.assumption (Finset.mem_insert_self _ _))
    (p.weaken (Finset.subset_insert _ _)))
def disjRight (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ B) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (codeDisj A B) := by
  exact .impIntro (p.weaken (Finset.subset_insert _ _))
def disjElim (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ (codeDisj A B))
    (q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L (insert A Γ) C)
    (r : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L (insert B Γ) C) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ C := by
  apply Derivation.classicalContradiction rfl
  let Δ := insert (.neg C) Γ
  have hNA : Derivation true e L Δ (codeNeg A) := by
    apply Derivation.impIntro
    have hC := useBranch q (Derivation.assumption (Finset.mem_insert_self A Δ))
      (by intro F hF; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hF))
    exact .negElim hC (.assumption (by simp [Δ]))
  have hB : Derivation true e L Δ B :=
    .impElim (p.weaken (Finset.subset_insert _ _)) hNA
  have hC := useBranch r hB (Finset.subset_insert _ _)
  exact .negElim hC (.assumption (Finset.mem_insert_self _ _))

def exIntro {D : BF L α 1} (t : L.Term α)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (D.instantiate t)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation c e L Γ (codeEx D) := by
  apply Derivation.impIntro
  exact .impElim (Derivation.allElim t (.assumption (Finset.mem_insert_self _ _)))
    (p.weaken (Finset.subset_insert _ _))

def exElim {D : BF L α 1} (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ (codeEx D))
    (q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L (insert D.toFormula (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ))
      (C.rename Sum.inl)) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true e L Γ C := by
  apply Derivation.classicalContradiction rfl
  let Δ := insert (.neg C) Γ
  have hu : Derivation true e L Δ (.all (codeNeg D)) := by
    apply Derivation.allIntro
    apply Derivation.impIntro
    have hΓ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ ⊆
        Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Δ :=
      Finset.image_subset_image (Finset.subset_insert _ _)
    have hC := q.weaken (Finset.insert_subset_insert _ hΓ)
    have hneg : Derivation true e L
        (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Δ)
        ((.neg C : Formula L α).rename Sum.inl) :=
      .assumption (Finset.mem_image.mpr ⟨.neg C, Finset.mem_insert_self _ _, rfl⟩)
    exact .negElim hC (hneg.weaken (Finset.subset_insert _ _))
  exact .impElim (p.weaken (Finset.subset_insert _ _)) hu

end Raw
end
end Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
