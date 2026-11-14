import Lemmatheca.PropositionalWeakExcludedMiddle.Schemas

/-! Linearity and implication–disjunction as finite added-axiom extensions of IPC. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Dummett
open Lemmatheca.MathematicalLogic.Propositional
open Extensions
universe u v

def linearity {α : Type u} (A B : PropFormula α) : PropFormula α :=
  .disj (.impl A B) (.impl B A)

def axioms {α : Type u} : Set (PropFormula α) :=
  Set.range (fun ab : PropFormula α × PropFormula α => linearity ab.1 ab.2)

def distribution {α : Type u} (A B C : PropFormula α) : PropFormula α :=
  .impl (.impl A (.disj B C)) (.disj (.impl A B) (.impl A C))

def distributionAxioms {α : Type u} : Set (PropFormula α) :=
  Set.range (fun abc : PropFormula α × PropFormula α × PropFormula α =>
    distribution abc.1 abc.2.1 abc.2.2)

theorem linearity_substitute {α : Type u} {β : Type v} (σ : α → PropFormula β)
    (A B : PropFormula α) :
    subst σ (linearity A B) = linearity (subst σ A) (subst σ B) := by
  rfl

theorem wem_from_linearity {α : Type u} (A : PropFormula α) :
    Derives ∅ (.impl (linearity A (.neg A)) (WeakExcludedMiddle.wem A)) := by
  unfold linearity WeakExcludedMiddle.wem
  apply Derives.implIntro
  apply Derives.disjElim (A := .impl A (.neg A)) (B := .impl (.neg A) A)
    (.assumption (by simp))
  · apply Derives.disjIntroLeft
    apply Derives.negIntro
    exact .negElim (A := A) (.assumption (by simp))
      (.implElim (A := A) (.assumption (by simp)) (.assumption (by simp)))
  · apply Derives.disjIntroRight
    apply Derives.negIntro
    exact .negElim (A := A)
      (.implElim (A := .neg A) (.assumption (by simp)) (.assumption (by simp)))
      (.assumption (by simp))

theorem kc_to_lc {α : Type u} (Γ : Set (PropFormula α)) (C : PropFormula α) :
    SchemaConsequence WeakExcludedMiddle.axioms Γ C → SchemaConsequence axioms Γ C := by
  rw [schemaConsequence_iff_union, schemaConsequence_iff_union]
  intro h
  apply h.replace
  intro D hD
  rcases hD with hΓ | hW
  · exact .assumption (Or.inl hΓ)
  · obtain ⟨A, rfl⟩ := hW
    exact .implElim ((wem_from_linearity A).weaken (Set.empty_subset _))
      (.assumption (Or.inr ⟨(A, .neg A), rfl⟩))

theorem distribution_from_linearity {α : Type u} (A B C : PropFormula α) :
    Derives ∅ (.impl (linearity B C) (distribution A B C)) := by
  unfold linearity distribution
  apply Derives.implIntro
  apply Derives.implIntro
  apply Derives.disjElim (A := .impl B C) (B := .impl C B) (.assumption (by simp))
  · apply Derives.disjIntroRight
    apply Derives.implIntro
    apply Derives.disjElim (A := B) (B := C)
      (.implElim (A := A) (.assumption (by simp)) (.assumption (by simp)))
    · exact .implElim (A := B) (.assumption (by simp)) (.assumption (by simp))
    · exact .assumption (by simp)
  · apply Derives.disjIntroLeft
    apply Derives.implIntro
    apply Derives.disjElim (A := B) (B := C)
      (.implElim (A := A) (.assumption (by simp)) (.assumption (by simp)))
    · exact .assumption (by simp)
    · exact .implElim (A := C) (.assumption (by simp)) (.assumption (by simp))

theorem linearity_from_distribution {α : Type u} (B C : PropFormula α) :
    Derives ∅ (.impl (distribution (.disj B C) B C) (linearity B C)) := by
  unfold distribution linearity
  apply Derives.implIntro
  apply Derives.disjElim (A := .impl (.disj B C) B) (B := .impl (.disj B C) C)
    (.implElim (.assumption (by simp))
      ((identity (.disj B C)).weaken (Set.empty_subset _)))
  · apply Derives.disjIntroRight
    apply Derives.implIntro
    exact .implElim (A := .disj B C) (.assumption (by simp)) (.disjIntroRight (.assumption (by simp)))
  · apply Derives.disjIntroLeft
    apply Derives.implIntro
    exact .implElim (A := .disj B C) (.assumption (by simp)) (.disjIntroLeft (.assumption (by simp)))

theorem schema_equivalent {α : Type u} (Γ : Set (PropFormula α)) (D : PropFormula α) :
    SchemaConsequence axioms Γ D ↔ SchemaConsequence distributionAxioms Γ D := by
  rw [schemaConsequence_iff_union, schemaConsequence_iff_union]
  constructor
  · intro h
    apply h.replace
    intro E hE
    rcases hE with hΓ | hL
    · exact .assumption (Or.inl hΓ)
    · obtain ⟨⟨B, C⟩, rfl⟩ := hL
      exact .implElim ((linearity_from_distribution B C).weaken (Set.empty_subset _))
        (.assumption (Or.inr ⟨(.disj B C, B, C), rfl⟩))
  · intro h
    apply h.replace
    intro E hE
    rcases hE with hΓ | hH
    · exact .assumption (Or.inl hΓ)
    · obtain ⟨⟨A, B, C⟩, rfl⟩ := hH
      exact .implElim ((distribution_from_linearity A B C).weaken (Set.empty_subset _))
        (.assumption (Or.inr ⟨(B, C), rfl⟩))

theorem instance_theorem {α : Type u} (A B : PropFormula α) :
    SchemaConsequence axioms ∅ (linearity A B) := by
  apply (schemaConsequence_iff_union _ _ _).mpr
  exact .assumption (Or.inr ⟨(A, B), rfl⟩)

theorem excluded_middle_implies_linearity {α : Type u} (A B : PropFormula α) :
    Derives ∅ (.impl (.disj A (.neg A)) (linearity A B)) := by
  unfold linearity
  apply Derives.implIntro
  apply Derives.disjElim (A := A) (B := .neg A) (.assumption (by simp))
  · apply Derives.disjIntroRight
    apply Derives.implIntro
    exact .assumption (by simp)
  · apply Derives.disjIntroLeft
    apply Derives.implIntro
    exact .falsumElim (.negElim (A := A) (.assumption (by simp)) (.assumption (by simp)))

end Lemmatheca.ProofTheory.Intuitionistic.Dummett
