import Lemmatheca.PropositionalWeakExcludedMiddle.Schemas

/-! The two schemas interderive by original intuitionistic deductions. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.WeakExcludedMiddle
open Lemmatheca.MathematicalLogic.Propositional
open Extensions
universe u
variable {α : Type u}

theorem wem_to_deMorgan (A B : PropFormula α) :
    Derives ∅ (.impl (wem A) (deMorgan A B)) := by
  unfold wem deMorgan
  apply Derives.implIntro
  apply Derives.implIntro
  apply Derives.disjElim (A := .neg A) (B := .neg (.neg A)) (.assumption (by simp))
  · exact .disjIntroLeft (.assumption (by simp))
  · apply Derives.disjIntroRight
    apply Derives.negIntro
    apply Derives.negElim (A := .neg A) ?_ (.assumption (by simp))
    apply Derives.negIntro
    exact .negElim (A := .conj A B)
      (.conjIntro (.assumption (by simp)) (.assumption (by simp))) (.assumption (by simp))

theorem deMorgan_to_wem (A : PropFormula α) :
    Derives ∅ (.impl (deMorgan A (.neg A)) (wem A)) := by
  have hn : Derives ∅ (.neg (.conj A (.neg A))) := by
    apply Derives.negIntro
    have hab : Derives (insert (.conj A (.neg A)) ∅) (.conj A (.neg A)) :=
      .assumption (by simp)
    exact .negElim (.conjElimLeft hab) (.conjElimRight hab)
  unfold deMorgan wem
  apply Derives.implIntro
  exact .implElim (.assumption (by simp)) (hn.weaken (Set.empty_subset _))

theorem deMorgan_schema_equivalence (Γ : Set (PropFormula α)) (C : PropFormula α) :
    SchemaConsequence axioms Γ C ↔ SchemaConsequence deMorganAxioms Γ C := by
  rw [schemaConsequence_iff_union, schemaConsequence_iff_union]
  constructor
  · intro h
    apply h.replace
    intro D hD
    rcases hD with hΓ | hW
    · exact .assumption (Or.inl hΓ)
    · obtain ⟨A, rfl⟩ := hW
      exact .implElim ((deMorgan_to_wem A).weaken (Set.empty_subset _))
        (.assumption (Or.inr ⟨(A, .neg A), rfl⟩))
  · intro h
    apply h.replace
    intro D hD
    rcases hD with hΓ | hD
    · exact .assumption (Or.inl hΓ)
    · obtain ⟨⟨A, B⟩, rfl⟩ := hD
      exact .implElim ((wem_to_deMorgan A B).weaken (Set.empty_subset _))
        (.assumption (Or.inr ⟨A, rfl⟩))

theorem excluded_middle_to_wem (A : PropFormula α) :
    Derives ∅ (.impl (.disj A (.neg A)) (wem A)) := by
  apply Derives.implIntro
  apply Derives.disjElim (A := A) (B := .neg A) (.assumption (by simp))
  · exact .disjIntroRight (.implElim ((double_negation_intro A).weaken (Set.empty_subset _))
      (.assumption (by simp)))
  · exact .disjIntroLeft (.assumption (by simp))

end Lemmatheca.ProofTheory.Intuitionistic.WeakExcludedMiddle
