import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction

namespace Lemmatheca.ProofTheory.Intuitionistic

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u}

/-- All excluded-middle instances in the fixed atom language. -/
def excludedMiddleSchema : Set (PropFormula α) := Set.range (fun A => disj A (neg A))

/-- All double-negation-elimination instances in the fixed atom language. -/
def doubleNegationSchema : Set (PropFormula α) :=
  Set.range (fun A => impl (neg (neg A)) A)

private abbrev NativeDerives {α : Type*} [DecidableEq α] :=
  Lemmatheca.MathematicalLogic.Propositional.Derives (α := α)

private theorem classical_from_assumptions [DecidableEq α]
    {Γ : Set (PropFormula α)} {A : PropFormula α} (h : Derives Γ A)
    {Δ : Finset (PropFormula α)} (hΓ : ∀ B ∈ Γ, NativeDerives Δ B) : NativeDerives Δ A := by
  induction h generalizing Δ with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact .conjIntro (ihA hΓ) (ihB hΓ)
  | conjElimLeft _ ih => exact .conjElimLeft (ih hΓ)
  | conjElimRight _ ih => exact .conjElimRight (ih hΓ)
  | disjIntroLeft _ ih => exact .disjIntroLeft (ih hΓ)
  | disjIntroRight _ ih => exact .disjIntroRight (ih hΓ)
  | disjElim _ _ _ ihAB ihA ihB =>
      apply Lemmatheca.MathematicalLogic.Propositional.Derives.disjElim (ihAB hΓ)
      · apply ihA
        intro X hX
        rcases Set.mem_insert_iff.mp hX with rfl | hX
        · exact .assumption (by simp)
        · exact (hΓ X hX).weaken (Finset.subset_insert _ _)
      · apply ihB
        intro X hX
        rcases Set.mem_insert_iff.mp hX with rfl | hX
        · exact .assumption (by simp)
        · exact (hΓ X hX).weaken (Finset.subset_insert _ _)
  | implIntro _ ih =>
      apply Lemmatheca.MathematicalLogic.Propositional.Derives.implIntro
      apply ih
      intro X hX
      rcases Set.mem_insert_iff.mp hX with rfl | hX
      · exact .assumption (by simp)
      · exact (hΓ X hX).weaken (Finset.subset_insert _ _)
  | implElim _ _ ihAB ihA => exact .implElim (ihAB hΓ) (ihA hΓ)
  | negIntro _ ih =>
      apply Lemmatheca.MathematicalLogic.Propositional.Derives.negIntro
      apply ih
      intro X hX
      rcases Set.mem_insert_iff.mp hX with rfl | hX
      · exact .assumption (by simp)
      · exact (hΓ X hX).weaken (Finset.subset_insert _ _)
  | negElim _ _ ihA ihN => exact .negElim (ihA hΓ) (ihN hΓ)
  | falsumElim _ ih => exact .falsumElim (ih hΓ)

private theorem classical_dne [DecidableEq α] (Γ : Finset (PropFormula α))
    (A : PropFormula α) : NativeDerives Γ (impl (neg (neg A)) A) := by
  apply Lemmatheca.MathematicalLogic.Propositional.Derives.implIntro
  apply Lemmatheca.MathematicalLogic.Propositional.Derives.classicalContradiction
  exact .negElim (A := neg A) (.assumption (by simp)) (.assumption (by simp))

private theorem native_to_dne [DecidableEq α] {Γ : Finset (PropFormula α)}
    {A : PropFormula α} (h : NativeDerives Γ A) :
    Derives ((Γ : Set (PropFormula α)) ∪ doubleNegationSchema) A := by
  induction h with
  | assumption hA => exact .assumption (Or.inl hA)
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB =>
      apply Derives.disjElim ihAB
      · simpa only [Finset.coe_insert, Set.insert_union] using ihA
      · simpa only [Finset.coe_insert, Set.insert_union] using ihB
  | implIntro _ ih =>
      apply Derives.implIntro
      simpa only [Finset.coe_insert, Set.insert_union] using ih
  | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
  | negIntro _ ih =>
      apply Derives.negIntro
      simpa only [Finset.coe_insert, Set.insert_union] using ih
  | negElim _ _ ihA ihN => exact .negElim ihA ihN
  | falsumElim _ ih => exact .falsumElim ih
  | @classicalContradiction Γ A _ ih =>
      have nn : Derives ((Γ : Set (PropFormula α)) ∪ doubleNegationSchema)
          (neg (neg A)) := .negIntro (by
        simpa only [Finset.coe_insert, Set.insert_union] using ih)
      exact .implElim (.assumption (Or.inr ⟨A, rfl⟩)) nn

theorem em_derives_dne (A : PropFormula α) :
    Derives excludedMiddleSchema (impl (neg (neg A)) A) := by
  apply Derives.implIntro
  apply Derives.disjElim (A := A) (B := neg A)
  · exact .assumption (by right; exact ⟨A, rfl⟩)
  · exact .assumption (by simp)
  · apply Derives.falsumElim
    exact .negElim (A := neg A) (.assumption (by simp)) (.assumption (by simp))

theorem dne_derives_em (A : PropFormula α) :
    Derives doubleNegationSchema (disj A (neg A)) := by
  exact .implElim (.assumption ⟨disj A (neg A), rfl⟩)
    ((double_negated_excluded_middle A).weaken (Set.empty_subset _))

theorem em_iff_dne (Γ : Set (PropFormula α)) (A : PropFormula α) :
    Derives (Γ ∪ excludedMiddleSchema) A ↔ Derives (Γ ∪ doubleNegationSchema) A := by
  constructor
  · intro h
    apply h.replace
    intro B hB
    rcases hB with hB | ⟨X, rfl⟩
    · exact .assumption (Or.inl hB)
    · exact (dne_derives_em X).weaken (Set.subset_union_right)
  · intro h
    apply h.replace
    intro B hB
    rcases hB with hB | ⟨X, rfl⟩
    · exact .assumption (Or.inl hB)
    · exact (em_derives_dne X).weaken (Set.subset_union_right)

theorem classical_iff_dne [DecidableEq α] (Γ : Finset (PropFormula α))
    (A : PropFormula α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives Γ A ↔
      Derives ((Γ : Set (PropFormula α)) ∪ doubleNegationSchema) A := by
  constructor
  · exact native_to_dne
  · intro h
    apply classical_from_assumptions h
    intro B hB
    rcases hB with hB | ⟨X, rfl⟩
    · exact .assumption hB
    · exact classical_dne Γ X

theorem classical_iff_em [DecidableEq α] (Γ : Finset (PropFormula α))
    (A : PropFormula α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives Γ A ↔
      Derives ((Γ : Set (PropFormula α)) ∪ excludedMiddleSchema) A := by
  exact (classical_iff_dne Γ A).trans (em_iff_dne (Γ : Set (PropFormula α)) A).symm

theorem schemas_boolean_valid {A : PropFormula α}
    (h : A ∈ excludedMiddleSchema ∪ doubleNegationSchema) : Tautology A := by
  rcases h with ⟨B, rfl⟩ | ⟨B, rfl⟩
  · intro v
    simp [Satisfies, eval]
  · intro v
    simp [Satisfies, eval]

end Lemmatheca.ProofTheory.Intuitionistic
