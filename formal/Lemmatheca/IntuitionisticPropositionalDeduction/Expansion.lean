import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction

namespace Lemmatheca.ProofTheory.Intuitionistic

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u}

/-- Remove primitive negation, replacing it by implication to falsum. -/
def expandNegation : PropFormula α → PropFormula α
  | .atom p => .atom p
  | .falsum => .falsum
  | .neg A => .impl (expandNegation A) .falsum
  | .conj A B => .conj (expandNegation A) (expandNegation B)
  | .disj A B => .disj (expandNegation A) (expandNegation B)
  | .impl A B => .impl (expandNegation A) (expandNegation B)

/-- Formulas using only atoms, falsum, conjunction, disjunction and implication. -/
def NegationFree : PropFormula α → Prop
  | .atom _ | .falsum => True
  | .neg _ => False
  | .conj A B | .disj A B | .impl A B => NegationFree A ∧ NegationFree B

/-- The primitive intuitionistic rules without the two primitive-negation rules. -/
inductive CoreDerives : Set (PropFormula α) → PropFormula α → Prop
  | assumption {Γ A} : A ∈ Γ → CoreDerives Γ A
  | conjIntro {Γ A B} : CoreDerives Γ A → CoreDerives Γ B → CoreDerives Γ (conj A B)
  | conjElimLeft {Γ A B} : CoreDerives Γ (conj A B) → CoreDerives Γ A
  | conjElimRight {Γ A B} : CoreDerives Γ (conj A B) → CoreDerives Γ B
  | disjIntroLeft {Γ A B} : CoreDerives Γ A → CoreDerives Γ (disj A B)
  | disjIntroRight {Γ A B} : CoreDerives Γ B → CoreDerives Γ (disj A B)
  | disjElim {Γ A B C} : CoreDerives Γ (disj A B) →
      CoreDerives (insert A Γ) C → CoreDerives (insert B Γ) C → CoreDerives Γ C
  | implIntro {Γ A B} : CoreDerives (insert A Γ) B → CoreDerives Γ (impl A B)
  | implElim {Γ A B} : CoreDerives Γ (impl A B) → CoreDerives Γ A → CoreDerives Γ B
  | falsumElim {Γ A} : CoreDerives Γ falsum → CoreDerives Γ A

theorem expandNegation_negationFree (A : PropFormula α) :
    NegationFree (expandNegation A) := by
  induction A <;> simp_all [expandNegation, NegationFree]

theorem expandNegation_atoms [DecidableEq α] (A : PropFormula α) :
    atoms (expandNegation A) = atoms A := by
  induction A <;> simp_all [expandNegation, atoms]

theorem expandNegation_idempotent (A : PropFormula α) :
    expandNegation (expandNegation A) = expandNegation A := by
  induction A <;> simp_all [expandNegation]

theorem CoreDerives.to_derives {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : CoreDerives Γ A) : Derives Γ A := by
  induction h with
  | assumption hA => exact .assumption hA
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB => exact .disjElim ihAB ihA ihB
  | implIntro _ ih => exact .implIntro ih
  | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
  | falsumElim _ ih => exact .falsumElim ih

theorem Derives.expandNegation {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) : CoreDerives (expandNegation '' Γ) (expandNegation A) := by
  induction h with
  | assumption hA => exact .assumption (Set.mem_image_of_mem _ hA)
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB =>
      apply CoreDerives.disjElim ihAB
      · simpa only [Set.image_insert_eq] using ihA
      · simpa only [Set.image_insert_eq] using ihB
  | implIntro _ ih =>
      apply CoreDerives.implIntro
      simpa only [Set.image_insert_eq] using ih
  | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
  | negIntro _ ih =>
      apply CoreDerives.implIntro
      simpa only [Set.image_insert_eq, Lemmatheca.ProofTheory.Intuitionistic.expandNegation] using ih
  | negElim _ _ ihA ihN => exact .implElim ihN ihA
  | falsumElim _ ih => exact .falsumElim ih

private theorem expandNegation_context_iff (A : PropFormula α) :
    ∀ Γ : Set (PropFormula α), Derives Γ A ↔ Derives Γ (expandNegation A) := by
  induction A with
  | atom p => intro Γ; rfl
  | falsum => intro Γ; rfl
  | neg A ih =>
      intro Γ
      change Derives Γ (neg A) ↔ Derives Γ (impl (expandNegation A) falsum)
      constructor
      · intro h
        apply Derives.implIntro
        exact .negElim ((ih _).mpr (.assumption (Set.mem_insert _ _)))
          (h.weaken (Set.subset_insert _ _))
      · intro h
        apply Derives.negIntro
        exact .implElim (h.weaken (Set.subset_insert _ _))
          ((ih _).mp (.assumption (Set.mem_insert _ _)))
  | conj A B ihA ihB =>
      intro Γ
      change Derives Γ (conj A B) ↔ Derives Γ (conj (expandNegation A) (expandNegation B))
      constructor
      · intro h
        exact .conjIntro ((ihA _).mp (.conjElimLeft h)) ((ihB _).mp (.conjElimRight h))
      · intro h
        exact .conjIntro ((ihA _).mpr (.conjElimLeft h)) ((ihB _).mpr (.conjElimRight h))
  | disj A B ihA ihB =>
      intro Γ
      change Derives Γ (disj A B) ↔ Derives Γ (disj (expandNegation A) (expandNegation B))
      constructor
      · intro h
        apply Derives.disjElim h
        · exact .disjIntroLeft ((ihA _).mp (.assumption (Set.mem_insert _ _)))
        · exact .disjIntroRight ((ihB _).mp (.assumption (Set.mem_insert _ _)))
      · intro h
        apply Derives.disjElim h
        · exact .disjIntroLeft ((ihA _).mpr (.assumption (Set.mem_insert _ _)))
        · exact .disjIntroRight ((ihB _).mpr (.assumption (Set.mem_insert _ _)))
  | impl A B ihA ihB =>
      intro Γ
      change Derives Γ (impl A B) ↔ Derives Γ (impl (expandNegation A) (expandNegation B))
      constructor
      · intro h
        apply Derives.implIntro
        apply (ihB _).mp
        exact .implElim (h.weaken (Set.subset_insert _ _))
          ((ihA _).mpr (.assumption (Set.mem_insert _ _)))
      · intro h
        apply Derives.implIntro
        apply (ihB _).mpr
        exact .implElim (h.weaken (Set.subset_insert _ _))
          ((ihA _).mp (.assumption (Set.mem_insert _ _)))

theorem expandNegation_equivalence (A : PropFormula α) :
    Derives ∅ (biconditional A (expandNegation A)) := by
  apply Derives.conjIntro
  · exact .implIntro ((expandNegation_context_iff A _).mp (.assumption (Set.mem_insert _ _)))
  · exact .implIntro ((expandNegation_context_iff A _).mpr (.assumption (Set.mem_insert _ _)))

theorem expandNegation_derives_iff (Γ : Set (PropFormula α)) (A : PropFormula α) :
    Derives Γ A ↔ Derives (expandNegation '' Γ) (expandNegation A) := by
  constructor
  · intro h
    exact h.expandNegation.to_derives
  · intro h
    have he : Derives Γ (expandNegation A) := h.replace (by
      intro B hB
      rcases hB with ⟨C, hC, rfl⟩
      exact (expandNegation_context_iff C Γ).mp (.assumption hC))
    exact (expandNegation_context_iff A Γ).mpr he

end Lemmatheca.ProofTheory.Intuitionistic
