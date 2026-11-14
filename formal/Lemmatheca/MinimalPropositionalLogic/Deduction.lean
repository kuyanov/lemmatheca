import Lemmatheca.IntuitionisticPropositionalDeduction.Deduction

/-! Minimal natural deduction on the shared native propositional syntax.
Falsum elimination is absent; contradiction is a conclusion, not a license for
an unrelated conclusion. -/
namespace Lemmatheca.ProofTheory.Minimal
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u v

inductive Derives {α : Type u} : Set (PropFormula α) → PropFormula α → Prop
  | assumption {Γ A} : A ∈ Γ → Derives Γ A
  | conjIntro {Γ A B} : Derives Γ A → Derives Γ B → Derives Γ (conj A B)
  | conjElimLeft {Γ A B} : Derives Γ (conj A B) → Derives Γ A
  | conjElimRight {Γ A B} : Derives Γ (conj A B) → Derives Γ B
  | disjIntroLeft {Γ A B} : Derives Γ A → Derives Γ (disj A B)
  | disjIntroRight {Γ A B} : Derives Γ B → Derives Γ (disj A B)
  | disjElim {Γ A B C} : Derives Γ (disj A B) →
      Derives (insert A Γ) C → Derives (insert B Γ) C → Derives Γ C
  | implIntro {Γ A B} : Derives (insert A Γ) B → Derives Γ (impl A B)
  | implElim {Γ A B} : Derives Γ (impl A B) → Derives Γ A → Derives Γ B
  | negIntro {Γ A} : Derives (insert A Γ) falsum → Derives Γ (neg A)
  | negElim {Γ A} : Derives Γ A → Derives Γ (neg A) → Derives Γ falsum

variable {α : Type u} {β : Type v}

theorem Derives.weaken {Γ Δ : Set (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) (hΓ : Γ ⊆ Δ) : Derives Δ A := by
  induction h generalizing Δ with
  | assumption hA => exact .assumption (hΓ hA)
  | conjIntro _ _ ihA ihB => exact .conjIntro (ihA hΓ) (ihB hΓ)
  | conjElimLeft _ ih => exact .conjElimLeft (ih hΓ)
  | conjElimRight _ ih => exact .conjElimRight (ih hΓ)
  | disjIntroLeft _ ih => exact .disjIntroLeft (ih hΓ)
  | disjIntroRight _ ih => exact .disjIntroRight (ih hΓ)
  | disjElim _ _ _ ihAB ihA ihB =>
      exact .disjElim (ihAB hΓ) (ihA (Set.insert_subset_insert hΓ))
        (ihB (Set.insert_subset_insert hΓ))
  | implIntro _ ih => exact .implIntro (ih (Set.insert_subset_insert hΓ))
  | implElim _ _ ihAB ihA => exact .implElim (ihAB hΓ) (ihA hΓ)
  | negIntro _ ih => exact .negIntro (ih (Set.insert_subset_insert hΓ))
  | negElim _ _ ihA ihN => exact .negElim (ihA hΓ) (ihN hΓ)


theorem Derives.replace {Γ Δ : Set (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) (hΓ : ∀ B ∈ Γ, Derives Δ B) : Derives Δ A := by
  induction h generalizing Δ with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact .conjIntro (ihA hΓ) (ihB hΓ)
  | conjElimLeft _ ih => exact .conjElimLeft (ih hΓ)
  | conjElimRight _ ih => exact .conjElimRight (ih hΓ)
  | disjIntroLeft _ ih => exact .disjIntroLeft (ih hΓ)
  | disjIntroRight _ ih => exact .disjIntroRight (ih hΓ)
  | @disjElim Γ A B C _ _ _ ihAB ihA ihB =>
      apply Derives.disjElim (ihAB hΓ)
      · apply ihA
        intro D hD
        rcases Set.mem_insert_iff.mp hD with rfl | hD
        · exact .assumption (Set.mem_insert _ _)
        · exact (hΓ D hD).weaken (Set.subset_insert _ _)
      · apply ihB
        intro D hD
        rcases Set.mem_insert_iff.mp hD with rfl | hD
        · exact .assumption (Set.mem_insert _ _)
        · exact (hΓ D hD).weaken (Set.subset_insert _ _)
  | @implIntro Γ A B _ ih =>
      apply Derives.implIntro
      apply ih
      intro D hD
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · exact .assumption (Set.mem_insert _ _)
      · exact (hΓ D hD).weaken (Set.subset_insert _ _)
  | implElim _ _ ihAB ihA => exact .implElim (ihAB hΓ) (ihA hΓ)
  | @negIntro Γ A _ ih =>
      apply Derives.negIntro
      apply ih
      intro D hD
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · exact .assumption (Set.mem_insert _ _)
      · exact (hΓ D hD).weaken (Set.subset_insert _ _)
  | negElim _ _ ihA ihN => exact .negElim (ihA hΓ) (ihN hΓ)


theorem Derives.cut {Γ : Set (PropFormula α)} {A B : PropFormula α}
    (hB : Derives Γ B) (hA : Derives (insert B Γ) A) : Derives Γ A := by
  apply hA.replace
  intro C hC
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact hB
  · exact .assumption hC


theorem Derives.substitute (σ : α → PropFormula β) {Γ : Set (PropFormula α)}
    {A : PropFormula α} (h : Derives Γ A) :
    Derives (Intuitionistic.substituteContext σ Γ) (subst σ A) := by
  induction h with
  | assumption hA => exact .assumption (Set.mem_image_of_mem _ hA)
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB =>
      apply Derives.disjElim ihAB
      · simpa [Intuitionistic.substituteContext, Set.image_insert_eq, subst] using ihA
      · simpa [Intuitionistic.substituteContext, Set.image_insert_eq, subst] using ihB
  | implIntro _ ih =>
      apply Derives.implIntro
      simpa [Intuitionistic.substituteContext, Set.image_insert_eq, subst] using ih
  | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
  | negIntro _ ih =>
      apply Derives.negIntro
      simpa [Intuitionistic.substituteContext, Set.image_insert_eq, subst] using ih
  | negElim _ _ ihA ihN => exact .negElim ihA ihN


theorem deduction {Γ : Set (PropFormula α)} {A B : PropFormula α} :
    Derives (insert A Γ) B ↔ Derives Γ (impl A B) := by
  constructor
  · exact Derives.implIntro
  · intro h
    exact .implElim (h.weaken (Set.subset_insert _ _)) (.assumption (Set.mem_insert _ _))


theorem negation_iff_implication {Γ : Set (PropFormula α)} {A : PropFormula α} :
    Derives Γ (neg A) ↔ Derives Γ (impl A falsum) := by
  constructor
  · intro h
    exact .implIntro (.negElim (.assumption (Set.mem_insert _ _))
      (h.weaken (Set.subset_insert _ _)))
  · intro h
    exact .negIntro (.implElim (h.weaken (Set.subset_insert _ _))
      (.assumption (Set.mem_insert _ _)))


theorem negation_implication_equivalence (A : PropFormula α) :
    Derives ∅ (biconditional (neg A) (impl A falsum)) := by
  apply Derives.conjIntro
  · apply Derives.implIntro
    exact negation_iff_implication.mp (.assumption (Set.mem_insert _ _))
  · apply Derives.implIntro
    exact negation_iff_implication.mpr (.assumption (Set.mem_insert _ _))


theorem double_negation_intro (A : PropFormula α) :
    Derives ∅ (impl A (neg (neg A))) := by
  apply Derives.implIntro
  apply Derives.negIntro
  exact .negElim (A := A) (.assumption (by simp)) (.assumption (by simp))


theorem contraposition (A B : PropFormula α) :
    Derives ∅ (impl (impl A B) (impl (neg B) (neg A))) := by
  apply Derives.implIntro
  apply Derives.implIntro
  apply Derives.negIntro
  exact .negElim (A := B) (.implElim (A := A) (.assumption (by simp)) (.assumption (by simp)))
    (.assumption (by simp))


theorem triple_negation_elim (A : PropFormula α) :
    Derives ∅ (impl (neg (neg (neg A))) (neg A)) := by
  apply Derives.implIntro
  apply Derives.negIntro
  have hA : Derives (insert A (insert (neg (neg (neg A))) ∅)) A :=
    .assumption (by simp)
  have hNN : Derives (insert A (insert (neg (neg (neg A))) ∅)) (neg (neg A)) :=
    .implElim ((double_negation_intro A).weaken (Set.empty_subset _)) hA
  exact .negElim hNN (.assumption (by simp))


theorem double_negated_excluded_middle (A : PropFormula α) :
    Derives ∅ (neg (neg (disj A (neg A)))) := by
  apply Derives.negIntro
  have hn : Derives (insert (neg (disj A (neg A))) ∅) (neg A) := by
    apply Derives.negIntro
    exact .negElim (A := disj A (neg A))
      (.disjIntroLeft (.assumption (by simp))) (.assumption (by simp))
  exact .negElim (A := disj A (neg A)) (.disjIntroRight hn) (.assumption (by simp))


theorem negated_falsum : Derives (∅ : Set (PropFormula α)) (neg falsum) := by
  exact .negIntro (.assumption (Set.mem_insert _ _))


/-- All explosion implications in the given atom language. -/
def explosionSchema : Set (PropFormula α) := Set.range (fun A => impl falsum A)

theorem Derives.to_intuitionistic {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) : Intuitionistic.Derives Γ A := by
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
  | negIntro _ ih => exact .negIntro ih
  | negElim _ _ ihA ihN => exact .negElim ihA ihN


theorem intuitionistic_iff_explosion {Γ : Set (PropFormula α)} {A : PropFormula α} :
    Intuitionistic.Derives Γ A ↔ Derives (Γ ∪ explosionSchema) A := by
  constructor
  · intro h
    induction h with
    | assumption hA => exact .assumption (Or.inl hA)
    | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
    | conjElimLeft _ ih => exact .conjElimLeft ih
    | conjElimRight _ ih => exact .conjElimRight ih
    | disjIntroLeft _ ih => exact .disjIntroLeft ih
    | disjIntroRight _ ih => exact .disjIntroRight ih
    | disjElim _ _ _ ihAB ihA ihB =>
        apply Derives.disjElim ihAB
        · simpa only [Set.insert_union] using ihA
        · simpa only [Set.insert_union] using ihB
    | implIntro _ ih =>
        apply Derives.implIntro
        simpa only [Set.insert_union] using ih
    | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
    | negIntro _ ih =>
        apply Derives.negIntro
        simpa only [Set.insert_union] using ih
    | negElim _ _ ihA ihN => exact .negElim ihA ihN
    | @falsumElim Γ B _ ih =>
        apply Derives.implElim (A := falsum) ?_ ih
        exact .assumption (Or.inr (Set.mem_range_self B))
  · intro h
    apply h.to_intuitionistic.replace
    intro B hB
    rcases hB with hB | hB
    · exact .assumption hB
    · rcases hB with ⟨C, rfl⟩
      exact .implIntro (.falsumElim (.assumption (Set.mem_insert _ _)))


theorem explosion_iff_disjunctive_syllogism (Γ : Set (PropFormula α)) :
    (∀ B, Derives Γ (impl falsum B)) ↔
      ∀ A B, Derives Γ (impl (disj A B) (impl (neg A) B)) := by
  constructor
  · intro h A B
    apply Derives.implIntro
    apply Derives.implIntro
    apply Derives.disjElim (A := A) (B := B) (.assumption (by simp))
    · have he : Derives (insert A (insert (neg A) (insert (disj A B) Γ)))
          (impl falsum B) := (h B).weaken (by
            intro D hD
            exact Or.inr (Or.inr (Or.inr hD)))
      exact .implElim he (.negElim (A := A) (.assumption (by simp)) (.assumption (by simp)))
    · exact .assumption (by simp)
  · intro h B
    apply Derives.implIntro
    have hs := (h falsum B).weaken (Set.subset_insert falsum Γ)
    have hn : Derives (insert falsum Γ) (neg falsum) :=
      negated_falsum.weaken (Set.empty_subset _)
    exact .implElim (.implElim hs (.disjIntroLeft (.assumption (by simp)))) hn


theorem dne_implies_explosion (A : PropFormula α) :
    Derives ∅ (impl (impl (neg (neg A)) A) (impl falsum A)) := by
  apply Derives.implIntro
  apply Derives.implIntro
  exact .implElim (A := neg (neg A)) (.assumption (by simp))
    (.negIntro (A := neg A) (.assumption (by simp)))


theorem empty_not_derives_falsum : ¬ Derives (∅ : Set (PropFormula α)) falsum := by
  intro h
  exact Intuitionistic.empty_not_derives_falsum h.to_intuitionistic


end Lemmatheca.ProofTheory.Minimal
