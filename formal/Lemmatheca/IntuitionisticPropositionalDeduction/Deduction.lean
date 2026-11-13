import Lemmatheca.PropositionalProofs.Deduction

/-! Intuitionistic natural deduction on the corpus's shared propositional syntax.
Arbitrary sets specify allowed open assumptions; the inductive derivations are finite.
Primitive negation has its two intuitionistic rules, with an explicit expansion bridge
provided separately. No classical contradiction constructor is present. -/

namespace Lemmatheca.ProofTheory.Intuitionistic

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u v

/-- Finite intuitionistic derivations with arbitrary allowed-assumption sets. -/
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
  | falsumElim {Γ A} : Derives Γ falsum → Derives Γ A

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
  | falsumElim _ ih => exact .falsumElim (ih hΓ)

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
  | falsumElim _ ih => exact .falsumElim (ih hΓ)

theorem Derives.cut {Γ : Set (PropFormula α)} {A B : PropFormula α}
    (hB : Derives Γ B) (hA : Derives (insert B Γ) A) : Derives Γ A := by
  apply hA.replace
  intro C hC
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact hB
  · exact .assumption hC

theorem finite_support {Γ : Set (PropFormula α)} {A : PropFormula α} :
    Derives Γ A ↔ ∃ Δ : Set (PropFormula α), Δ.Finite ∧ Δ ⊆ Γ ∧ Derives Δ A := by
  classical
  constructor
  · intro h
    induction h with
    | assumption hA =>
        exact ⟨{_}, Set.finite_singleton _, Set.singleton_subset_iff.mpr hA,
          .assumption (Set.mem_singleton _)⟩
    | conjIntro _ _ ihA ihB =>
        rcases ihA with ⟨D, hfD, hsD, hdD⟩
        rcases ihB with ⟨E, hfE, hsE, hdE⟩
        exact ⟨D ∪ E, hfD.union hfE, Set.union_subset hsD hsE,
          .conjIntro (hdD.weaken Set.subset_union_left) (hdE.weaken Set.subset_union_right)⟩
    | conjElimLeft _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        exact ⟨D, hf, hs, .conjElimLeft hd⟩
    | conjElimRight _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        exact ⟨D, hf, hs, .conjElimRight hd⟩
    | disjIntroLeft _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        exact ⟨D, hf, hs, .disjIntroLeft hd⟩
    | disjIntroRight _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        exact ⟨D, hf, hs, .disjIntroRight hd⟩
    | @disjElim Γ A B C _ _ _ ih0 ih1 ih2 =>
        rcases ih0 with ⟨D, hfD, hsD, hdD⟩
        rcases ih1 with ⟨E, hfE, hsE, hdE⟩
        rcases ih2 with ⟨F, hfF, hsF, hdF⟩
        let G := D ∪ ((E \ {A}) ∪ (F \ {B}))
        have he : E \ {A} ⊆ Γ := by
          intro X hX
          rcases Set.mem_insert_iff.mp (hsE hX.1) with rfl | hXΓ
          · exact (hX.2 (Set.mem_singleton _)).elim
          · exact hXΓ
        have hf : F \ {B} ⊆ Γ := by
          intro X hX
          rcases Set.mem_insert_iff.mp (hsF hX.1) with rfl | hXΓ
          · exact (hX.2 (Set.mem_singleton _)).elim
          · exact hXΓ
        refine ⟨G, hfD.union (hfE.sdiff.union hfF.sdiff),
          Set.union_subset hsD (Set.union_subset he hf), .disjElim (A := A) (B := B) ?_ ?_ ?_⟩
        · exact hdD.weaken Set.subset_union_left
        · apply hdE.weaken
          intro X hX
          by_cases e : X = A
          · exact Set.mem_insert_iff.mpr (Or.inl e)
          · exact Set.mem_insert_iff.mpr (Or.inr (Or.inr (Or.inl ⟨hX, by simpa using e⟩)))
        · apply hdF.weaken
          intro X hX
          by_cases e : X = B
          · exact Set.mem_insert_iff.mpr (Or.inl e)
          · exact Set.mem_insert_iff.mpr (Or.inr (Or.inr (Or.inr ⟨hX, by simpa using e⟩)))
    | @implIntro Γ A B _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        refine ⟨D \ {A}, hf.sdiff, ?_, .implIntro (hd.weaken ?_)⟩
        · intro X hX
          rcases Set.mem_insert_iff.mp (hs hX.1) with rfl | hXΓ
          · exact (hX.2 (Set.mem_singleton _)).elim
          · exact hXΓ
        · intro X hX
          by_cases e : X = A
          · exact Set.mem_insert_iff.mpr (Or.inl e)
          · exact Set.mem_insert_iff.mpr (Or.inr ⟨hX, by simpa using e⟩)
    | implElim _ _ ihAB ihA =>
        rcases ihAB with ⟨D, hfD, hsD, hdD⟩
        rcases ihA with ⟨E, hfE, hsE, hdE⟩
        exact ⟨D ∪ E, hfD.union hfE, Set.union_subset hsD hsE,
          .implElim (hdD.weaken Set.subset_union_left) (hdE.weaken Set.subset_union_right)⟩
    | @negIntro Γ A _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        refine ⟨D \ {A}, hf.sdiff, ?_, .negIntro (hd.weaken ?_)⟩
        · intro X hX
          rcases Set.mem_insert_iff.mp (hs hX.1) with rfl | hXΓ
          · exact (hX.2 (Set.mem_singleton _)).elim
          · exact hXΓ
        · intro X hX
          by_cases e : X = A
          · exact Set.mem_insert_iff.mpr (Or.inl e)
          · exact Set.mem_insert_iff.mpr (Or.inr ⟨hX, by simpa using e⟩)
    | negElim _ _ ihA ihN =>
        rcases ihA with ⟨D, hfD, hsD, hdD⟩
        rcases ihN with ⟨E, hfE, hsE, hdE⟩
        exact ⟨D ∪ E, hfD.union hfE, Set.union_subset hsD hsE,
          .negElim (hdD.weaken Set.subset_union_left) (hdE.weaken Set.subset_union_right)⟩
    | falsumElim _ ih =>
        rcases ih with ⟨D, hf, hs, hd⟩
        exact ⟨D, hf, hs, .falsumElim hd⟩
  · rintro ⟨D, _, hs, hd⟩
    exact hd.weaken hs

/-- The pointwise image of an arbitrary premise set under simultaneous substitution. -/
def substituteContext (σ : α → PropFormula β) (Γ : Set (PropFormula α)) :
    Set (PropFormula β) := subst σ '' Γ

theorem Derives.substitute (σ : α → PropFormula β) {Γ : Set (PropFormula α)}
    {A : PropFormula α} (h : Derives Γ A) :
    Derives (substituteContext σ Γ) (subst σ A) := by
  induction h with
  | assumption hA => exact .assumption (Set.mem_image_of_mem _ hA)
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact .disjIntroLeft ih
  | disjIntroRight _ ih => exact .disjIntroRight ih
  | disjElim _ _ _ ihAB ihA ihB =>
      apply Derives.disjElim ihAB
      · simpa [substituteContext, Set.image_insert_eq, subst] using ihA
      · simpa [substituteContext, Set.image_insert_eq, subst] using ihB
  | implIntro _ ih =>
      apply Derives.implIntro
      simpa [substituteContext, Set.image_insert_eq, subst] using ih
  | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
  | negIntro _ ih =>
      apply Derives.negIntro
      simpa [substituteContext, Set.image_insert_eq, subst] using ih
  | negElim _ _ ihA ihN => exact .negElim ihA ihN
  | falsumElim _ ih => exact .falsumElim ih

theorem deduction {Γ : Set (PropFormula α)} {A B : PropFormula α} :
    Derives (insert A Γ) B ↔ Derives Γ (impl A B) := by
  constructor
  · exact Derives.implIntro
  · intro h
    exact .implElim (h.weaken (Set.subset_insert _ _)) (.assumption (Set.mem_insert _ _))

theorem identity (A : PropFormula α) : Derives ∅ (impl A A) := by
  exact .implIntro (.assumption (Set.mem_insert _ _))

theorem implication_composition (A B C : PropFormula α) :
    Derives ∅ (impl (impl A B) (impl (impl B C) (impl A C))) := by
  apply Derives.implIntro
  apply Derives.implIntro
  apply Derives.implIntro
  exact .implElim (A := B) (.assumption (by simp))
    (.implElim (A := A) (.assumption (by simp)) (.assumption (by simp)))

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

theorem boolean_sound {Γ : Set (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) (v : α → Bool)
    (hΓ : ∀ B ∈ Γ, eval v B = true) : eval v A = true := by
  induction h with
  | assumption hA => exact hΓ _ hA
  | conjIntro _ _ ihA ihB => exact Bool.and_eq_true_iff.mpr ⟨ihA hΓ, ihB hΓ⟩
  | conjElimLeft _ ih => exact (Bool.and_eq_true_iff.mp (ih hΓ)).1
  | conjElimRight _ ih => exact (Bool.and_eq_true_iff.mp (ih hΓ)).2
  | disjIntroLeft _ ih => exact Bool.or_eq_true_iff.mpr (Or.inl (ih hΓ))
  | disjIntroRight _ ih => exact Bool.or_eq_true_iff.mpr (Or.inr (ih hΓ))
  | disjElim _ _ _ ihAB ihA ihB =>
      rcases Bool.or_eq_true_iff.mp (ihAB hΓ) with hA | hB
      · apply ihA
        intro D hD
        rcases Set.mem_insert_iff.mp hD with rfl | hD
        · exact hA
        · exact hΓ D hD
      · apply ihB
        intro D hD
        rcases Set.mem_insert_iff.mp hD with rfl | hD
        · exact hB
        · exact hΓ D hD
  | @implIntro Γ A B _ ih =>
      cases he : eval v A with
      | false => simp [eval, he]
      | true =>
          have hB : eval v B = true := ih (by
            intro D hD
            rcases Set.mem_insert_iff.mp hD with rfl | hD
            · exact he
            · exact hΓ D hD)
          simp [eval, he, hB]
  | @implElim Γ A B _ _ ihAB ihA =>
      have hA := ihA hΓ
      have hAB : (!(eval v A) || eval v B) = true := ihAB hΓ
      simpa [hA] using hAB
  | @negIntro Γ A _ ih =>
      cases he : eval v A with
      | false => simp [eval, he]
      | true =>
          have hf := ih (by
            intro D hD
            rcases Set.mem_insert_iff.mp hD with rfl | hD
            · exact he
            · exact hΓ D hD)
          simp [eval] at hf
  | negElim _ _ ihA ihN =>
      have hA := ihA hΓ
      have hn := ihN hΓ
      simp [eval, hA] at hn
  | falsumElim _ ih =>
      have hf := ih hΓ
      simp [eval] at hf

theorem empty_not_derives_falsum : ¬ Derives (∅ : Set (PropFormula α)) falsum := by
  intro h
  have hf := boolean_sound h (fun _ => false) (by simp)
  simp [eval] at hf

end Lemmatheca.ProofTheory.Intuitionistic
