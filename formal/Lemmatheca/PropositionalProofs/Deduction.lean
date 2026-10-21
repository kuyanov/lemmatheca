import Lemmatheca.PropositionalLogic.Propositional

/-! Classical natural deduction for the shared finite propositional syntax.
Contexts record allowed open assumptions. Temporary assumptions are inserted
in branch contexts and discharged by the enclosing rule. -/

namespace Lemmatheca.MathematicalLogic.Propositional

open PropFormula

variable {α : Type*} [DecidableEq α]

/-- Existence of a finite classical natural-deduction proof from a finite context. -/
inductive Derives : Finset (PropFormula α) → PropFormula α → Prop
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
  | classicalContradiction {Γ A} : Derives (insert (neg A) Γ) falsum → Derives Γ A

/-- Enlarging the ambient set of permitted open assumptions preserves derivability. -/
theorem Derives.weaken {Γ Δ : Finset (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) (hΓ : Γ ⊆ Δ) : Derives Δ A := by
  induction h generalizing Δ with
  | assumption hA => exact .assumption (hΓ hA)
  | conjIntro _ _ ihA ihB => exact .conjIntro (ihA hΓ) (ihB hΓ)
  | conjElimLeft _ ih => exact .conjElimLeft (ih hΓ)
  | conjElimRight _ ih => exact .conjElimRight (ih hΓ)
  | disjIntroLeft _ ih => exact .disjIntroLeft (ih hΓ)
  | disjIntroRight _ ih => exact .disjIntroRight (ih hΓ)
  | disjElim _ _ _ ihAB ihA ihB =>
      exact .disjElim (ihAB hΓ) (ihA (Finset.insert_subset_insert _ hΓ))
        (ihB (Finset.insert_subset_insert _ hΓ))
  | implIntro _ ih => exact .implIntro (ih (Finset.insert_subset_insert _ hΓ))
  | implElim _ _ ihAB ihA => exact .implElim (ihAB hΓ) (ihA hΓ)
  | negIntro _ ih => exact .negIntro (ih (Finset.insert_subset_insert _ hΓ))
  | negElim _ _ ihA ihnotA => exact .negElim (ihA hΓ) (ihnotA hΓ)
  | falsumElim _ ih => exact .falsumElim (ih hΓ)
  | classicalContradiction _ ih =>
      exact .classicalContradiction (ih (Finset.insert_subset_insert _ hΓ))

/-- The displayed conjunction-projection proof has no open assumptions. -/
theorem derives_conjunction_projection (A B : PropFormula α) :
    Derives ∅ (impl (conj A B) A) := by
  have h : Derives (insert (conj A B) ∅) (conj A B) := .assumption (by simp)
  exact .implIntro (.conjElimLeft h)

/-- Classical contradiction proves excluded middle without premises. -/
theorem derives_excluded_middle (A : PropFormula α) :
    Derives ∅ (disj A (neg A)) := by
  apply Derives.classicalContradiction
  have hn : Derives (insert (neg (disj A (neg A))) ∅) (neg A) := by
    apply Derives.negIntro
    have ha : Derives (insert A (insert (neg (disj A (neg A))) ∅)) A :=
      .assumption (by simp)
    have hd : Derives (insert A (insert (neg (disj A (neg A))) ∅)) (disj A (neg A)) :=
      .disjIntroLeft ha
    exact .negElim hd (.assumption (by simp))
  have hd : Derives (insert (neg (disj A (neg A))) ∅) (disj A (neg A)) :=
    .disjIntroRight hn
  exact .negElim hd (.assumption (by simp))

/-- Derivations of the same conclusion in the positive and negative branches combine. -/
theorem Derives.cases {Γ : Finset (PropFormula α)} {A C : PropFormula α}
    (hA : Derives (insert A Γ) C) (hnotA : Derives (insert (neg A) Γ) C) :
    Derives Γ C := by
  exact .disjElim ((derives_excluded_middle A).weaken (by simp)) hA hnotA

/-- Every rule of the specified calculus preserves Boolean semantic consequence. -/
theorem derives_sound {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) : Entails Γ A := by
  induction h with
  | assumption hA =>
      intro v hv
      exact hv _ hA
  | conjIntro _ _ ihA ihB =>
      intro v hv
      exact Bool.and_eq_true_iff.mpr ⟨ihA v hv, ihB v hv⟩
  | conjElimLeft _ ih =>
      intro v hv
      exact (Bool.and_eq_true_iff.mp (ih v hv)).1
  | conjElimRight _ ih =>
      intro v hv
      exact (Bool.and_eq_true_iff.mp (ih v hv)).2
  | disjIntroLeft _ ih =>
      intro v hv
      exact Bool.or_eq_true_iff.mpr (Or.inl (ih v hv))
  | disjIntroRight _ ih =>
      intro v hv
      exact Bool.or_eq_true_iff.mpr (Or.inr (ih v hv))
  | disjElim _ _ _ ihAB ihA ihB =>
      intro v hv
      rcases Bool.or_eq_true_iff.mp (ihAB v hv) with hA | hB
      · apply ihA v
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact hA
        · exact hv D hD
      · apply ihB v
        intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact hB
        · exact hv D hD
  | @implIntro Γ A B _ ih =>
      intro v hv
      cases he : eval v A with
      | false => simp [Satisfies, eval, he]
      | true =>
          have hB : eval v B = true := ih v (by
            intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · exact he
            · exact hv D hD)
          simp [Satisfies, eval, he, hB]
  | @implElim Γ A B _ _ ihAB ihA =>
      intro v hv
      have hA : eval v A = true := ihA v hv
      have hAB : (!(eval v A) || eval v B) = true := ihAB v hv
      simpa [Satisfies, hA] using hAB
  | @negIntro Γ A _ ih =>
      intro v hv
      cases he : eval v A with
      | false => simp [Satisfies, eval, he]
      | true =>
          have hf := ih v (by
            intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · exact he
            · exact hv D hD)
          simp [Satisfies, eval] at hf
  | @negElim Γ A _ _ ihA ihnotA =>
      intro v hv
      have hA : eval v A = true := ihA v hv
      have hn : (!(eval v A)) = true := ihnotA v hv
      simp [hA] at hn
  | falsumElim _ ih =>
      intro v hv
      have hf := ih v hv
      simp [Satisfies, eval] at hf
  | @classicalContradiction Γ A _ ih =>
      intro v hv
      cases he : eval v A with
      | false =>
          have hf := ih v (by
            intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · simp [Satisfies, eval, he]
            · exact hv D hD)
          simp [Satisfies, eval] at hf
      | true => exact he

/-- Affirming the consequent is not a derivation when the atoms are distinct. -/
theorem affirmingConsequent_not_derivable (a b : α) (hab : a ≠ b) :
    ¬ Derives {impl (atom a) (atom b), atom b} (atom a) := by
  intro h
  have hc := affirmingConsequent_countervaluation a b hab
  have ht := derives_sound h _ hc.1
  exact Bool.false_ne_true (hc.2.symm.trans ht)

/-- The positive formula or its negation, according to its value under a valuation. -/
def signed (v : α → Bool) (A : PropFormula α) : PropFormula α :=
  if eval v A then A else neg A

/-- The finitely many atom literals describing one row on the supplied support. -/
def signedContext (S : Finset α) (v : α → Bool) : Finset (PropFormula α) :=
  S.image (fun a => signed v (atom a))

/-- A finite signed atom context derives the correct sign of every supported formula. -/
theorem derives_signed (S : Finset α) (v : α → Bool) (A : PropFormula α)
    (hA : atoms A ⊆ S) : Derives (signedContext S v) (signed v A) := by
  induction A generalizing S with
  | atom a =>
      apply Derives.assumption
      exact Finset.mem_image.mpr ⟨a, hA (by simp [atoms]), rfl⟩
  | falsum =>
      simp only [signed, eval, Bool.false_eq_true, ↓reduceIte]
      exact .negIntro (.assumption (by simp))
  | neg A ih =>
      have dA := ih S hA
      cases he : eval v A with
      | false =>
          simpa [signed, eval, he] using dA
      | true =>
          simp [signed, he] at dA
          simp only [signed, eval, he, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          apply Derives.negIntro
          exact Derives.negElim (A := A)
            (dA.weaken (Finset.subset_insert _ _)) (.assumption (by simp))
  | conj A B ihA ihB =>
      let Γ := signedContext S v
      have dA : Derives Γ (signed v A) :=
        ihA S (fun a ha => hA (Finset.mem_union_left _ ha))
      have dB : Derives Γ (signed v B) :=
        ihB S (fun b hb => hA (Finset.mem_union_right _ hb))
      cases heA : eval v A <;> cases heB : eval v B <;>
        simp [signed, eval, heA, heB] at dA dB ⊢
      · apply Derives.negIntro
        have hd : Derives (insert (conj A B) Γ) (conj A B) := .assumption (by simp)
        exact .negElim (.conjElimLeft hd) (dA.weaken (Finset.subset_insert _ _))
      · apply Derives.negIntro
        have hd : Derives (insert (conj A B) Γ) (conj A B) := .assumption (by simp)
        exact .negElim (.conjElimLeft hd) (dA.weaken (Finset.subset_insert _ _))
      · apply Derives.negIntro
        have hd : Derives (insert (conj A B) Γ) (conj A B) := .assumption (by simp)
        exact .negElim (.conjElimRight hd) (dB.weaken (Finset.subset_insert _ _))
      · exact .conjIntro dA dB
  | disj A B ihA ihB =>
      let Γ := signedContext S v
      have dA : Derives Γ (signed v A) :=
        ihA S (fun a ha => hA (Finset.mem_union_left _ ha))
      have dB : Derives Γ (signed v B) :=
        ihB S (fun b hb => hA (Finset.mem_union_right _ hb))
      cases heA : eval v A <;> cases heB : eval v B <;>
        simp [signed, eval, heA, heB] at dA dB ⊢
      · apply Derives.negIntro
        have hd : Derives (insert (disj A B) Γ) (disj A B) := .assumption (by simp)
        refine Derives.disjElim hd ?_ ?_
        · exact Derives.negElim (A := A) (.assumption (by simp))
            (dA.weaken (by intro D hD; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hD)))
        · exact Derives.negElim (A := B) (.assumption (by simp))
            (dB.weaken (by intro D hD; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hD)))
      · exact .disjIntroRight dB
      · exact .disjIntroLeft dA
      · exact .disjIntroLeft dA
  | impl A B ihA ihB =>
      let Γ := signedContext S v
      have dA : Derives Γ (signed v A) :=
        ihA S (fun a ha => hA (Finset.mem_union_left _ ha))
      have dB : Derives Γ (signed v B) :=
        ihB S (fun b hb => hA (Finset.mem_union_right _ hb))
      cases heA : eval v A <;> cases heB : eval v B <;>
        simp [signed, eval, heA, heB] at dA dB ⊢
      · apply Derives.implIntro
        apply Derives.falsumElim
        exact Derives.negElim (A := A) (.assumption (by simp))
          (dA.weaken (Finset.subset_insert _ _))
      · exact .implIntro (dB.weaken (Finset.subset_insert _ _))
      · apply Derives.negIntro
        have hd : Derives (insert (impl A B) Γ) (impl A B) := .assumption (by simp)
        exact .negElim (.implElim hd (dA.weaken (Finset.subset_insert _ _)))
          (dB.weaken (Finset.subset_insert _ _))
      · exact .implIntro (dB.weaken (Finset.subset_insert _ _))

private theorem signedContext_insert (S : Finset α) (a : α) (v : α → Bool) :
    signedContext (insert a S) v = insert (signed v (atom a)) (signedContext S v) := by
  exact Finset.image_insert _ _ _

private theorem signedContext_update (S : Finset α) (a : α) (v : α → Bool)
    (b : Bool) (ha : a ∉ S) :
    signedContext S (Function.update v a b) = signedContext S v := by
  unfold signedContext
  apply Finset.image_congr
  intro x hx
  have hxa : x ≠ a := by
    intro h
    subst x
    exact ha hx
  simp only [signed, eval, Function.update_of_ne hxa]
  rfl

/-- All finitely many atom choices can be eliminated by classical binary cases. -/
theorem derives_cases_finite (S : Finset α) (Γ : Finset (PropFormula α))
    (C : PropFormula α) (h : ∀ v : α → Bool, Derives (Γ ∪ signedContext S v) C) :
    Derives Γ C := by
  revert h
  induction S using Finset.induction_on with
  | empty =>
      intro h
      simpa [signedContext] using h (fun _ => false)
  | @insert a S ha ih =>
      intro h
      apply ih
      intro v
      have ht := h (Function.update v a true)
      have hf := h (Function.update v a false)
      rw [signedContext_insert, signedContext_update S a v true ha] at ht
      rw [signedContext_insert, signedContext_update S a v false ha] at hf
      have dt : Derives (insert (atom a) (Γ ∪ signedContext S v)) C := by
        simpa [signed, eval, Finset.union_insert] using ht
      have df : Derives (insert (neg (atom a)) (Γ ∪ signedContext S v)) C := by
        simpa [signed, eval, Finset.union_insert] using hf
      exact Derives.cases dt df

/-- Finite-premise semantic consequence produces a derivation in the chosen calculus. -/
theorem derives_complete {Γ : Finset (PropFormula α)} {C : PropFormula α}
    (h : Entails Γ C) : Derives Γ C := by
  classical
  let S := atoms C ∪ contextAtoms Γ
  apply derives_cases_finite S Γ C
  intro v
  by_cases hv : SatisfiesContext v Γ
  · have heC : eval v C = true := h v hv
    have dC := derives_signed S v C Finset.subset_union_left
    have dt : Derives (signedContext S v) C := by
      simpa [signed, heC] using dC
    exact dt.weaken Finset.subset_union_right
  · simp only [SatisfiesContext, Satisfies] at hv
    push Not at hv
    obtain ⟨B, hB, hnotB⟩ := hv
    have heB : eval v B = false := by
      cases he : eval v B with
      | false => rfl
      | true => exact False.elim (hnotB he)
    have hsupport : atoms B ⊆ S := by
      intro a ha
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hB, ha⟩)
    have dB := derives_signed S v B hsupport
    have dn : Derives (signedContext S v) (neg B) := by
      simpa [signed, heB] using dB
    apply Derives.falsumElim
    exact Derives.negElim (A := B)
      (.assumption (Finset.mem_union_left _ hB)) (dn.weaken Finset.subset_union_right)

/-- Soundness and finite-premise completeness equate derivability with consequence. -/
theorem derives_iff_entails (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Derives Γ A ↔ Entails Γ A := by
  exact ⟨derives_sound, derives_complete⟩

/-- Assumption-free derivations are exactly tautologies. -/
theorem theorem_iff_tautology (A : PropFormula α) :
    Derives ∅ A ↔ Tautology A := by
  rw [derives_iff_entails, entails_empty_iff]

/-- Syntactic consistency is the absence of a derivation of falsum. -/
def Consistent (Γ : Finset (PropFormula α)) : Prop := ¬ Derives Γ falsum

/-- A finite context is syntactically consistent exactly when it has a valuation. -/
theorem consistent_iff_satisfiable (Γ : Finset (PropFormula α)) :
    Consistent Γ ↔ Satisfiable Γ := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    apply derives_complete
    intro v hv
    exact False.elim (hn ⟨v, hv⟩)
  · rintro ⟨v, hv⟩ hd
    have hf := derives_sound hd v hv
    simp [Satisfies, eval] at hf

/-- No assumption-free derivation concludes falsum, including with an empty atom type. -/
theorem empty_not_derives_falsum : ¬ Derives (∅ : Finset (PropFormula α)) falsum := by
  intro h
  have hf := derives_sound h (fun _ => false) (by intro B hB; simp at hB)
  simp [Satisfies, eval] at hf

/-- A formula and its negation derive any conclusion by negation elimination and explosion. -/
theorem contradictory_derives (A C : PropFormula α) :
    Derives {A, neg A} C := by
  apply Derives.falsumElim
  exact Derives.negElim (A := A) (.assumption (by simp)) (.assumption (by simp))

end Lemmatheca.MathematicalLogic.Propositional
