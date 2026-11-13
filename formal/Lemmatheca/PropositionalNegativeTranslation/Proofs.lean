import Lemmatheca.PropositionalNegativeTranslation.Translation
import Lemmatheca.IntuitionisticPropositionalDeduction.Classical
import Lemmatheca.PropositionalCompactness.PropositionalCompactness

namespace Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u}

/-- The rule required by translated disjunction elimination, in any premise set. -/
theorem double_negated_disjunction_elim {Γ : Set (PropFormula α)}
    {A B C : PropFormula α} (hC : Stable C) (hAB : Derives Γ (neg (neg (disj A B))))
    (hA : Derives (insert A Γ) C) (hB : Derives (insert B Γ) C) :
    Derives Γ C := by
  apply Derives.implElim ((show Derives ∅ (impl (neg (neg C)) C) from hC).weaken
    (Set.empty_subset Γ))
  apply Derives.negIntro
  have hN : Derives (insert (neg C) Γ) (neg (disj A B)) := by
    apply Derives.negIntro
    apply Derives.negElim (A := C)
    · apply Derives.disjElim (A := A) (B := B) (.assumption (by simp))
      · exact hA.weaken (by
          intro D hD
          rcases hD with rfl | hD
          · simp
          · simp [hD])
      · exact hB.weaken (by
          intro D hD
          rcases hD with rfl | hD
          · simp
          · simp [hD])
    · exact .assumption (by simp)
  exact .negElim hN (hAB.weaken (Set.subset_insert _ _))

/-- Translate the given classical derivation, not merely its semantic consequence. -/
theorem classical_translate [DecidableEq α] {Γ : Finset (PropFormula α)}
    {A : PropFormula α} (h : Lemmatheca.MathematicalLogic.Propositional.Derives Γ A) :
    Derives (context (Γ : Set (PropFormula α))) (negative A) := by
  induction h with
  | assumption hA => exact .assumption ⟨_, hA, rfl⟩
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih =>
      exact .implElim ((double_negation_intro _).weaken (Set.empty_subset _))
        (.disjIntroLeft ih)
  | disjIntroRight _ ih =>
      exact .implElim ((double_negation_intro _).weaken (Set.empty_subset _))
        (.disjIntroRight ih)
  | disjElim _ _ _ ihAB ihA ihB =>
      apply double_negated_disjunction_elim (negative_stable _) ihAB
      · simpa only [Finset.coe_insert, context_insert] using ihA
      · simpa only [Finset.coe_insert, context_insert] using ihB
  | implIntro _ ih =>
      apply Derives.implIntro
      simpa only [Finset.coe_insert, context_insert] using ih
  | implElim _ _ ihAB ihA => exact .implElim ihAB ihA
  | negIntro _ ih =>
      apply Derives.negIntro
      simpa only [Finset.coe_insert, context_insert, negative] using ih
  | negElim _ _ ihA ihN => exact .negElim ihA ihN
  | falsumElim _ ih => exact .falsumElim ih
  | @classicalContradiction Γ A _ ih =>
      apply Derives.implElim ((show Derives ∅
        (impl (neg (neg (negative A))) (negative A)) from negative_stable A).weaken
          (Set.empty_subset _))
      apply Derives.negIntro
      simpa only [Finset.coe_insert, context_insert, negative] using ih

theorem classical_iff [DecidableEq α] (Γ : Finset (PropFormula α))
    (A : PropFormula α) :
    Lemmatheca.MathematicalLogic.Propositional.Derives Γ A ↔
      Derives (context (Γ : Set (PropFormula α))) (negative A) := by
  constructor
  · exact classical_translate
  · intro h
    have hrep : Derives ((Γ : Set (PropFormula α)) ∪ doubleNegationSchema) (negative A) := by
      apply h.replace
      rintro _ ⟨B, hB, rfl⟩
      apply (classical_iff_dne Γ (negative B)).mp
      exact .implElim ((Lemmatheca.MathematicalLogic.Propositional.Derives.conjElimLeft
        (negative_classical_equivalence B)).weaken (Finset.empty_subset Γ)) (.assumption hB)
    have hn : Lemmatheca.MathematicalLogic.Propositional.Derives Γ (negative A) :=
      (classical_iff_dne Γ (negative A)).mpr hrep
    exact .implElim ((Lemmatheca.MathematicalLogic.Propositional.Derives.conjElimRight
      (negative_classical_equivalence A)).weaken (Finset.empty_subset Γ)) hn

theorem theory_iff [DecidableEq α] (Γ : Set (PropFormula α)) (A : PropFormula α) :
    Lemmatheca.MathematicalLogic.PropositionalCompactness.TheoryDerives Γ A ↔
      Derives (context Γ) (negative A) := by
  classical
  constructor
  · rintro ⟨D, hD, hd⟩
    exact (classical_translate hd).weaken (Set.image_mono hD)
  · intro h
    obtain ⟨E, hf, hs, hE⟩ := finite_support.mp h
    obtain ⟨D, hD, hfin, hd⟩ :=
      (Set.exists_subset_image_finite_and (f := negative) (s := Γ)
        (p := fun T => Derives T (negative A))).mp ⟨E, hs, hf, hE⟩
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · simpa only [hfin.coe_toFinset] using hD
    · apply (classical_iff hfin.toFinset A).mpr
      simpa only [hfin.coe_toFinset, context] using hd

end Lemmatheca.ProofTheory.Intuitionistic.NegativeTranslation
