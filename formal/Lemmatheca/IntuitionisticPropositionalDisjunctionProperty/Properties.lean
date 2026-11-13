import Lemmatheca.IntuitionisticPropositionalDisjunctionProperty.Gluing
import Lemmatheca.IntuitionisticKripkeSemantics.Constructions
import Lemmatheca.IntuitionisticPropositionalKripkeCompleteness.CanonicalModel

/-! Disjunction choices and substitution-admissible rules in the numbered-atom language. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.DisjunctionProperty

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

/-- A failed deduction has an actual rooted model, preserving the precise premise set. -/
theorem rooted_countermodel (Γ : Set (PropFormula ℕ)) (A : PropFormula ℕ)
    (h : ¬ Derives Γ A) :
    ∃ (W : Type) (r : Preorder W) (M : @Kripke.Model ℕ W r) (w : W),
      (∀ z, @LE.le W r.toLE w z) ∧ @Kripke.Countermodel ℕ W r M w Γ A := by
  let T := Canonical.extensionWorld Γ A h
  let W := {U : Canonical.PrimeWorld // T ≤ U}
  refine ⟨W, inferInstance, Kripke.generated Canonical.canonicalModel T,
    ⟨T, le_rfl⟩, ?_, ?_⟩
  · intro z
    exact z.property
  · exact Kripke.generated_countermodel Canonical.canonicalModel T Γ A
      (Canonical.canonical_countermodel h)

private theorem glue_not_disjunction {W₀ W₁ : Type} [Preorder W₀] [Preorder W₁]
    (M₀ : Kripke.Model ℕ W₀) (M₁ : Kripke.Model ℕ W₁) (w₀ : W₀) (w₁ : W₁)
    (A B : PropFormula ℕ) (hA : ¬ Kripke.Forces M₀ w₀ A)
    (hB : ¬ Kripke.Forces M₁ w₁ B) :
    ¬ Kripke.Forces (glue M₀ M₁) .root (disj A B) := by
  rintro (ha | hb)
  · apply hA
    apply (forces_left M₀ M₁ w₀ A).mp
    exact Kripke.forces_mono _ _
      (show (World.root : World W₀ W₁) ≤ .left w₀ from trivial) ha
  · apply hB
    apply (forces_right M₀ M₁ w₁ B).mp
    exact Kripke.forces_mono _ _
      (show (World.root : World W₀ W₁) ≤ .right w₁ from trivial) hb

/-- The theorem disjunction property, including the immediate introduction converse. -/
theorem disjunction_property (A B : PropFormula ℕ) :
    Derives ∅ (disj A B) ↔ Derives ∅ A ∨ Derives ∅ B := by
  classical
  constructor
  · intro h
    by_contra hn
    have hA : ¬ Derives ∅ A := fun ha => hn (Or.inl ha)
    have hB : ¬ Derives ∅ B := fun hb => hn (Or.inr hb)
    obtain ⟨W₀, r₀, M₀, w₀, _hw₀, hc₀⟩ := rooted_countermodel ∅ A hA
    obtain ⟨W₁, r₁, M₁, w₁, _hw₁, hc₁⟩ := rooted_countermodel ∅ B hB
    let : Preorder W₀ := r₀
    let : Preorder W₁ := r₁
    apply glue_not_disjunction M₀ M₁ w₀ w₁ A B hc₀.2 hc₁.2
    exact Kripke.sound h (glue M₀ M₁) .root (by
      intro D hD
      cases hD)
  · rintro (h | h)
    · exact .disjIntroLeft h
    · exact .disjIntroRight h

/-- The same choice remains valid under one negated assumption. -/
theorem negated_premise_disjunction (C A B : PropFormula ℕ)
    (h : Derives {neg C} (disj A B)) :
    Derives {neg C} A ∨ Derives {neg C} B := by
  classical
  by_contra hn
  have hA : ¬ Derives {neg C} A := fun ha => hn (Or.inl ha)
  have hB : ¬ Derives {neg C} B := fun hb => hn (Or.inr hb)
  obtain ⟨W₀, r₀, M₀, w₀, hw₀, hc₀⟩ := rooted_countermodel {neg C} A hA
  obtain ⟨W₁, r₁, M₁, w₁, hw₁, hc₁⟩ := rooted_countermodel {neg C} B hB
  let : Preorder W₀ := r₀
  let : Preorder W₁ := r₁
  have hroot : Kripke.Forces (glue M₀ M₁) .root (neg C) :=
    (root_negation M₀ M₁ w₀ w₁ hw₀ hw₁ C).mpr
      ⟨hc₀.1 _ (by simp), hc₁.1 _ (by simp)⟩
  apply glue_not_disjunction M₀ M₁ w₀ w₁ A B hc₀.2 hc₁.2
  exact Kripke.sound h (glue M₀ M₁) .root (by
    intro D hD
    rcases hD with rfl
    exact hroot)

/-- A derivable single-premise rule permits its premise as an open assumption. -/
def DerivableRule (P Q : PropFormula ℕ) : Prop := Derives {P} Q

/-- Admissibility requires theorem preservation under every simultaneous substitution. -/
def Admissible (P Q : PropFormula ℕ) : Prop :=
  ∀ σ : ℕ → PropFormula ℕ, Derives ∅ (subst σ P) → Derives ∅ (subst σ Q)

theorem derivable_admissible (P Q : PropFormula ℕ) (h : DerivableRule P Q) :
    Admissible P Q := by
  intro σ hp
  have hh : Derives {P} Q := h
  apply (hh.substitute σ).replace
  intro D hD
  rcases hD with ⟨E, hE, rfl⟩
  rcases hE with rfl
  exact hp

/-- The native premise of the corrected negated-antecedent Harrop rule. -/
def harropPremise (C A B : PropFormula ℕ) : PropFormula ℕ := impl (neg C) (disj A B)

/-- The native conclusion is a disjunction of two implications with the same negated premise. -/
def harropConclusion (C A B : PropFormula ℕ) : PropFormula ℕ :=
  disj (impl (neg C) A) (impl (neg C) B)

/-- The proof argument gives a theorem implication, not only a theorem disjunction. -/
theorem harrop_choice (C A B : PropFormula ℕ) (h : Derives ∅ (harropPremise C A B)) :
    Derives ∅ (impl (neg C) A) ∨ Derives ∅ (impl (neg C) B) := by
  have hd := (deduction (Γ := (∅ : Set (PropFormula ℕ)))
    (A := neg C) (B := disj A B)).mpr h
  rcases negated_premise_disjunction C A B (by simpa using hd) with hA | hB
  · exact Or.inl (.implIntro (by simpa using hA))
  · exact Or.inr (.implIntro (by simpa using hB))

/-- Full uniform-substitution admissibility for arbitrary instances of the Harrop rule. -/
theorem harrop_admissible (C A B : PropFormula ℕ) :
    Admissible (harropPremise C A B) (harropConclusion C A B) := by
  intro σ hp
  rcases harrop_choice (subst σ C) (subst σ A) (subst σ B) hp with hA | hB
  · exact .disjIntroLeft hA
  · exact .disjIntroRight hB

end Lemmatheca.ProofTheory.Intuitionistic.DisjunctionProperty
