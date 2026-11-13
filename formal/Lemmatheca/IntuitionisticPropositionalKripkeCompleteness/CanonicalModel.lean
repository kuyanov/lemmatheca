import Lemmatheca.IntuitionisticPropositionalKripkeCompleteness.PrimeExtension
import Lemmatheca.IntuitionisticKripkeSemantics.Models
import Mathlib.Order.ULift

/-! One fixed canonical inclusion model, its native truth lemma, and strong completeness. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Canonical

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe v

/-- All prime theories, ordered by inclusion through their underlying sets. -/
abbrev PrimeWorld := {T : Set Formula // IsPrime T}

/-- The specified extension is the actual chosen counterexample world. -/
noncomputable def extensionWorld (Γ : Set Formula) (B : Formula) (h : ¬ Derives Γ B) :
    PrimeWorld := ⟨extension Γ B, extension_prime h⟩

/-- This model is chosen independently of every premise set and conclusion. -/
noncomputable def canonicalModel : Kripke.Model ℕ PrimeWorld where
  world_nonempty := ⟨extensionWorld ∅ falsum empty_not_derives_falsum⟩
  valuation T p := atom p ∈ T.val
  persistent hTU _ h := hTU h

theorem canonical_truth (A : Formula) (T : PrimeWorld) :
    Kripke.Forces canonicalModel T A ↔ A ∈ T.val := by
  classical
  induction A generalizing T with
  | atom p => rfl
  | falsum =>
      constructor
      · intro h
        exact h.elim
      · intro h
        exact T.property.consistent (.assumption h)
  | neg A ih =>
      constructor
      · intro h
        by_contra hn
        obtain ⟨hU, hTU, hA⟩ := missing_negation_extension T.property hn
        let U : PrimeWorld := ⟨extension (insert A T.val) falsum, hU⟩
        exact h U hTU ((ih U).mpr hA)
      · intro h U hTU hA
        exact prime_negation U.property hTU h ((ih U).mp hA)
  | conj A B ihA ihB =>
      exact (and_congr (ihA T) (ihB T)).trans (prime_conj_iff T.property A B).symm
  | disj A B ihA ihB =>
      exact (or_congr (ihA T) (ihB T)).trans (prime_disj_iff T.property A B).symm
  | impl A B ihA ihB =>
      constructor
      · intro h
        by_contra hn
        obtain ⟨hU, hTU, hA, hnB⟩ := missing_implication_extension T.property hn
        let U : PrimeWorld := ⟨extension (insert A T.val) B, hU⟩
        exact hnB ((ihB U).mp (h U hTU ((ihA U).mpr hA)))
      · intro h U hTU hA
        exact (ihB U).mpr (prime_implication U.property hTU h ((ihA U).mp hA))

/-- The same fixed model in any world universe, with no change of theory, order or valuation. -/
noncomputable def liftedCanonicalModel : Kripke.Model ℕ (ULift.{v} PrimeWorld) where
  world_nonempty := ⟨ULift.up (extensionWorld ∅ falsum empty_not_derives_falsum)⟩
  valuation T p := atom p ∈ T.down.val
  persistent hTU _ h := hTU h

theorem lifted_canonical_forcing (A : Formula) (T : ULift.{v} PrimeWorld) :
    Kripke.Forces liftedCanonicalModel T A ↔ Kripke.Forces canonicalModel T.down A := by
  induction A generalizing T with
  | atom p => rfl
  | falsum => rfl
  | neg A ih =>
      constructor
      · intro h U hTU hA
        exact h (ULift.up U) hTU ((ih (ULift.up U)).mpr hA)
      · intro h U hTU hA
        exact h U.down hTU ((ih U).mp hA)
  | conj A B ihA ihB => exact and_congr (ihA T) (ihB T)
  | disj A B ihA ihB => exact or_congr (ihA T) (ihB T)
  | impl A B ihA ihB =>
      constructor
      · intro h U hTU hA
        exact (ihB (ULift.up U)).mp (h (ULift.up U) hTU ((ihA (ULift.up U)).mpr hA))
      · intro h U hTU hA
        exact (ihB U).mpr (h U.down hTU ((ihA U).mp hA))

theorem canonical_countermodel {Γ : Set Formula} {A : Formula} (h : ¬ Derives Γ A) :
    Kripke.Countermodel canonicalModel (extensionWorld Γ A h) Γ A := by
  constructor
  · intro B hB
    exact (canonical_truth B _).mpr (extension_contains Γ A hB)
  · intro hA
    exact extension_omits h ((canonical_truth A _).mp hA)

theorem strong_completeness (Γ : Set Formula) (A : Formula) :
    Derives Γ A ↔ Kripke.Entails.{0,v} Γ A := by
  classical
  constructor
  · intro h W _ M w hΓ
    exact Kripke.sound h M w hΓ
  · intro h
    by_contra hd
    let T := extensionWorld Γ A hd
    have hT : Kripke.Countermodel canonicalModel T Γ A := canonical_countermodel hd
    have hf : Kripke.Forces liftedCanonicalModel (ULift.up T) A :=
      h (ULift.{v} PrimeWorld) liftedCanonicalModel (ULift.up T) (by
        intro B hB
        exact (lifted_canonical_forcing B _).mpr (hT.1 B hB))
    exact hT.2 ((lifted_canonical_forcing A _).mp hf)

theorem finite_premise_consequence (Γ : Set Formula) (A : Formula) :
    Kripke.Entails.{0,v} Γ A ↔ ∃ D : Set Formula, D.Finite ∧ D ⊆ Γ ∧ Derives D A := by
  exact (strong_completeness.{v} Γ A).symm.trans finite_support

theorem finite_semantic_consequence (Γ : Set Formula) (A : Formula) :
    Kripke.Entails.{0,v} Γ A ↔
      ∃ D : Set Formula, D.Finite ∧ D ⊆ Γ ∧ Kripke.Entails.{0,v} D A := by
  rw [finite_premise_consequence.{v}]
  constructor
  · rintro ⟨D, hf, hs, hd⟩
    exact ⟨D, hf, hs, (strong_completeness.{v} D A).mp hd⟩
  · rintro ⟨D, hf, hs, hd⟩
    exact ⟨D, hf, hs, (strong_completeness.{v} D A).mpr hd⟩

/-- Pointed satisfiability over an arbitrary fixed universe of worlds. -/
def Satisfiable (Γ : Set Formula) : Prop :=
  ∃ (W : Type v) (r : Preorder W) (M : @Kripke.Model ℕ W r) (w : W),
    @Kripke.ForcesContext ℕ W r M w Γ

theorem satisfiable_iff_consistent (Γ : Set Formula) :
    Satisfiable.{v} Γ ↔ Consistent Γ := by
  constructor
  · rintro ⟨W, r, M, w, hΓ⟩ hd
    exact Kripke.sound hd M w hΓ
  · intro hc
    let T := extensionWorld Γ falsum hc
    refine ⟨ULift.{v} PrimeWorld, inferInstance, liftedCanonicalModel, ULift.up T, ?_⟩
    intro A hA
    apply (lifted_canonical_forcing A _).mpr
    apply (canonical_truth A _).mpr
    exact extension_contains Γ falsum hA

theorem satisfiability_compactness (Γ : Set Formula) :
    Satisfiable.{v} Γ ↔ ∀ D : Set Formula, D.Finite → D ⊆ Γ → Satisfiable.{v} D := by
  constructor
  · rintro ⟨W, r, M, w, hΓ⟩ D _ hs
    exact ⟨W, r, M, w, fun A hA => hΓ A (hs hA)⟩
  · intro h
    apply (satisfiable_iff_consistent.{v} Γ).mpr
    intro hd
    obtain ⟨D, hf, hs, hDed⟩ := finite_support.mp hd
    exact ((satisfiable_iff_consistent.{v} D).mp (h D hf hs)) hDed

/-- The precise canonical world produced from a consistent set satisfies all its premises. -/
theorem canonical_satisfies {Γ : Set Formula} (h : Consistent Γ) :
    Kripke.ForcesContext canonicalModel (extensionWorld Γ falsum h) Γ := by
  exact (canonical_countermodel h).1

def truthTheory {W : Type v} [Preorder W] (M : Kripke.Model ℕ W) (w : W) : Set Formula :=
  {A | Kripke.Forces M w A}

theorem truthTheory_prime {W : Type v} [Preorder W] (M : Kripke.Model ℕ W) (w : W) :
    IsPrime (truthTheory M w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hd
    exact Kripke.sound hd M w (fun _ hB => hB)
  · intro hd
    exact Kripke.sound hd M w (fun _ hB => hB)
  · intro A B h
    exact h

theorem canonical_truthTheory (T : PrimeWorld) : truthTheory canonicalModel T = T.val := by
  ext A
  exact canonical_truth A T

end Lemmatheca.ProofTheory.Intuitionistic.Canonical
