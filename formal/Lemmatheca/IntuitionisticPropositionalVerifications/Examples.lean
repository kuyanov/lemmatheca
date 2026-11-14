import Lemmatheca.IntuitionisticPropositionalVerifications.Subformulas

namespace Lemmatheca.Entry.IntuitionisticPropositionalVerifications

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.ProofTheory.Intuitionistic
open PropFormula Verification

universe u
variable {α : Type u} [DecidableEq α]

/-- Explicit conjunction producer, retained-principal consumer, and their cut. -/
def conjunctionDetour (p q : α) : CutFree.CutProof {atom p, atom q} (atom p) := by
  let Γ : Finset (PropFormula α) := {atom p, atom q}
  let producer : CutFree.CutProof Γ (conj (atom p) (atom q)) :=
    .conjRight (.atom (by simp [Γ])) (.atom (by simp [Γ]))
  let consumer : CutFree.CutProof (insert (conj (atom p) (atom q)) Γ) (atom p) :=
    .conjLeft (A := atom p) (B := atom q) (by simp) (.atom (by simp [Γ]))
  simpa only [Finset.union_self] using CutFree.CutProof.cut producer consumer

/-- The displayed one-leaf verification with the very same endsequent. -/
def conjunctionResult (p q : α) : Normal {atom p, atom q} (atom p) :=
  .neutral (.assumption (by simp))

def identityVerification (A : PropFormula α) : Normal ∅ (impl A A) :=
  .implIntro (.neutral (.assumption (by simp)))

theorem no_normal_to_neutral :
    ¬ Nonempty (∀ {Γ : Finset (PropFormula α)} {A : PropFormula α}, Normal Γ A → Neutral Γ A) := by
  rintro ⟨f⟩
  exact no_closed_neutral (f (identityVerification (falsum : PropFormula α)))

theorem no_atomic_excluded_middle (p : α) :
    ¬ Nonempty (Normal ∅ (disj (atom p) (neg (atom p)))) := by
  rintro ⟨v⟩
  cases extractDisjunction v with
  | inl v =>
      have h := boolean_sound v.toSequent.to_natural (fun _ => false) (by simp)
      simp [eval] at h
  | inr v =>
      have h := boolean_sound v.toSequent.to_natural (fun _ => true) (by simp)
      simp [eval] at h

end Lemmatheca.Entry.IntuitionisticPropositionalVerifications
