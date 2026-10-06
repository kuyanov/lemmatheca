import Lemmatheca.SetTheory.NaturalNumbersAsSets

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false

namespace Lemmatheca.Entry.NaturalNumbersAsSets
open Lemmatheca.SetTheory.NaturalNumbersAsSets
open Lemmatheca.SetTheory.AxiomaticSetTheory
open scoped ZFSet Ordinal
universe u v

def extraPointSucc : WithTop ℕ → WithTop ℕ
  | ⊤ => ⊤
  | (n : ℕ) => ((n + 1 : ℕ) : WithTop ℕ)

theorem extra_point_counterexample :
    Function.Injective extraPointSucc ∧ (∀ x, extraPointSucc x ≠ (0 : WithTop ℕ)) ∧
    (let A : Set (WithTop ℕ) := Set.range (fun n : ℕ => (n : WithTop ℕ))
     (0 : WithTop ℕ) ∈ A ∧ (∀ x ∈ A, extraPointSucc x ∈ A) ∧ A ≠ Set.univ) ∧
    (fun n : ℕ => (extraPointSucc^[n]) (0 : WithTop ℕ)) =
      (fun n : ℕ => (n : WithTop ℕ)) := by
  have hinj : Function.Injective extraPointSucc := by
    intro a b h
    cases a with
    | top =>
      cases b with
      | top => rfl
      | coe b => cases h
    | coe a =>
      cases b with
      | top => cases h
      | coe b => exact congrArg some (Nat.succ_inj.mp (Option.some.inj h))
  refine ⟨hinj, ?_, ?_, ?_⟩
  · intro x h
    cases x with
    | top => cases h
    | coe n => exact Nat.noConfusion (Option.some.inj h)
  · refine ⟨⟨0, rfl⟩, ?_, ?_⟩
    · rintro x ⟨n, rfl⟩
      exact ⟨n+1, rfl⟩
    · intro he
      have hm : (⊤ : WithTop ℕ) ∈ Set.range (fun n : ℕ => (n : WithTop ℕ)) :=
        he.symm ▸ Set.mem_univ _
      obtain ⟨n, hn⟩ := hm
      cases hn
  · funext n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',ih]; rfl

end Lemmatheca.Entry.NaturalNumbersAsSets
