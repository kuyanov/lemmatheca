import Lemmatheca.AxiomaticSetTheory.AxiomaticSetTheory

/-! The concrete least inductive set accompanying the infinity axiom. -/
set_option autoImplicit false
namespace Lemmatheca.SetTheory.NaturalNumbersAsSets
open Lemmatheca.SetTheory.AxiomaticSetTheory
open scoped ZFSet Ordinal
universe u

def naturalSet (n : ℕ) : ZFSet.{u} := ZFSet.mk (PSet.ofNat n)

private theorem naturalSet_zero : naturalSet.{u} 0 = ∅ := rfl

private theorem naturalSet_succ (n : ℕ) :
    naturalSet.{u} (n + 1) = insert (naturalSet n) (naturalSet n) := rfl

private theorem ofNat_naturalSet (n : ℕ) :
    ZFSet.mk (PSet.ofNat n) = naturalSet.{u} n := rfl

theorem omega_members (x : ZFSet.{u}) : x ∈ ZFSet.omega ↔ ∃ n, naturalSet n = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change (∃ n : ULift ℕ, PSet.Equiv x (PSet.ofNat n.down)) ↔
      ∃ n, naturalSet n = ZFSet.mk x
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n.down, (ofNat_naturalSet _).symm.trans (ZFSet.sound hn).symm⟩
    · rintro ⟨n,hn⟩
      refine ⟨⟨n⟩, ZFSet.exact ?_⟩
      exact hn.symm.trans (ofNat_naturalSet _).symm

theorem omega_least (I : ZFSet.{u}) (hI : IsInductive I) : ZFSet.omega ⊆ I := by
  have hn : ∀ n : ℕ, naturalSet.{u} n ∈ I := by
    intro n
    induction n with
    | zero => rw [naturalSet_zero]; exact hI.1
    | succ n ih => rw [naturalSet_succ]; exact hI.2 _ ih
  intro x hx
  obtain ⟨n,rfl⟩ := (omega_members x).mp hx
  exact hn n

theorem omega_unique_least :
    ∃! W : ZFSet.{u}, IsInductive W ∧ ∀ I, IsInductive I → W ⊆ I := by
  have hω : IsInductive ZFSet.omega.{u} := ⟨ZFSet.omega_zero, fun _ => ZFSet.omega_succ⟩
  refine ⟨ZFSet.omega, ⟨hω, omega_least⟩, ?_⟩
  intro W hW
  exact le_antisymm (hW.2 _ hω) (omega_least W hW.1)

end Lemmatheca.SetTheory.NaturalNumbersAsSets
