import Lemmatheca.Entry.AxiomaticSetTheory
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

/-! The constructed omega is connected explicitly to Lean's natural numbers.
Arithmetic statements about `Nat` specialize along this bijection; ordinal casts
identify their addition, multiplication and order with the finite ordinals. -/
namespace Lemmatheca.Entry.NaturalNumbersAsSets
open Lemmatheca.Entry.AxiomaticSetTheory
open scoped ZFSet Ordinal
universe u v

noncomputable def naturalSet (n : ℕ) : ZFSet.{u} := (n : Ordinal.{u}).toZFSet

theorem omega_members (x : ZFSet.{u}) : x ∈ ZFSet.omega ↔ ∃ n, naturalSet n = x := by
  sorry

theorem omega_eq_ordinal : ZFSet.omega.{u} = Ordinal.omega0.toZFSet := by
  sorry

theorem omega_least (I : ZFSet.{u}) (hI : IsInductive I) : ZFSet.omega ⊆ I := by
  sorry

theorem omega_unique_least :
    ∃! W : ZFSet.{u}, IsInductive W ∧ ∀ I, IsInductive I → W ⊆ I := by
  sorry

theorem omega_subset_induction (A : ZFSet.{u}) (hA : A ⊆ ZFSet.omega)
    (hz : ∅ ∈ A) (hs : ∀ n ∈ A, insert n n ∈ A) : A = ZFSet.omega := by
  sorry

theorem omega_predicate_induction (P : ZFSet.{u} → Prop) (hz : P ∅)
    (hs : ∀ n ∈ ZFSet.omega, P n → P (insert n n)) : ∀ n ∈ ZFSet.omega, P n := by
  sorry

theorem omega_peano :
    (∀ n ∈ ZFSet.omega.{u}, insert n n ≠ ∅) ∧
    (∀ n ∈ ZFSet.omega.{u}, ∀ m ∈ ZFSet.omega, insert n n = insert m m → n = m) ∧
    (∀ n ∈ ZFSet.omega.{u}, n ≠ ∅ → ∃! m, m ∈ ZFSet.omega ∧ insert m m = n) := by
  sorry

theorem finite_ordinals (a : ZFSet.{u}) (ha : a.IsOrdinal) :
    a ∈ ZFSet.omega ↔ Finite a := by
  sorry

theorem omega_no_greatest : ∀ n ∈ ZFSet.omega.{u}, ∃ m ∈ ZFSet.omega, n ∈ m := by
  sorry

theorem naturalSet_order (m n : ℕ) :
    (naturalSet.{u} m ∈ naturalSet n ↔ m < n) ∧
      (naturalSet.{u} m ⊆ naturalSet n ↔ m ≤ n) := by
  sorry

theorem sequence_unique (C : Type v) (c : C) (g : C → C) :
    ∃! f : ℕ → C, f 0 = c ∧ ∀ n, f (n + 1) = g (f n) := by
  sorry

theorem sequence_parameter_unique (C : Type v) (c : C) (g : ℕ → C → C) :
    ∃! f : ℕ → C, f 0 = c ∧ ∀ n, f (n + 1) = g n (f n) := by
  sorry

theorem natural_additive_difference (m n : ℕ) : m ≤ n ↔ ∃! k, m + k = n := by
  sorry

theorem peano_system_unique (C : Type v) (c : C) (g : C → C)
    (hg : Function.Injective g) (hc : ∀ x, g x ≠ c)
    (hInd : ∀ A : Set C, c ∈ A → (∀ x ∈ A, g x ∈ A) → A = Set.univ) :
    ∃! f : ℕ → C, Function.Bijective f ∧ f 0 = c ∧ ∀ n, f (n + 1) = g (f n) := by
  sorry

def extraPointSucc : WithTop ℕ → WithTop ℕ
  | ⊤ => ⊤
  | (n : ℕ) => ((n + 1 : ℕ) : WithTop ℕ)

theorem extra_point_counterexample :
    Function.Injective extraPointSucc ∧ (∀ x, extraPointSucc x ≠ (0 : WithTop ℕ)) ∧
    (let A : Set (WithTop ℕ) := Set.range (fun n : ℕ => (n : WithTop ℕ))
     (0 : WithTop ℕ) ∈ A ∧ (∀ x ∈ A, extraPointSucc x ∈ A) ∧ A ≠ Set.univ) ∧
    (fun n : ℕ => (extraPointSucc^[n]) (0 : WithTop ℕ)) =
      (fun n : ℕ => (n : WithTop ℕ)) := by
  sorry

end Lemmatheca.Entry.NaturalNumbersAsSets
