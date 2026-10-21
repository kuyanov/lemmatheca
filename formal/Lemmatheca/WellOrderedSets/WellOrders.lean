import Mathlib.Order.InitialSeg
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.WellFoundedSet
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.PNat.Equiv
import Mathlib.Tactic

/-! Reusable WellOrders definitions and results. -/

/-!
# Well-orders: histories and partial recursive solutions

Non-strict orders use `LinearOrder`; well-foundedness concerns their strict `<`.
Initial segments are `IsLowerSet` subsets (including empty and full subsets).
The history at a point is a function on the subtype `Set.Iio a`.
-/

namespace Lemmatheca.SetTheory

universe u v
variable {α : Type u} {S : Type v}

theorem wellFounded_iff_induction (r : α → α → Prop) :
    WellFounded r ↔ ∀ P : α → Prop,
      (∀ a, (∀ b, r b a → P b) → P a) → ∀ a, P a := by
  constructor
  · intro h P step a
    exact h.induction a step
  · intro h
    exact ⟨h (Acc r) (fun a ih => Acc.intro a ih)⟩

section Ordered
variable [LinearOrder α]

/-- A rule for every point and every possible earlier history, with fixed value type. -/
def RecursionRule (α : Type u) [Preorder α] (S : Type v) :=
  (a : α) → (Set.Iio a → S) → S

/-- A function on a downward-closed domain obeying the given recursion rule. -/
structure PartialRecursiveSolution (Φ : RecursionRule α S) where
  domain : Set α
  lower : IsLowerSet domain
  value : domain → S
  equation : ∀ a : domain, value a =
    Φ a.val (fun b => value ⟨b.val, lower b.property.le a.property⟩)

theorem partial_recursive_solutions_agree [WellFoundedLT α] (Φ : RecursionRule α S)
    (h k : PartialRecursiveSolution Φ) :
    ∀ a (ha : a ∈ h.domain) (hk : a ∈ k.domain), h.value ⟨a, ha⟩ = k.value ⟨a, hk⟩ := by
  intro a
  induction a using (wellFounded_lt (α := α)).induction with
  | h a ih =>
    intro ha hk
    rw [h.equation ⟨a, ha⟩, k.equation ⟨a, hk⟩]
    congr 1
    funext b
    exact ih b.val b.property _ _

noncomputable def recursiveValue [WellFoundedLT α] (Φ : RecursionRule α S) : α → S :=
  wellFounded_lt.fix (fun a earlier => Φ a (fun b => earlier b.val b.property))

theorem recursion_exists_unique [WellFoundedLT α] (Φ : RecursionRule α S) :
    ∃! F : α → S, ∀ a, F a = Φ a (fun b => F b.val) := by
  refine ⟨recursiveValue Φ, ?_, ?_⟩
  · intro a
    exact wellFounded_lt.fix_eq _ a
  · intro F hF
    funext a
    induction a using (wellFounded_lt (α := α)).induction with
    | h a ih =>
      rw [hF, recursiveValue, wellFounded_lt.fix_eq]
      congr 1
      funext b
      exact ih b.val b.property

theorem three_case_induction [WellFoundedLT α] (P : α → Prop)
    (base : ∀ a, IsMin a → P a)
    (step : ∀ a b, a ⋖ b → P a → P b)
    (limit : ∀ b, Order.IsSuccLimit b → (∀ a, a < b → P a) → P b) :
    ∀ a, P a := by
  intro a
  induction a using (wellFounded_lt (α := α)).induction with
  | h a ih =>
    by_cases hlim : Order.IsSuccLimit a
    · exact limit a hlim ih
    · rcases Order.not_isSuccLimit_iff.mp hlim with hmin | hpred
      · exact base a hmin
      · obtain ⟨b, hb⟩ := Order.not_isSuccPrelimit_iff.mp hpred
        exact step b a hb (ih b hb.lt)

theorem finite_predecessor [Finite α] {b : α} (hb : ¬ IsMin b) :
    ∃ a, a ⋖ b := by
  classical
  have hn : (Set.Iio b).Nonempty := by
    simpa [isMin_iff_forall_not_lt] using hb
  obtain ⟨a, ha, hmax⟩ := (Set.Iio b).toFinite.exists_maximal hn
  refine ⟨a, ha, ?_⟩
  intro c hac hcb
  exact hac.not_ge (hmax hcb hac.le)

theorem recursion_empty_values_impossible [WellFoundedLT α] [Nonempty α] :
    IsEmpty (RecursionRule α Empty) := by
  classical
  let a := wellFounded_lt.min (Set.univ : Set α) Set.univ_nonempty
  have ha : ∀ b : Set.Iio a, False := by
    intro b
    exact wellFounded_lt.not_lt_min Set.univ (Set.mem_univ b.val) b.property
  exact ⟨fun Φ => Empty.elim (Φ a (fun b => False.elim (ha b)))⟩

end Ordered

end Lemmatheca.SetTheory

/-! Standard comparison relations, well-foundedness criteria, and natural
initial-segment identities. Integer comparison is pulled back along
`Equiv.intEquivNat`. -/

namespace Lemmatheca.SetTheory

open Lemmatheca.SetTheory

def integerEnumerationLT (a b : ℤ) : Prop := Equiv.intEquivNat a < Equiv.intEquivNat b

theorem noMin_not_wellFounded (A : Type*) [LinearOrder A] [Nonempty A]
    [NoMinOrder A] : ¬ WellFounded ((· < ·) : A → A → Prop) := by
  intro h
  obtain ⟨b, hb⟩ := exists_lt (h.min Set.univ Set.univ_nonempty)
  exact h.not_lt_min Set.univ (Set.mem_univ b) hb

theorem proper_positive_divisibility_wellFounded :
    WellFounded (fun a b : ℕ+ => a ∣ b ∧ a ≠ b) := by
  refine (measure (fun a : ℕ+ => a.val)).wf.mono ?_
  intro a b h
  have hd : a.val ∣ b.val := PNat.dvd_iff.mp h.1
  have hle := Nat.le_of_dvd b.property hd
  have hne : a.val ≠ b.val := fun he => h.2 (Subtype.ext he)
  exact lt_of_le_of_ne hle hne

theorem natural_segment_step (n : ℕ) :
    Set.Iio (n + 1) = Set.Iio n ∪ {n} := by
  ext k
  simp only [Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff]
  omega

theorem natural_segment_union : (⋃ n : ℕ, Set.Iio n) = Set.univ := by
  ext k
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_univ, iff_true]
  exact ⟨k + 1, by omega⟩

end Lemmatheca.SetTheory
