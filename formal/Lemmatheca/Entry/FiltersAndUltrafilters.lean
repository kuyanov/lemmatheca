import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Order.Filter.Cofinite

namespace Lemmatheca.Entry.FiltersAndUltrafilters
open Set Filter
universe u

def IsPrincipal {α : Type u} (F : Filter α) : Prop :=
  ∃ S : Set α, S.Nonempty ∧ F = principal S

def HasFiniteIntersectionProperty {α : Type u} (B : Set (Set α)) : Prop :=
  ∀ t : Set (Set α), t ⊆ B → t.Finite → (⋂₀ t).Nonempty

theorem tails_example :
    (∀ n : ℕ, Set.Ici n ∈ (cofinite : Filter ℕ)) ∧
    (∀ t : Finset ℕ, (⋂ n ∈ t, Set.Ici n) = Set.Ici (t.sup id)) ∧
    (⋂ n : ℕ, Set.Ici n) = ∅ := by sorry

theorem tails_generate : generate (Set.range (fun n : ℕ => Set.Ici n)) =
    (cofinite : Filter ℕ) := by sorry

theorem cofinite_parity :
    {n : ℕ | n % 2 = 0} ∉ (cofinite : Filter ℕ) ∧
    {n : ℕ | n % 2 = 1} ∉ (cofinite : Filter ℕ) := by sorry

theorem finite_partition {α ι : Type u} [Finite ι] (U : Ultrafilter α)
    (A : ι → Set α) (hc : (⋃ i, A i) = univ)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∃! i, A i ∈ U := by sorry

theorem principal_ultrafilter_iff {α : Type u} (U : Ultrafilter α) :
    IsPrincipal (U : Filter α) ↔ ∃ x : α, U = pure x := by sorry

theorem nonprincipal_iff_cofinite {α : Type u} [Infinite α] (U : Ultrafilter α) :
    ¬ IsPrincipal (U : Filter α) ↔ (U : Filter α) ≤ cofinite := by sorry

theorem finite_changes {α : Type u} (U : Ultrafilter α)
    (hU : (U : Filter α) ≤ cofinite) (A B : Set α)
    (h : ((A \ B) ∪ (B \ A)).Finite) : A ∈ U ↔ B ∈ U := by sorry

theorem parity_extensions : ∃ U V : Ultrafilter ℕ,
    (U : Filter ℕ) ≤ cofinite ∧ (V : Filter ℕ) ≤ cofinite ∧
    {n : ℕ | n % 2 = 0} ∈ U ∧ {n : ℕ | n % 2 = 1} ∈ V ∧ U ≠ V := by sorry

end Lemmatheca.Entry.FiltersAndUltrafilters
