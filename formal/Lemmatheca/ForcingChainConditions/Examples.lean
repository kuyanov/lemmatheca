import Lemmatheca.ForcingChainConditions.BinaryMaps
import Lemmatheca.ForcingChainConditions.Values
import Lemmatheca.ForcingChainConditions.CardinalBounds

namespace Lemmatheca.Entry.ForcingChainConditions
open Set Cardinal Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingChainConditions
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

@[instance_reducible] def discreteTopOrder (I : Type u) : PartialOrder (Option I) where
  le p q := q = none ∨ p = q
  le_refl := by intro a; exact Or.inr rfl
  le_trans := by
    intro a b c hab hbc
    rcases hbc with rfl | rfl
    · exact Or.inl rfl
    · exact hab
  le_antisymm := by
    intro a b hab hba
    rcases hab with hb | hab
    · subst b
      exact hba.elim id Eq.symm
    · exact hab

@[instance_reducible] def discreteOrderTop (I : Type u) : @OrderTop (Option I) (discreteTopOrder I).toLE := by
  letI := discreteTopOrder I
  exact { top := none, le_top := by intro a; exact Or.inl rfl }

theorem discrete_top_counterexample (I : Type u) [Uncountable I] :
    @Antichain (Option I) (discreteTopOrder I) (Set.range some) ∧
      #(Set.range (some : I → Option I)) = #I ∧
      ¬@CCC (Option I) (discreteTopOrder I) := by
  classical
  let := discreteTopOrder I
  have hinj : Function.Injective (some : I → Option I) := Option.some_injective I
  have hant : Antichain (Set.range (some : I → Option I)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨r, hri, hrj⟩
    change (some i = none ∨ r = some i) at hri
    change (some j = none ∨ r = some j) at hrj
    have hi : r = some i := hri.resolve_left (Option.some_ne_none _)
    have hj : r = some j := hrj.resolve_left (Option.some_ne_none _)
    exact hne (hi.symm.trans hj)
  have hcard : #(Set.range (some : I → Option I)) = #I := by
    exact Cardinal.lift_injective (Cardinal.mk_range_eq_of_injective hinj)
  refine ⟨hant, hcard, ?_⟩
  intro hccc
  have hc := Cardinal.mk_le_aleph0_iff.mpr (hccc _ hant).to_subtype
  rw [hcard] at hc
  exact not_countable (Cardinal.mk_le_aleph0_iff.mp hc)

theorem countable_strict_bound_fails :
    max Cardinal.aleph0 #(Fin 1) = Cardinal.aleph0 ∧
      #(⋃ _ : Fin 1, (Set.univ : Set ℕ)) = Cardinal.aleph0 := by
  constructor
  · simp
  · have he : (⋃ _ : Fin 1, (Set.univ : Set ℕ)) = Set.univ :=
      Set.eq_univ_of_forall (fun n => Set.mem_iUnion.mpr ⟨⟨0, by decide⟩, Set.mem_univ n⟩)
    rw [he, Cardinal.mk_univ, Cardinal.mk_nat]


theorem aleph_singletons_counterexample :
    let κ := (Cardinal.aleph (Ordinal.omega0 : Ordinal.{u})).ord
    let C : ℕ → Set Ordinal.{u} := fun n => {(Cardinal.aleph (n : Ordinal.{u})).ord}
    (∀ n, (C n).Countable ∧ ∀ b ∈ C n, b < κ) ∧
      (⋃ n, C n).Countable ∧ (⋃ n, C n).Infinite ∧
      (∀ b < κ, ∃ c ∈ ⋃ n, C n, b ≤ c) ∧
      Cardinal.aleph0 < Cardinal.aleph (Ordinal.omega0 : Ordinal.{u}) := by
  classical
  let f : ℕ → Ordinal.{u} := fun n => (Cardinal.aleph (n : Ordinal.{u})).ord
  let κ := (Cardinal.aleph (Ordinal.omega0 : Ordinal.{u})).ord
  have hinj : Function.Injective f := by
    intro m n h
    have hn := Cardinal.isNormal_aleph.strictMono.injective (Cardinal.ord_injective h)
    exact_mod_cast hn
  have hsup : (⨆ n, f n) = κ := by
    simp only [f, κ, Cardinal.ord_aleph]
    exact Ordinal.apply_omega0_of_isNormal Ordinal.isNormal_omega
  change (∀ n, ({f n} : Set Ordinal.{u}).Countable ∧ ∀ b ∈ ({f n} : Set Ordinal.{u}), b < κ) ∧
    (⋃ n, ({f n} : Set Ordinal.{u})).Countable ∧
    (⋃ n, ({f n} : Set Ordinal.{u})).Infinite ∧
    (∀ b < κ, ∃ c ∈ ⋃ n, ({f n} : Set Ordinal.{u}), b ≤ c) ∧ _
  refine ⟨?_, Set.countable_iUnion (fun n => Set.countable_singleton (f n)), ?_, ?_, ?_⟩
  · intro n
    refine ⟨Set.countable_singleton _, ?_⟩
    intro b hb
    have he : b = f n := Set.mem_singleton_iff.mp hb
    rw [he]
    dsimp [f, κ]
    rw [Cardinal.ord_aleph, Cardinal.ord_aleph]
    exact Ordinal.omega_strictMono (Ordinal.natCast_lt_omega0 n)
  · have hr : (⋃ n, ({f n} : Set Ordinal.{u})) = Set.range f := by simp
    rw [hr]
    exact Set.infinite_range_of_injective hinj
  · intro b hb
    rw [← hsup, Ordinal.lt_iSup_iff] at hb
    obtain ⟨n, hn⟩ := hb
    exact ⟨f n, Set.mem_iUnion.mpr ⟨n, Set.mem_singleton _⟩, hn.le⟩
  · simp

end
end Lemmatheca.Entry.ForcingChainConditions
