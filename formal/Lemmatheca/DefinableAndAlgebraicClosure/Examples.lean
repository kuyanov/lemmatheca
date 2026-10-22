import Lemmatheca.DefinableAndAlgebraicClosure.Closures
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.Order.Interval.Set.Infinite

namespace Lemmatheca.Entry.DefinableAndAlgebraicClosure

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Closures
open Lemmatheca.ModelTheory
open Lemmatheca.ModelTheory.QuantifierElimination
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

universe u

theorem two_point_closures {M : Type u} [Language.empty.Structure M] [Fintype M]
    (h : Fintype.card M = 2) :
    dcl Language.empty (∅ : Set M) = ∅ ∧ acl Language.empty (∅ : Set M) = Set.univ := by
  classical
  have : Nontrivial M := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨c, hcb⟩ := exists_ne b
    let g : M ≃[Language.empty] M := { toEquiv := Equiv.swap b c }
    have hg : Definability.Fixes g (∅ : Set M) := by simp [Definability.Fixes]
    have h := automorphism_fixes_dcl g hg b hb
    change (Equiv.swap b c) b = b at h
    exact hcb (by simpa only [Equiv.swap_apply_left] using h)
  · apply Set.eq_univ_of_forall
    intro b
    refine ⟨Set.univ, ?_, Set.toFinite _, Set.mem_univ b⟩
    change (∅ : Set M).Definable Language.empty (Set.univ : Set (Fin 1 → M))
    exact Set.definable_univ

theorem infinite_equality_closures {M : Type u} [Language.empty.Structure M]
    [Infinite M] (A : Set M) :
    dcl Language.empty A = A ∧ acl Language.empty A = A := by
  classical
  have hsub : acl Language.empty A ⊆ A := by
    rintro b ⟨s, hs, hfin, hb⟩
    obtain ⟨A₀, hA₀, hs₀⟩ := Set.definable_iff_finitely_definable.mp hs
    by_cases hba : b ∈ A₀
    · exact hA₀ hba
    · obtain ⟨d, hd⟩ := (hfin.union A₀.finite_toSet).exists_notMem
      have hds : d ∉ s := fun h => hd (Or.inl h)
      have hdA : d ∉ A₀ := fun h => hd (Or.inr h)
      let g : M ≃[Language.empty] M := { toEquiv := Equiv.swap b d }
      have hg : Definability.Fixes g (A₀ : Set M) := by
        intro a ha
        have hab : a ≠ b := fun h => hba (h ▸ ha)
        have had : a ≠ d := fun h => hdA (h ▸ ha)
        change (Equiv.swap b d) a = a
        exact Equiv.swap_apply_of_ne_of_ne hab had
      have hinv := Definability.definable_invariant hs₀ g hg (fun _ : Fin 1 => b)
      have hdb : g b ∈ s := hinv.mp hb
      change (Equiv.swap b d) b ∈ s at hdb
      exact False.elim (hds (by simpa only [Equiv.swap_apply_left] using hdb))
  exact ⟨Set.Subset.antisymm ((dcl_subset_acl A).trans hsub) (subset_dcl A),
    Set.Subset.antisymm hsub ((subset_dcl A).trans (dcl_subset_acl A))⟩

theorem strictDlo_closures {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] (A : Set M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    dcl binaryRelLanguage A = A ∧ acl binaryRelLanguage A = A := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  dsimp only
  have hsub : acl binaryRelLanguage A ⊆ A := by
    rintro b ⟨s, hs, hfin, hb⟩
    obtain ⟨t, ht, heq⟩ := Shared.strictDlo_definable_finite_union A s hs
    obtain ⟨c, hct, hbc⟩ := (Set.ext_iff.mp heq b).mp hb
    have hcf : c.realize.Finite := hfin.subset (by
      intro x hx
      rw [heq]
      exact ⟨c, hct, hx⟩)
    cases c with
    | empty => exact False.elim hbc
    | point a =>
      have hba : b = a := hbc
      exact hba ▸ ht (.point a) hct
    | interval lower upper =>
      exfalso
      cases lower with
      | none =>
        cases upper with
        | none =>
          exact Set.infinite_univ (by simpa [Cell.realize, Set.Iio_def, Set.Ioi_def, Set.Ioo_def] using hcf)
        | some u =>
          exact Set.Iio_infinite u (by simpa [Cell.realize, Set.Iio_def, Set.Ioi_def, Set.Ioo_def] using hcf)
      | some l =>
        cases upper with
        | none =>
          exact Set.Ioi_infinite l (by simpa [Cell.realize, Set.Iio_def, Set.Ioi_def, Set.Ioo_def] using hcf)
        | some u =>
          have hx : l < b ∧ b < u := by simpa [Cell.realize] using hbc
          exact Set.Ioo_infinite (hx.1.trans hx.2) (by simpa [Cell.realize, Set.Iio_def, Set.Ioi_def, Set.Ioo_def] using hcf)
  exact ⟨Set.Subset.antisymm ((dcl_subset_acl A).trans hsub) (subset_dcl A),
    Set.Subset.antisymm hsub ((subset_dcl A).trans (dcl_subset_acl A))⟩

end Lemmatheca.Entry.DefinableAndAlgebraicClosure
