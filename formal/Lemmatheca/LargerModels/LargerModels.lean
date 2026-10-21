import Lemmatheca.HenkinCompleteness.HenkinCompleteness
import Lemmatheca.ElementarySubmodels.ElementarySubmodels
import Mathlib.ModelTheory.Satisfiability

open Lemmatheca.MathematicalLogic

/-! Model sizes and model witnesses for the existing first-order proof calculus. -/

namespace Lemmatheca.ModelTheory.LargerModels

open FirstOrder FirstOrder.Language Cardinal CategoryTheory
open Lemmatheca.MathematicalLogic.FirstOrderProofs

universe u v

section Sizes

variable {L : Language.{u, u}} {M P : Type u} [L.Structure M] [L.Structure P]

/-- Arbitrary lower size bounds while retaining the given structure elementarily. -/
theorem arbitrarily_large_elementary_extension [Infinite M] (κ : Cardinal.{u}) :
    ∃ N : Bundled.{u, u} L.Structure, Nonempty (M ↪ₑ[L] N) ∧ κ ≤ #N := by
  let μ := max κ (max L.card #M)
  obtain ⟨N, he, hN⟩ := L.exists_elementaryEmbedding_card_eq_of_ge M μ
    (by simpa only [Cardinal.lift_id] using ((le_max_left L.card #M).trans
      (le_max_right κ (max L.card #M))))
    (by simpa only [Cardinal.lift_id] using ((le_max_right L.card #M).trans
      (le_max_right κ (max L.card #M))))
  exact ⟨N, he, hN ▸ le_max_left _ _⟩

/-- Restrict the specified elementary map to an elementary substructure containing its range. -/
theorem restrict_elementary_range (f : M ↪ₑ[L] P) (S : L.ElementarySubstructure P)
    (h : Set.range f ⊆ S) :
    ∃ g : M ↪ₑ[L] S, ∀ a, (g a : P) = f a := by
  let g : M → S := fun a => ⟨f a, h ⟨a, rfl⟩⟩
  refine ⟨⟨g, fun {_} φ a => ?_⟩, fun _ => rfl⟩
  exact (S.subtype.map_formula φ (g ∘ a)).symm.trans (f.map_formula φ a)

/-- A strict cardinal increase forces the elementary embedding to miss an element. -/
theorem proper_elementary_extension [Infinite M] :
    ∃ N : Bundled.{u, u} L.Structure, ∃ e : M ↪ₑ[L] N, ∃ b : N, ∀ a, e a ≠ b := by
  classical
  obtain ⟨N, ⟨e⟩, hN⟩ := arbitrarily_large_elementary_extension
    (L := L) (M := M) (Order.succ #M)
  have hns : ¬ Function.Surjective e := by
    intro hs
    exact (Order.lt_succ #M).not_ge (hN.trans (Cardinal.mk_le_of_surjective hs))
  obtain ⟨b, hb⟩ := not_forall.mp hns
  exact ⟨N, e, b, fun a ha => hb ⟨a, ha⟩⟩

theorem no_embedding_into_smaller {N : Type u} [L.Structure N] (h : #N < #M) :
    ¬ Nonempty (M ↪[L] N) := by
  rintro ⟨e⟩
  exact h.not_ge (Cardinal.mk_le_of_injective e.injective)

theorem nonisomorphic_of_card_ne {N : Type u} [L.Structure N] (h : #M ≠ #N) :
    ¬ Nonempty (M ≃[L] N) := by
  rintro ⟨e⟩
  exact h (Cardinal.mk_congr e.toEquiv)

end Sizes

section ModelWitnesses

variable {L : Language.{u, v}} [Countable L.Symbols] {T : L.Theory}

/-- Countable-language completeness for the actual sentence/fresh-constant calculus. -/
theorem consistent_iff_satisfiable : Consistent T ↔ T.IsSatisfiable := by
  constructor
  · intro hT
    obtain ⟨M, hM, hne, _, hm⟩ := HenkinCompleteness.countable_model_existence hT
    let := hM
    let := hne
    let := hm
    exact Theory.Model.isSatisfiable M
  · rintro ⟨M⟩
    exact theory_consistent_of_model M.is_model

theorem not_derives_iff_countermodel (θ : L.Sentence) :
    ¬ Derives T θ ↔ (insert θ.not T).IsSatisfiable := by
  classical
  rw [← HenkinCompleteness.consequence_iff_derives, Theory.models_iff_not_satisfiable]
  simp only [not_not, Set.union_singleton]

/-- Independence is about the two opposite syntactic nonderivability claims. -/
def Independent (T : L.Theory) (θ : L.Sentence) : Prop :=
  ¬ Derives T θ ∧ ¬ Derives T θ.not

theorem independent_iff_two_models (θ : L.Sentence) :
    Independent T θ ↔ (insert θ T).IsSatisfiable ∧ (insert θ.not T).IsSatisfiable := by
  classical
  constructor
  · rintro ⟨hpos, hneg⟩
    refine ⟨?_, (not_derives_iff_countermodel θ).mp hpos⟩
    obtain ⟨M⟩ := (not_derives_iff_countermodel θ.not).mp hneg
    have hm : M ⊨ insert θ T := by
      constructor
      intro φ hφ
      rcases Set.mem_insert_iff.mp hφ with hφ | hφ
      · subst φ
        have hθ := M.is_model.realize_of_mem (θ.not).not (Set.mem_insert _ _)
        simpa only [Sentence.realize_not, not_not] using hθ
      · exact M.is_model.realize_of_mem φ (Set.mem_insert_of_mem _ hφ)
    let := hm
    exact Theory.Model.isSatisfiable M
  · rintro ⟨⟨M⟩, hneg⟩
    refine ⟨(not_derives_iff_countermodel θ).mpr hneg, ?_⟩
    intro hproof
    have hθ := M.is_model.realize_of_mem θ (Set.mem_insert _ _)
    have hnθ := derives_sound hproof (default : Empty → M)
      (fun φ hφ => M.is_model.realize_of_mem φ (Set.mem_insert_of_mem _ hφ))
    exact hnθ hθ

/-- An external conditional model construction yields external relative consistency. -/
theorem relative_consistency {K : Language} [Countable K.Symbols] (S : K.Theory)
    (h : ∀ _M : Theory.ModelType.{u, v, max u v} T, S.IsSatisfiable) :
    Consistent T → Consistent S := by
  intro hT
  exact consistent_iff_satisfiable.mpr (h (consistent_iff_satisfiable.mp hT).some)

end ModelWitnesses

end Lemmatheca.ModelTheory.LargerModels
