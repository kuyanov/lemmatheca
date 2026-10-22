import Lemmatheca.CountableSaturatedModels.CountableChains
import Lemmatheca.AtomicAndPrimeModels.AtomicConstruction

/-! The two countable-model existence criteria and the varying-arity omission argument. -/
namespace Lemmatheca.ModelTheory.CountableSaturatedModels

open FirstOrder FirstOrder.Language
open Types IsolatedTypes AtomicAndPrimeModels

variable {L : Language.{0, 0}} {T : L.Theory}

/-- The outer chain gives a countable saturated elementary extension of the specified source. -/
theorem countable_saturated_extension [Countable L.Symbols] (h : Small T)
    (M : T.ModelType.{0, 0, 0}) [Countable M] :
    ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧ Saturation.OmegaSaturated L N ∧
      Nonempty (M ↪ₑ[L] N) := by
  obtain ⟨D, h0, hD⟩ := exists_saturatingChain h M
  let U := Classical.choice (CountableChain.exists_union D)
  have he : Nonempty (M ↪ₑ[L] D.stage 0) := by
    rw [h0]
    exact ⟨ElementaryEmbedding.refl L M⟩
  obtain ⟨e⟩ := he
  exact ⟨U.model, U.countable_model, union_saturated D hD U,
    ⟨(U.inclusion 0).comp e⟩⟩

theorem exists_countable_saturated [Countable L.Symbols] (hT : T.IsComplete) (h : Small T) :
    ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧ Saturation.OmegaSaturated L N := by
  let M := hT.1.some
  obtain ⟨N, hc, _, _⟩ := CountableCategoricity.countable_realization
    (T.typeOf (fun i : Fin 0 => Fin.elim0 i : Fin 0 → M))
  let := hc
  obtain ⟨P, hP, hs, _⟩ := countable_saturated_extension h N
  exact ⟨P, hP, hs⟩

/-- A countable model accepting elementary embeddings of every countable T-model. -/
def CountableUniversal (T : L.Theory) (U : Type) [L.Structure U] : Prop :=
  Countable U ∧ ∀ N : T.ModelType.{0, 0, 0}, Countable N → Nonempty (N ↪ₑ[L] U)

variable {U : Type} [L.Structure U] [Nonempty U] [U ⊨ T]

theorem saturated_realizes_types [Countable L.Symbols] (hT : T.IsComplete)
    (hU : Saturation.OmegaSaturated L U) (n : ℕ) (p : T.CompleteType (Fin n)) :
    ∃ b : Fin n → U, Realizes (formulas p) b := by
  obtain ⟨N, hc, a, ha⟩ := CountableCategoricity.countable_realization p
  let := hc
  obtain ⟨f, _⟩ := Saturation.countable_embedding hU
    (PartialElementaryMaps.FiniteMap.empty (hT.models_elementarily_equivalent N U))
  exact ⟨f ∘ a, fun φ hφ => (f.map_formula φ a).mpr (ha φ hφ)⟩

theorem small_of_saturated [Countable L.Symbols] [Countable U]
    (hT : T.IsComplete) (hU : Saturation.OmegaSaturated L U) : Small T := by
  intro n
  have hs : Function.Surjective (fun b : Fin n → U => T.typeOf b) := by
    intro p
    obtain ⟨b, hb⟩ := saturated_realizes_types hT hU n p
    exact ⟨b, ((realizes_complete_iff p b).mp hb).symm⟩
  exact hs.countable

theorem saturated_universal [Countable U] (hT : T.IsComplete)
    (hU : Saturation.OmegaSaturated L U) : CountableUniversal T U := by
  refine ⟨inferInstance, fun N hc => ?_⟩
  let := hc
  obtain ⟨f, _⟩ := Saturation.countable_embedding hU
    (PartialElementaryMaps.FiniteMap.empty (hT.models_elementarily_equivalent N U))
  exact ⟨f⟩

omit [Nonempty U] [U ⊨ T] in
theorem universal_realizes_types [Countable L.Symbols] (hU : CountableUniversal T U)
    (n : ℕ) (p : T.CompleteType (Fin n)) :
    ∃ b : Fin n → U, Realizes (formulas p) b := by
  obtain ⟨N, hc, a, ha⟩ := CountableCategoricity.countable_realization p
  obtain ⟨f⟩ := hU.2 N hc
  exact ⟨f ∘ a, fun φ hφ => (f.map_formula φ a).mpr (ha φ hφ)⟩

theorem small_of_universal [Countable L.Symbols] (hU : CountableUniversal T U) :
    Small T := by
  let := hU.1
  intro n
  have hs : Function.Surjective (fun b : Fin n → U => T.typeOf b) := by
    intro p
    obtain ⟨b, hb⟩ := universal_realizes_types hU n p
    exact ⟨b, ((realizes_complete_iff p b).mp hb).symm⟩
  exact hs.countable

theorem small_iff_countable_saturated [Countable L.Symbols] (hT : T.IsComplete) :
    Small T ↔ ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧ Saturation.OmegaSaturated L N := by
  constructor
  · exact exists_countable_saturated hT
  · rintro ⟨N, hc, hs⟩
    let := hc
    exact small_of_saturated (U := N) hT hs

theorem small_iff_countable_universal [Countable L.Symbols] (hT : T.IsComplete) :
    Small T ↔ ∃ N : T.ModelType.{0, 0, 0}, CountableUniversal T N := by
  constructor
  · intro h
    obtain ⟨N, hc, hs⟩ := exists_countable_saturated hT h
    let := hc
    exact ⟨N, saturated_universal hT hs⟩
  · rintro ⟨N, hu⟩
    exact small_of_universal hu

/-- All the nonisolated types, retaining the individual arity as part of the index. -/
abbrev NonisolatedTypes (T : L.Theory) :=
  Σ n : ℕ, {p : T.CompleteType (Fin n) // ¬Isolated T p}

theorem countable_nonisolated (h : Small T) : Countable (NonisolatedTypes T) := by
  let : ∀ n, Countable (T.CompleteType (Fin n)) := h
  infer_instance

theorem small_exists_countable_atomic [Countable L.Symbols] (hT : T.IsComplete)
    (h : Small T) : ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧ IsAtomic T N := by
  classical
  let := countable_nonisolated h
  obtain ⟨N, SN, hne, hc, hmodel, homit⟩ := OmittingTypes.exists_countable_omitting
    (I := NonisolatedTypes T) (n := fun i => i.1) hT hT.1
    (fun i => i.2.val) (fun i => i.2.property)
  let := SN
  let := hne
  let := hmodel
  refine ⟨Theory.ModelType.of T N, hc, fun n a => ?_⟩
  by_contra hn
  let i : NonisolatedTypes T := ⟨n, T.typeOf a, hn⟩
  apply homit i
  exact ⟨a, fun φ hφ => Theory.CompleteType.formula_mem_typeOf.mp hφ⟩

theorem small_exists_prime [Countable L.Symbols] (hT : T.IsComplete) (h : Small T) :
    ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧ IsPrime T N := by
  obtain ⟨N, hc, ha⟩ := small_exists_countable_atomic hT h
  let := hc
  exact ⟨N, hc, countable_atomic_prime hT ha⟩

theorem categorical_small [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T) : Small T := by
  intro n
  let := (CountableCategoricity.categorical_iff_finite_types hT hInf).mp hcat n
  infer_instance

theorem categorical_models_saturated_prime [Countable L.Symbols] [Countable U]
    (hT : T.IsComplete) (hInf : ∃ N : T.ModelType.{0, 0, 0}, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T) :
    Saturation.OmegaSaturated L U ∧ IsPrime T U := by
  have hs := categorical_small hT hInf hcat
  obtain ⟨N, hc, hsat⟩ := exists_countable_saturated hT hs
  let := hc
  let : Infinite N := CountableCategoricity.models_infinite hT hInf
  let : Infinite U := CountableCategoricity.models_infinite hT hInf
  obtain ⟨e⟩ := hcat N (Theory.ModelType.of T U)
    (Cardinal.mk_eq_aleph0 N) (Cardinal.mk_eq_aleph0 U)
  have ha : IsAtomic T U := fun n a =>
    (CountableCategoricity.categorical_iff_isolated hT hInf).mp hcat n (T.typeOf a)
  exact ⟨(Saturation.isomorphism_invariant e).mp hsat, countable_atomic_prime hT ha⟩

end Lemmatheca.ModelTheory.CountableSaturatedModels
