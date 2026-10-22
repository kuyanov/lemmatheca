import Lemmatheca.CountableCategoricity.Orbits
import Lemmatheca.ElementarySubmodels.ElementarySubmodels
import Lemmatheca.AtomicAndPrimeModels.AtomicModels

/-! Native countable categoricity statements; atomic interfaces supply their later proofs. -/
namespace Lemmatheca.ModelTheory.CountableCategoricity

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.IsolatedTypes

variable {L : Language.{0, 0}} {T : L.Theory}

/-- Completeness transfers every finite lower size bound from an infinite model. -/
theorem models_infinite (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N)
    {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T] : Infinite M := by
  obtain ⟨N, hN⟩ := hInf
  let := hN
  exact (hT.models_elementarily_equivalent N M).infinite

/-- Downward Löwenheim–Skolem retains the particular tuple realizing the given complete type. -/
theorem countable_realization [Countable L.Symbols] {n : ℕ}
    (p : T.CompleteType (Fin n)) :
    ∃ N : Theory.ModelType.{0, 0, 0} T, Countable N ∧
      ∃ a : Fin n → N, Realizes (formulas p) a := by
  obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in p
  obtain ⟨S, hS, hcount⟩ := ElementarySubmodels.exists_countable_elementarySubstructure
    (L := L) (Set.range a) (Set.finite_range a).countable
  let : S ⊨ T := (S.subtype.theory_model_iff T).mpr N.is_model
  let b : Fin n → S := fun i => ⟨a i, hS (Set.mem_range_self i)⟩
  refine ⟨Theory.ModelType.of T S, hcount, b, ?_⟩
  intro φ hφ
  apply (S.subtype.map_formula φ b).mp
  have hb : S.subtype ∘ b = a := rfl
  rw [hb]
  exact ((realizes_complete_iff p a).mpr ha.symm) φ hφ

/-- The existence clause in countable categoricity is supplied under the entry's standing hypotheses. -/
theorem countable_infinite_model [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N) :
    ∃ N : Theory.ModelType.{0, 0, 0} T, Countable N ∧ Infinite N := by
  let N := hT.1.some
  obtain ⟨M, hc, _, _⟩ := countable_realization
    (T.typeOf (fun i : Fin 0 => Fin.elim0 i : Fin 0 → N))
  exact ⟨M, hc, models_infinite hT hInf⟩

/-- Completeness fixes the unique zero-type even when the axiom set is not deductively closed. -/
theorem zero_types_unique (hT : T.IsComplete) (p q : T.CompleteType (Fin 0)) : p = q := by
  obtain ⟨M, a, ha⟩ := T.exists_modelType_is_realized_in p
  obtain ⟨N, b, hb⟩ := T.exists_modelType_is_realized_in q
  rw [← ha, ← hb]
  apply (AtomicAndPrimeModels.typeOf_eq_iff a b).mpr
  intro φ
  let σ := existentialSentence φ
  have hm : M ⊨ σ ↔ φ.Realize a :=
    (existentialSentence_realize φ).trans ⟨fun ⟨c, hc⟩ => Subsingleton.elim c a ▸ hc,
      fun h => ⟨a, h⟩⟩
  have hn : N ⊨ σ ↔ φ.Realize b :=
    (existentialSentence_realize φ).trans ⟨fun ⟨c, hc⟩ => Subsingleton.elim c b ▸ hc,
      fun h => ⟨b, h⟩⟩
  exact hm.symm.trans ((hT.models_elementarily_equivalent M N).realize_sentence σ |>.trans hn)

/-- Omission separates two countable models; atomic uniqueness proves the converse. -/
theorem categorical_iff_isolated [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N) :
    (Cardinal.aleph0 : Cardinal.{0}).Categorical T ↔
      ∀ n (p : T.CompleteType (Fin n)), Isolated T p := by
  classical
  constructor
  · intro hc n p
    apply (OmittingTypes.isolated_iff_countable_realized hT hT.1 p).mpr
    intro N hN hne hcount hmodel
    let := hN
    let := hne
    let := hcount
    let := hmodel
    obtain ⟨M, hMcount, a, ha⟩ := countable_realization p
    let := hMcount
    let : Infinite M := models_infinite hT hInf
    let : Infinite N := models_infinite hT hInf
    obtain ⟨e⟩ := hc M (Theory.ModelType.of T N)
      (Cardinal.mk_eq_aleph0 M) (Cardinal.mk_eq_aleph0 N)
    exact ⟨e ∘ a, fun φ hφ => (e.toElementaryEmbedding.map_formula φ a).mpr (ha φ hφ)⟩
  · intro hi M N hM hN
    let : Countable M := Cardinal.mk_le_aleph0_iff.mp hM.le
    let : Countable N := Cardinal.mk_le_aleph0_iff.mp hN.le
    exact AtomicAndPrimeModels.countable_atomic_unique hT
      (fun n a => hi n (T.typeOf a)) (fun n a => hi n (T.typeOf a))

/-- Countable categoricity is equivalent to finitely many complete types in each finite context. -/
theorem categorical_iff_finite_types [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N) :
    (Cardinal.aleph0 : Cardinal.{0}).Categorical T ↔
      ∀ n, Finite (T.CompleteType (Fin n)) := by
  rw [categorical_iff_isolated hT hInf]
  exact forall_congr' fun n => IsolatedTypes.finite_iff_all_isolated.symm

/-- The finite formula-class formulation uses the same native semantic quotient. -/
theorem categorical_iff_finite_formulaClasses [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N) :
    (Cardinal.aleph0 : Cardinal.{0}).Categorical T ↔
      ∀ n, Finite (FormulaClass T (Fin n)) := by
  rw [categorical_iff_finite_types hT hInf]
  exact forall_congr' fun n => finite_types_iff_formulaClasses

variable {M : Type} [L.Structure M] [Nonempty M] [Countable M] [M ⊨ T]

/-- The automorphism sends each specified source coordinate to its specified target coordinate. -/
theorem type_eq_iff_sameOrbit [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T)
    {n : ℕ} (a b : Fin n → M) :
    T.typeOf a = T.typeOf b ↔ SameOrbit (L := L) a b := by
  constructor
  · intro hab
    have hi := (categorical_iff_isolated hT hInf).mp hcat
    exact AtomicAndPrimeModels.countable_atomic_tuple_isomorphism hT
      (fun n a => hi n (T.typeOf a)) (fun n a => hi n (T.typeOf a)) a b hab
  · exact sameOrbit_typeOf a b

/-- The map defined on actual orbit representatives is a bijection onto all complete types. -/
theorem orbitType_bijective [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T) (n : ℕ) :
    Function.Bijective (orbitType (T := T) (M := M) n) := by
  constructor
  · intro c d
    induction c using Quotient.inductionOn with | h a =>
      induction d using Quotient.inductionOn with | h b =>
        intro h
        exact Quotient.sound ((type_eq_iff_sameOrbit hT hInf hcat a b).mp h)
  · intro p
    obtain ⟨a, ha⟩ := isolated_realized (M := M) hT p
      ((categorical_iff_isolated hT hInf).mp hcat n p)
    exact ⟨Quotient.mk _ a, ((realizes_complete_iff p a).mp ha).symm⟩

/-- An isolating formula defines exactly the orbit of the given tuple, without parameters. -/
theorem orbit_isolator [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T)
    {n : ℕ} (a : Fin n → M) :
    ∃ θ : L.Formula (Fin n), Isolates T (T.typeOf a) θ ∧
      ∀ b, SameOrbit (L := L) a b ↔ θ.Realize b := by
  obtain ⟨θ, hθ⟩ := (categorical_iff_isolated hT hInf).mp hcat n (T.typeOf a)
  refine ⟨θ, hθ, fun b => ?_⟩
  exact (type_eq_iff_sameOrbit hT hInf hcat a b).symm.trans
    ((realizes_complete_iff (T.typeOf a) b).symm.trans (isolator_realizes _ θ hθ b).symm)

/-- Every countable model of a countably categorical theory has finitely many tuple orbits. -/
theorem categorical_oligomorphic [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T) : Oligomorphic L M := by
  intro n
  let := (categorical_iff_finite_types hT hInf).mp hcat n
  exact Finite.of_injective _ (orbitType_bijective (M := M) hT hInf hcat n).1

/-- One countable model with finitely many actual tuple orbits characterizes categoricity. -/
theorem categorical_iff_oligomorphic [Countable L.Symbols] (hT : T.IsComplete)
    (hInf : ∃ N : Theory.ModelType.{0, 0, 0} T, Infinite N) :
    (Cardinal.aleph0 : Cardinal.{0}).Categorical T ↔
      ∃ N : Theory.ModelType.{0, 0, 0} T, Countable N ∧ Oligomorphic L N := by
  constructor
  · intro hc
    obtain ⟨N, hcount, _⟩ := countable_infinite_model hT hInf
    let := hcount
    exact ⟨N, hcount, categorical_oligomorphic (M := N) hT hInf hc⟩
  · rintro ⟨N, hcount, ho⟩
    apply (categorical_iff_finite_types hT hInf).mpr
    intro n
    let := ho n
    exact (finite_realized_types_exhaust (M := N) hT (finite_realized_types_of_orbits (M := N))).1

end Lemmatheca.ModelTheory.CountableCategoricity
