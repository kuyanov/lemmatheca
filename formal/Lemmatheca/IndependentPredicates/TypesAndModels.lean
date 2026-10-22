import Lemmatheca.IndependentPredicates.QuantifierElimination
import Lemmatheca.CountableSaturatedModels.Constructions
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.SetTheory.Cardinal.Continuum

/-! Complete one-types, finite predicate support, and the missing countable models. -/
namespace Lemmatheca.ModelTheory.IndependentPredicates

open FirstOrder FirstOrder.Language
open Types IsolatedTypes AtomicAndPrimeModels

private def termVariable {α : Type*} : Lang.Term α → α
  | .var i => i
  | .func f _ => f.elim

private theorem termVariable_realize {α : Type*} {M : Type*} [Lang.Structure M]
    (t : Lang.Term α) (a : α → M) : t.realize a = a (termVariable t) := by
  cases t with
  | var _ => rfl
  | func f _ => exact f.elim

private theorem qf_agreement {α : Type*} {k : ℕ} {M N : Type*}
    [Lang.Structure M] [Lang.Structure N] (φ : Lang.BoundedFormula α k) (hφ : φ.IsQF)
    (a : α → M) (b : α → N) (v : Fin k → M) (w : Fin k → N)
    (he : ∀ i j, Sum.elim a v i = Sum.elim a v j ↔ Sum.elim b w i = Sum.elim b w j)
    (hp : ∀ n ∈ predicateSupport φ, ∀ i,
      predicate n (Sum.elim a v i) ↔ predicate n (Sum.elim b w i)) :
    φ.Realize a v ↔ φ.Realize b w := by
  induction hφ with
  | falsum => rfl
  | @of_isAtomic φ ha =>
    cases ha with
    | equal t s =>
      change t.realize (Sum.elim a v) = s.realize (Sum.elim a v) ↔
        t.realize (Sum.elim b w) = s.realize (Sum.elim b w)
      simp only [termVariable_realize]
      exact he _ _
    | rel r ts =>
      cases r with
      | pred n =>
        have htsM : (fun i => (ts i).realize (Sum.elim a v)) =
            fun _ : Fin 1 => (ts 0).realize (Sum.elim a v) := by
          funext i
          exact congrArg (fun i => (ts i).realize (Sum.elim a v)) (Subsingleton.elim i 0)
        have htsN : (fun i => (ts i).realize (Sum.elim b w)) =
            fun _ : Fin 1 => (ts 0).realize (Sum.elim b w) := by
          funext i
          exact congrArg (fun i => (ts i).realize (Sum.elim b w)) (Subsingleton.elim i 0)
        change Structure.RelMap (L := Lang) (.pred n) _ ↔ Structure.RelMap (L := Lang) (.pred n) _
        rw [htsM, htsN]
        change predicate n ((ts 0).realize (Sum.elim a v)) ↔
          predicate n ((ts 0).realize (Sum.elim b w))
        simp only [termVariable_realize]
        exact hp n (by change n ∈ ({n} : Finset ℕ); exact Finset.mem_singleton_self n) _
  | @imp φ ψ hφ hψ ihφ ihψ =>
    exact imp_congr
      (ihφ fun n hn => hp n (Finset.mem_union_left _ hn))
      (ihψ fun n hn => hp n (Finset.mem_union_right _ hn))

theorem one_variable_type_eq {M N : Type} [Lang.Structure M] [Lang.Structure N]
    [Nonempty M] [Nonempty N] [M ⊨ independentTheory] [N ⊨ independentTheory]
    (a : M) (b : N) (h : ∀ n, predicate n a ↔ predicate n b) :
    independentTheory.typeOf (fun _ : Fin 1 => a) =
      independentTheory.typeOf (fun _ : Fin 1 => b) := by
  apply (realizes_complete_iff _ _).mp
  intro φ hφ
  have hMa : φ.Realize (fun _ : Fin 1 => a) :=
    Theory.CompleteType.formula_mem_typeOf.mp hφ
  obtain ⟨ψ, hψ, heψ⟩ := hasQuantifierElimination 1 (QuantifierElimination.Shared.pack φ)
  have hMψ := (heψ.realize_bd_iff (M := M)).mp
    ((QuantifierElimination.Shared.pack_realize φ (fun _ => a)).mpr hMa)
  have hψ' : ψ.Realize Empty.elim (fun _ => a) ↔ ψ.Realize Empty.elim (fun _ => b) := by
    apply qf_agreement ψ hψ
    · intro i j
      cases i with
      | inl i => exact i.elim
      | inr i =>
        cases j with
        | inl j => exact j.elim
        | inr j => exact iff_of_true rfl rfl
    · intro n _ i
      cases i with
      | inl i => exact i.elim
      | inr i => exact h n
  exact (QuantifierElimination.Shared.pack_realize φ (fun _ => b)).mp
    ((heψ.realize_bd_iff (M := N)).mpr (hψ'.mp hMψ))

noncomputable def typeOfSubset (A : Set ℕ) : independentTheory.CompleteType (Fin 1) := by
  let : Set ℕ ⊨ independentTheory := subset_model
  exact independentTheory.typeOf (fun _ => A)

def coordinateFormula (n : ℕ) : Lang.Formula (Fin 1) :=
  predicateFormula n (.var (.inl 0))

def typeProfile (p : independentTheory.CompleteType (Fin 1)) : Set ℕ :=
  {n | coordinateFormula n ∈ formulas p}

theorem typeOfSubset_membership (A : Set ℕ) (n : ℕ) :
    coordinateFormula n ∈ formulas (typeOfSubset A) ↔ n ∈ A := by
  let : Set ℕ ⊨ independentTheory := subset_model
  change Formula.equivSentence (coordinateFormula n) ∈
    independentTheory.typeOf (fun _ : Fin 1 => A) ↔ _
  rw [Theory.CompleteType.formula_mem_typeOf]
  rfl

theorem typeOfSubset_bijective : Function.Bijective typeOfSubset := by
  constructor
  · intro A B hAB
    ext n
    rw [← typeOfSubset_membership A n, ← typeOfSubset_membership B n, hAB]
  · intro p
    obtain ⟨N, a, ha⟩ := independentTheory.exists_modelType_is_realized_in p
    let A : Set ℕ := {n | predicate n (a 0)}
    let : Set ℕ ⊨ independentTheory := subset_model
    have ht := one_variable_type_eq A (a 0) (fun _ => Iff.rfl)
    have he : (fun _ : Fin 1 => a 0) = a := by
      funext i
      exact congrArg a (Subsingleton.elim 0 i)
    refine ⟨A, ?_⟩
    change independentTheory.typeOf (fun _ : Fin 1 => A) = p
    exact ht.trans ((congrArg independentTheory.typeOf he).trans ha)

noncomputable def subsetTypeEquiv : Set ℕ ≃ independentTheory.CompleteType (Fin 1) :=
  Equiv.ofBijective typeOfSubset typeOfSubset_bijective

theorem profile_inverse (p : independentTheory.CompleteType (Fin 1)) :
    typeOfSubset (typeProfile p) = p := by
  obtain ⟨A, rfl⟩ := typeOfSubset_bijective.2 p
  congr 1

theorem type_cardinality : Cardinal.mk (independentTheory.CompleteType (Fin 1)) =
    Cardinal.continuum := by
  rw [← Cardinal.mk_congr subsetTypeEquiv]
  exact Cardinal.mk_set_nat

theorem finite_support_agreement (φ : Lang.Formula (Fin 1)) (hφ : φ.IsQF)
    (A B : Set ℕ) (h : ∀ n ∈ predicateSupport φ, n ∈ A ↔ n ∈ B) :
    φ.Realize (fun _ => A) ↔ φ.Realize (fun _ => B) := by
  apply qf_agreement φ hφ (fun _ => A) (fun _ => B) Fin.elim0 Fin.elim0
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact iff_of_true rfl rfl
      | inr j => exact j.elim0
    | inr i => exact i.elim0
  · intro n hn i
    cases i with
    | inl i => exact h n hn
    | inr i => exact i.elim0

theorem all_one_types_nonisolated (p : independentTheory.CompleteType (Fin 1)) :
    ¬ Isolated independentTheory p := by
  classical
  obtain ⟨A, rfl⟩ := typeOfSubset_bijective.2 p
  rintro ⟨θ, hθ⟩
  let : Set ℕ ⊨ independentTheory := subset_model
  have hθA : θ.Realize (fun _ : Fin 1 => A) :=
    Theory.CompleteType.formula_mem_typeOf.mp hθ.1
  obtain ⟨ψ, hψ, heψ⟩ := hasQuantifierElimination 1 (QuantifierElimination.Shared.pack θ)
  obtain ⟨m, hm⟩ := (predicateSupport ψ).exists_notMem
  let B : Set ℕ := {n | if n = m then n ∉ A else n ∈ A}
  have hψAB : ψ.Realize Empty.elim (fun _ => A) ↔
      ψ.Realize Empty.elim (fun _ => B) := by
    apply qf_agreement ψ hψ
    · intro i j
      cases i with
      | inl i => exact i.elim
      | inr i =>
        cases j with
        | inl j => exact j.elim
        | inr j => exact iff_of_true rfl rfl
    · intro n hn i
      have hnm : n ≠ m := fun h => hm (h ▸ hn)
      cases i with
      | inl i => exact i.elim
      | inr i =>
        change n ∈ A ↔ n ∈ B
        simp [B, hnm]
  have hψA : ψ.Realize Empty.elim (fun _ => A) :=
    (heψ.realize_bd_iff (M := Set ℕ)).mp
      ((QuantifierElimination.Shared.pack_realize θ (fun _ => A)).mpr hθA)
  have hθB : θ.Realize (fun _ : Fin 1 => B) :=
    (QuantifierElimination.Shared.pack_realize θ (fun _ => B)).mp
      ((heψ.realize_bd_iff (M := Set ℕ)).mpr (hψAB.mp hψA))
  have hB : θ ∈ formulas (typeOfSubset B) :=
    Theory.CompleteType.formula_mem_typeOf.mpr hθB
  have hBA := typeOfSubset_bijective.1 (((isolates_iff_unique _ _).mp hθ).2 _ hB)
  have hmAB : m ∈ B ↔ m ∈ A := by rw [hBA]
  by_cases hma : m ∈ A <;> simp [B, hma] at hmAB

private theorem finiteSubset_type (F : Finset ℕ) :
    let : Finset ℕ ⊨ independentTheory := finiteSubset_model
    independentTheory.typeOf (fun _ : Fin 1 => F) = typeOfSubset (F : Set ℕ) := by
  let : Finset ℕ ⊨ independentTheory := finiteSubset_model
  let : Set ℕ ⊨ independentTheory := subset_model
  exact one_variable_type_eq F (F : Set ℕ) (fun _ => Iff.rfl)

theorem finiteSubset_realized_iff (A : Set ℕ) :
    (∃ b : Fin 1 → Finset ℕ, Realizes (formulas (typeOfSubset A)) b) ↔ A.Finite := by
  classical
  let : Finset ℕ ⊨ independentTheory := finiteSubset_model
  constructor
  · rintro ⟨b, hb⟩
    have ht := (realizes_complete_iff _ _).mp hb
    have he : b = fun _ : Fin 1 => b 0 := by
      funext i
      exact congrArg b (Subsingleton.elim i 0)
    rw [he] at ht
    have hA : A = (b 0 : Set ℕ) :=
      typeOfSubset_bijective.1 (ht.trans (finiteSubset_type (b 0)))
    rw [hA]
    exact (b 0).finite_toSet
  · intro hA
    refine ⟨fun _ => hA.toFinset, (realizes_complete_iff _ _).mpr ?_⟩
    rw [finiteSubset_type, hA.coe_toFinset]

def allPositive : Set (Lang.Formula (Fin 1)) := Set.range coordinateFormula

theorem allPositive_finitely_realized : FinitelyRealized (Finset ℕ) allPositive := by
  classical
  intro s hs
  let F := s.biUnion predicateSupport
  refine ⟨fun _ => F, ?_⟩
  intro φ hφ
  obtain ⟨n, rfl⟩ := hs hφ
  change n ∈ F
  exact Finset.mem_biUnion.mpr ⟨coordinateFormula n, hφ, by
    simp [coordinateFormula, predicateFormula, predicateSupport]⟩

theorem allPositive_omitted : Omits (Finset ℕ) allPositive := by
  rintro ⟨b, hb⟩
  obtain ⟨n, hn⟩ := (b 0).exists_notMem
  have h := hb (coordinateFormula n) (Set.mem_range_self n)
  exact hn h

theorem allPositive_unique_completion (p : independentTheory.CompleteType (Fin 1))
    (h : allPositive ⊆ formulas p) : p = typeOfSubset Set.univ := by
  have hp : typeProfile p = Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    exact h (Set.mem_range_self n)
  rw [← profile_inverse p, hp]

theorem no_atomic_model (M : Type) [Lang.Structure M] [Nonempty M]
    [M ⊨ independentTheory] : ¬ IsAtomic independentTheory M := by
  intro h
  let a : M := Classical.choice (inferInstance : Nonempty M)
  exact all_one_types_nonisolated _ (h 1 (fun _ => a))

theorem no_prime_model (M : Type) [Lang.Structure M] [Nonempty M]
    [M ⊨ independentTheory] : ¬ IsPrime independentTheory M := by
  intro h
  exact no_atomic_model M (prime_atomic independentTheory_complete h)

theorem not_small : ¬ CountableSaturatedModels.Small independentTheory := by
  intro h
  let := h 1
  have hc : Cardinal.mk (independentTheory.CompleteType (Fin 1)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr inferInstance
  rw [type_cardinality] at hc
  exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hc

theorem no_countable_saturated (M : Type) [Lang.Structure M] [Nonempty M]
    [M ⊨ independentTheory] [Countable M] : ¬ Saturation.OmegaSaturated Lang M := by
  intro h
  exact not_small (CountableSaturatedModels.small_of_saturated independentTheory_complete h)

theorem no_countable_universal (M : Type) [Lang.Structure M] [Nonempty M]
    [M ⊨ independentTheory] : ¬ CountableSaturatedModels.CountableUniversal independentTheory M := by
  intro h
  exact not_small (CountableSaturatedModels.small_of_universal h)

end Lemmatheca.ModelTheory.IndependentPredicates
