import Lemmatheca.AtomicAndPrimeModels.AtomicModels

/-! Consistent isolating refinements and a specified finite-stage atomic-model construction. -/
namespace Lemmatheca.ModelTheory.AtomicAndPrimeModels

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.IsolatedTypes
open Lemmatheca.MathematicalLogic.HenkinCompleteness

variable {L : Language.{0, 0}} {T : L.Theory}

noncomputable section
local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

/-- A formula is consistent with T when it is realized in a nonempty T-model. -/
def ConsistentFormula (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) : Prop :=
  ∃ M : T.ModelType.{0, 0, 0}, ∃ a : Fin n → M, φ.Realize a

/-- A consistent isolator that entails the original formula. -/
def IsolatingRefinement (T : L.Theory) {n : ℕ}
    (φ ψ : L.Formula (Fin n)) : Prop :=
  (∃ p : T.CompleteType (Fin n), Isolates T p ψ) ∧ T ⊨ᵇ ψ.imp φ

/-- Every consistent finite-tuple formula has an isolating refinement. -/
def HasIsolatingRefinements (T : L.Theory) : Prop :=
  ∀ n (φ : L.Formula (Fin n)), ConsistentFormula T φ →
    ∃ ψ, IsolatingRefinement T φ ψ

theorem refinement_consistent {n : ℕ} {φ ψ : L.Formula (Fin n)}
    (h : IsolatingRefinement T φ ψ) : ConsistentFormula T ψ := by
  obtain ⟨p, hp⟩ := h.1
  obtain ⟨M, a, ha⟩ := T.exists_modelType_is_realized_in p
  exact ⟨M, a, Theory.CompleteType.formula_mem_typeOf.mp (ha.symm ▸ hp.1)⟩

theorem refinements_iff_dense_types :
    HasIsolatingRefinements T ↔
      ∀ n (φ : L.Formula (Fin n)), ConsistentFormula T φ →
        ∃ p : T.CompleteType (Fin n), Isolated T p ∧ φ ∈ formulas p := by
  constructor
  · intro h n φ hφ
    obtain ⟨ψ, ⟨p, hp⟩, hψφ⟩ := h n φ hφ
    obtain ⟨M, a, ha⟩ := T.exists_modelType_is_realized_in p
    have hψa : ψ.Realize a := Theory.CompleteType.formula_mem_typeOf.mp (ha.symm ▸ hp.1)
    exact ⟨p, ⟨ψ, hp⟩, ha ▸ Theory.CompleteType.formula_mem_typeOf.mpr
      (hψφ.realize_formula M hψa)⟩
  · intro h n φ hφ
    obtain ⟨p, ⟨ψ, hψ⟩, hpφ⟩ := h n φ hφ
    exact ⟨ψ, ⟨⟨p, hψ⟩, hψ.2 φ hpφ⟩⟩

/-- The condition and specified tuple of names remain jointly satisfiable after refinement. -/
theorem finite_refinement_extension (h : HasIsolatingRefinements T)
    (Γ : Finset (L.Formula ℕ)) (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ)))
    {n : ℕ} (t : Fin n → ℕ) :
    ∃ (p : T.CompleteType (Fin n)) (ψ : L.Formula (Fin n)),
      Isolates T p ψ ∧
        IsPartial T (↑(insert (Formula.relabel t ψ) Γ) : Set (L.Formula ℕ)) := by
  obtain ⟨M, a, ha⟩ := (partial_iff_model T _).mp hΓ
  have hχ : ConsistentFormula T (OmittingTypes.finiteConditionFormula Γ t) :=
    ⟨M, a ∘ t, (OmittingTypes.finiteConditionFormula_realize Γ t (a ∘ t)).mpr
      ⟨a, ha, rfl⟩⟩
  obtain ⟨ψ, hψ⟩ := h _ _ hχ
  obtain ⟨N, b, hb⟩ := refinement_consistent hψ
  have hχb := hψ.2.realize_formula N hb
  obtain ⟨c, hc, hct⟩ := (OmittingTypes.finiteConditionFormula_realize Γ t b).mp hχb
  obtain ⟨p, hp⟩ := hψ.1
  refine ⟨p, ψ, hp, (partial_iff_model T _).mpr ⟨N, c, ?_⟩⟩
  intro φ hφ
  rcases Finset.mem_insert.mp hφ with rfl | hφ
  · rw [Formula.realize_relabel, hct]
    exact hb
  · exact hc φ hφ

/-- Decisions, Henkin witnesses, and isolation of every finite tuple of names. -/
abbrev AtomicTask (L : Language.{0, 0}) :=
  L.Formula ℕ ⊕ (L.BoundedFormula ℕ 1 ⊕ (Σ n : ℕ, Fin n → ℕ))

/-- One added formula fulfils the indicated request with the displayed names unchanged. -/
def MeetsAtomic (T : L.Theory) : AtomicTask L → L.Formula ℕ → Prop
  | .inl σ, A => A = σ ∨ A = σ.not
  | .inr (.inl η), A => ∃ c, A = witnessAxiom η c
  | .inr (.inr ⟨_, t⟩), A =>
      ∃ p ψ, Isolates T p ψ ∧ A = Formula.relabel t ψ

/-- The chosen finite conditions and their exact one-request successor equations. -/
structure AtomicConstruction (T : L.Theory) (R : ℕ → AtomicTask L) where
  conditions : ℕ → Finset (L.Formula ℕ)
  zero : conditions 0 = ∅
  consistent : ∀ s, IsPartial T (↑(conditions s) : Set (L.Formula ℕ))
  step : ∀ s, ∃ A, conditions (s + 1) = insert A (conditions s) ∧ MeetsAtomic T (R s) A

theorem countable_atomic_tasks [Countable L.Symbols] : Countable (AtomicTask L) := by
  exact OmittingTypes.countable_tasks (L := L) (I := ℕ) (n := id)

theorem atomic_task_enumeration [Countable L.Symbols] :
    ∃ R : ℕ → AtomicTask L, Function.Surjective R := by
  let := countable_atomic_tasks (L := L)
  let : Nonempty (AtomicTask L) := ⟨.inl ⊥⟩
  exact exists_surjective_nat _

theorem exists_atomicConstruction (hT : T.IsSatisfiable)
    (h : HasIsolatingRefinements T) (R : ℕ → AtomicTask L) :
    Nonempty (AtomicConstruction T R) := by
  classical
  have next (Γ : Finset (L.Formula ℕ)) (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ)))
      (r : AtomicTask L) : ∃ A, IsPartial T (↑(insert A Γ) : Set (L.Formula ℕ)) ∧
        MeetsAtomic T r A := by
    rcases r with σ | η | ⟨n, t⟩
    · rcases OmittingTypes.decision_preserves Γ hΓ σ with hσ | hnσ
      · exact ⟨σ, hσ, Or.inl rfl⟩
      · exact ⟨σ.not, hnσ, Or.inr rfl⟩
    · obtain ⟨c, _, hc⟩ := OmittingTypes.witness_preserves Γ hΓ η
      exact ⟨witnessAxiom η c, hc, c, rfl⟩
    · obtain ⟨p, ψ, hp, hcon⟩ := finite_refinement_extension h Γ hΓ t
      exact ⟨Formula.relabel t ψ, hcon, p, ψ, hp, rfl⟩
  have hzero : IsPartial T (∅ : Set (L.Formula ℕ)) := by
    let M := hT.some
    exact (partial_iff_model _ _).mpr
      ⟨M, fun _ => Classical.choice (inferInstance : Nonempty M), fun _ hφ => hφ.elim⟩
  let State := {Γ : Finset (L.Formula ℕ) // IsPartial T (↑Γ : Set (L.Formula ℕ))}
  let step (s : ℕ) (Γ : State) : State :=
    ⟨insert (Classical.choose (next Γ.val Γ.property (R s))) Γ.val,
      (Classical.choose_spec (next Γ.val Γ.property (R s))).1⟩
  let states : ℕ → State := Nat.rec ⟨∅, by simpa only [Finset.coe_empty] using hzero⟩ step
  refine ⟨⟨fun s => (states s).val, rfl, fun s => (states s).property, fun s => ?_⟩⟩
  exact ⟨Classical.choose (next (states s).val (states s).property (R s)), rfl,
    (Classical.choose_spec (next (states s).val (states s).property (R s))).2⟩

/-- The precise union of the selected finite conditions. -/
def atomicLimit {R : ℕ → AtomicTask L} (D : AtomicConstruction T R) :
    Set (L.Formula ℕ) := ⋃ s, (↑(D.conditions s) : Set (L.Formula ℕ))

/-- Every tuple, including repetitions and the empty tuple, has an isolator in U. -/
def IsolatesNamed (T : L.Theory) (U : Set (L.Formula ℕ)) : Prop :=
  ∀ n (t : Fin n → ℕ), ∃ p ψ, Isolates T p ψ ∧ Formula.relabel t ψ ∈ U

private theorem atomicConditions_mono {R : ℕ → AtomicTask L}
    (D : AtomicConstruction T R) : Monotone D.conditions := by
  apply monotone_nat_of_le_succ
  intro s
  obtain ⟨A, hA, _⟩ := D.step s
  rw [hA]
  exact Finset.subset_insert _ _

theorem atomicLimit_isPartial {R : ℕ → AtomicTask L} (D : AtomicConstruction T R) :
    IsPartial T (atomicLimit D) := by
  classical
  apply (partial_iff_finite _ _).mpr
  intro Γ hΓ
  choose stage hstage using fun φ : Γ => Set.mem_iUnion.mp (hΓ φ.property)
  let s := Finset.univ.sup stage
  have hsub : (↑Γ : Set (L.Formula ℕ)) ⊆ (↑(D.conditions s) : Set (L.Formula ℕ)) := by
    intro φ hφ
    exact atomicConditions_mono D (Finset.le_sup (Finset.mem_univ (⟨φ, hφ⟩ : Γ)))
      (hstage ⟨φ, hφ⟩)
  obtain ⟨M, a, ha⟩ := (partial_iff_model _ _).mp (D.consistent s)
  exact (partial_iff_model _ _).mpr ⟨M, a, fun φ hφ => ha φ (hsub hφ)⟩

theorem atomicLimit_properties {R : ℕ → AtomicTask L} (hR : Function.Surjective R)
    (D : AtomicConstruction T R) :
    Complete (atomicLimit D) ∧ Henkin (atomicLimit D) ∧ IsolatesNamed T (atomicLimit D) := by
  have task (r : AtomicTask L) : ∃ A ∈ atomicLimit D, MeetsAtomic T r A := by
    obtain ⟨s, hs⟩ := hR r
    obtain ⟨A, hA, hmeet⟩ := D.step s
    refine ⟨A, Set.mem_iUnion.mpr ⟨s + 1, ?_⟩, hs ▸ hmeet⟩
    rw [hA]
    exact Finset.mem_insert_self _ _
  refine ⟨fun σ => ?_, fun η => ?_, fun n t => ?_⟩
  · obtain ⟨A, hA, hmeet⟩ := task (.inl σ)
    rcases hmeet with rfl | rfl
    · exact Or.inl hA
    · exact Or.inr hA
  · obtain ⟨A, hA, c, rfl⟩ := task (.inr (.inl η))
    exact ⟨c, hA⟩
  · obtain ⟨A, hA, p, ψ, hp, rfl⟩ := task (.inr (.inr ⟨n, t⟩))
    exact ⟨p, ψ, hp, hA⟩

/-- The actual elementary range of the chosen names is atomic. -/
theorem named_atomic {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (U : Set (L.Formula ℕ)) (hU : Henkin U) (hIso : IsolatesNamed T U)
    (a : ℕ → M) (ha : Realizes U a) :
    let S := OmittingTypes.namedSubstructure U hU a ha
    let : Nonempty S := OmittingTypes.named_nonempty U hU a ha
    let : S ⊨ T := OmittingTypes.named_models U hU a ha
    IsAtomic T S := by
  dsimp only
  let S := OmittingTypes.namedSubstructure U hU a ha
  let : Nonempty S := OmittingTypes.named_nonempty U hU a ha
  let : S ⊨ T := OmittingTypes.named_models U hU a ha
  obtain ⟨e, he⟩ := OmittingTypes.named_elementary U hU a ha
  intro n x
  choose t ht using fun j => (x j).property
  obtain ⟨p, ψ, hp, hψ⟩ := hIso n t
  have hcomp : a ∘ t = e ∘ x := by
    funext i
    exact (ht i).trans (he (x i)).symm
  have hψM := ha _ hψ
  rw [Formula.realize_relabel, hcomp] at hψM
  have hψS := (e.map_formula ψ x).mp hψM
  have hpx := (realizes_complete_iff p x).mp ((isolator_realizes p ψ hp x).mp hψS)
  exact ⟨ψ, hpx ▸ hp⟩

theorem exists_countable_atomic [Countable L.Symbols] (hT : T.IsComplete)
    (h : HasIsolatingRefinements T) :
    ∃ M : T.ModelType.{0, 0, 0}, Countable M ∧ IsAtomic T M := by
  obtain ⟨R, hR⟩ := atomic_task_enumeration (L := L)
  obtain ⟨D⟩ := exists_atomicConstruction hT.1 h R
  obtain ⟨M, a, ha⟩ := (partial_iff_model T (atomicLimit D)).mp (atomicLimit_isPartial D)
  obtain ⟨_, hU, hIso⟩ := atomicLimit_properties hR D
  let S := OmittingTypes.namedSubstructure (atomicLimit D) hU a ha
  let : Nonempty S := OmittingTypes.named_nonempty _ _ _ _
  let : S ⊨ T := OmittingTypes.named_models _ _ _ _
  exact ⟨Theory.ModelType.of T S, OmittingTypes.named_countable _ _ _ _,
    named_atomic _ hU hIso a ha⟩

theorem atomic_implies_refinements {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (hT : T.IsComplete) (hM : IsAtomic T M) : HasIsolatingRefinements T := by
  intro n φ hφ
  obtain ⟨N, b, hb⟩ := hφ
  have hexN : N ⊨ existentialSentence φ := (existentialSentence_realize φ).mpr ⟨b, hb⟩
  have hex : T ⊨ᵇ existentialSentence φ := (hT.realize_sentence_iff _ N).mp hexN
  obtain ⟨a, ha⟩ := (existentialSentence_realize φ).mp (hex.realize_sentence M)
  obtain ⟨ψ, hψ⟩ := hM n a
  exact ⟨ψ, ⟨⟨T.typeOf a, hψ⟩,
    hψ.2 φ (Theory.CompleteType.formula_mem_typeOf.mpr ha)⟩⟩

theorem existence_criterion [Countable L.Symbols] (hT : T.IsComplete) :
    HasIsolatingRefinements T ↔
      ∃ M : T.ModelType.{0, 0, 0}, Countable M ∧ IsAtomic T M := by
  constructor
  · exact exists_countable_atomic hT
  · rintro ⟨M, _, hM⟩
    exact atomic_implies_refinements hT hM

theorem exists_prime_iff [Countable L.Symbols] (hT : T.IsComplete) :
    (∃ M : T.ModelType.{0, 0, 0}, IsPrime T M) ↔ HasIsolatingRefinements T := by
  constructor
  · rintro ⟨M, hM⟩
    exact atomic_implies_refinements hT (prime_atomic hT hM)
  · intro h
    obtain ⟨M, hc, ha⟩ := exists_countable_atomic hT h
    let := hc
    exact ⟨M, countable_atomic_prime hT ha⟩

end
end Lemmatheca.ModelTheory.AtomicAndPrimeModels
