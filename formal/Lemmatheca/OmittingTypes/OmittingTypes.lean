import Lemmatheca.OmittingTypes.FiniteConditions

/-! A countable finite-stage construction and its specified named elementary model. -/
namespace Lemmatheca.ModelTheory.OmittingTypes

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.IsolatedTypes
open Lemmatheca.MathematicalLogic.HenkinCompleteness

universe u v w z
variable {L : Language.{u, v}} {T : L.Theory} {I : Type z} {n : I → ℕ}

noncomputable section
local instance : DecidableEq (L.Formula ℕ) := Classical.decEq _

/-- Decisions, conditional witnesses, and tuples for a possibly varying-arity type family. -/
abbrev Task (L : Language.{u, v}) (I : Type z) (n : I → ℕ) :=
  L.Formula ℕ ⊕ (L.BoundedFormula ℕ 1 ⊕ (Σ i : I, Fin (n i) → ℕ))

/-- A task is answered by a condition from the original formula collection. -/
def MeetsConditions (p : (i : I) → Set (L.Formula (Fin (n i)))) :
    Task L I n → L.Formula ℕ → Prop
  | .inl σ, A => A = σ ∨ A = σ.not
  | .inr (.inl η), A => ∃ c, A = witnessAxiom η c
  | .inr (.inr ⟨i, t⟩), A => ∃ φ ∈ p i, A = (Formula.relabel t φ).not

/-- The complete-type API retains exactly its original formula-set semantics. -/
abbrev Meets (p : (i : I) → T.CompleteType (Fin (n i))) :=
  MeetsConditions (fun i => formulas (p i))

/-- The generic finite-stage data retains all of T and avoids original partial conditions. -/
structure ConditionsConstruction (p : (i : I) → Set (L.Formula (Fin (n i))))
    (R : ℕ → Task L I n) where
  conditions : ℕ → Finset (L.Formula ℕ)
  zero : conditions 0 = ∅
  consistent : ∀ s, IsPartial T (↑(conditions s) : Set (L.Formula ℕ))
  step : ∀ s, ∃ A, conditions (s + 1) = insert A (conditions s) ∧ MeetsConditions p (R s) A

/-- The original complete-type construction is the same generic finite-stage data. -/
abbrev FiniteStageConstruction (p : (i : I) → T.CompleteType (Fin (n i)))
    (R : ℕ → Task L I n) :=
  ConditionsConstruction (T := T) (fun i => formulas (p i)) R

/-- There are countably many tasks, including repeated names and all finite arities in the family. -/
theorem countable_tasks [Countable L.Symbols] [Countable I] :
    Countable (Task L I n) := by
  let : Countable (L.BoundedFormula ℕ 0) := Function.Injective.countable
    (f := fun φ : L.BoundedFormula ℕ 0 => (⟨0, φ⟩ : Σ k, L.BoundedFormula ℕ k))
    sigma_mk_injective
  let : Countable (L.BoundedFormula ℕ 1) := Function.Injective.countable
    (f := fun φ : L.BoundedFormula ℕ 1 => (⟨1, φ⟩ : Σ k, L.BoundedFormula ℕ k))
    sigma_mk_injective
  infer_instance

/-- A task list can visit every request; the empty type family causes no exceptional case. -/
theorem task_enumeration [Countable L.Symbols] [Countable I] :
    ∃ R : ℕ → Task L I n, Function.Surjective R := by
  let := countable_tasks (L := L) (I := I) (n := n)
  let : Nonempty (Task L I n) := ⟨.inl ⊥⟩
  exact exists_surjective_nat _

/-- Generic requests over a satisfiable background theory admit a finite-stage construction. -/
theorem exists_conditionsConstruction (hT : T.IsSatisfiable)
    (p : (i : I) → Set (L.Formula (Fin (n i)))) (hp : ∀ i, Nonprincipal T (p i))
    (R : ℕ → Task L I n) : Nonempty (ConditionsConstruction (T := T) p R) := by
  classical
  have next (Γ : Finset (L.Formula ℕ)) (hΓ : IsPartial T (↑Γ : Set (L.Formula ℕ)))
      (r : Task L I n) : ∃ A, IsPartial T (↑(insert A Γ) : Set (L.Formula ℕ)) ∧
        MeetsConditions p r A := by
    rcases r with σ | η | ⟨i, t⟩
    · rcases decision_preserves Γ hΓ σ with hσ | hnσ
      · exact ⟨σ, hσ, Or.inl rfl⟩
      · exact ⟨σ.not, hnσ, Or.inr rfl⟩
    · obtain ⟨c, _, hc⟩ := witness_preserves Γ hΓ η
      exact ⟨witnessAxiom η c, hc, c, rfl⟩
    · obtain ⟨φ, hφ, hcon⟩ := partial_finite_avoidance (p i) (hp i) Γ hΓ t
      exact ⟨(Formula.relabel t φ).not, hcon, φ, hφ, rfl⟩
  have hzero : IsPartial T (∅ : Set (L.Formula ℕ)) := by
    let N := hT.some
    exact (partial_iff_model _ _).mpr
      ⟨N, fun _ => Classical.choice (inferInstance : Nonempty N), fun _ h => h.elim⟩
  let State := {Γ : Finset (L.Formula ℕ) // IsPartial T (↑Γ : Set (L.Formula ℕ))}
  let step (s : ℕ) (Γ : State) : State :=
    ⟨insert (Classical.choose (next Γ.val Γ.property (R s))) Γ.val,
      (Classical.choose_spec (next Γ.val Γ.property (R s))).1⟩
  let states : ℕ → State := Nat.rec ⟨∅, by simpa only [Finset.coe_empty] using hzero⟩ step
  refine ⟨⟨fun s => (states s).val, rfl, fun s => (states s).property, fun s => ?_⟩⟩
  exact ⟨Classical.choose (next (states s).val (states s).property (R s)), rfl,
    (Classical.choose_spec (next (states s).val (states s).property (R s))).2⟩


/-- Classical recursion combines the three satisfiability-preserving extensions. -/
theorem exists_finiteStageConstruction (hT : T.IsSatisfiable)
    (p : (i : I) → T.CompleteType (Fin (n i))) (hp : ∀ i, ¬Isolated T (p i))
    (R : ℕ → Task L I n) : Nonempty (FiniteStageConstruction p R) := by
  exact exists_conditionsConstruction hT (fun i => formulas (p i))
    (fun i h => hp i ((principal_complete_iff (p i)).mp h)) R


/-- The set of all original conditions ever inserted by this construction. -/
def conditionsLimit {p : (i : I) → Set (L.Formula (Fin (n i)))}
    {R : ℕ → Task L I n} (D : ConditionsConstruction (T := T) p R) : Set (L.Formula ℕ) :=
  ⋃ s, (↑(D.conditions s) : Set (L.Formula ℕ))

/-- The old complete-type limit is the same union. -/
abbrev limitConditions {p : (i : I) → T.CompleteType (Fin (n i))}
    {R : ℕ → Task L I n} (D : FiniteStageConstruction p R) : Set (L.Formula ℕ) :=
  conditionsLimit D

/-- Every named tuple has a recorded failure from its original partial condition set. -/
def AvoidsConditions (U : Set (L.Formula ℕ))
    (p : (i : I) → Set (L.Formula (Fin (n i)))) : Prop :=
  ∀ i (t : Fin (n i) → ℕ), ∃ φ ∈ p i, (Formula.relabel t φ).not ∈ U

/-- The old named-avoidance condition is its complete-type specialization. -/
abbrev AvoidsNamed (U : Set (L.Formula ℕ))
    (p : (i : I) → T.CompleteType (Fin (n i))) : Prop :=
  AvoidsConditions U (fun i => formulas (p i))

private theorem conditions_mono {p : (i : I) → Set (L.Formula (Fin (n i)))}
    {R : ℕ → Task L I n} (D : ConditionsConstruction (T := T) p R) : Monotone D.conditions := by
  apply monotone_nat_of_le_succ
  intro s
  obtain ⟨A, hA, _⟩ := D.step s
  rw [hA]
  exact Finset.subset_insert _ _


theorem conditionsLimit_isPartial {p : (i : I) → Set (L.Formula (Fin (n i)))}
    {R : ℕ → Task L I n} (D : ConditionsConstruction (T := T) p R) :
    IsPartial T (conditionsLimit D) := by
  classical
  apply (partial_iff_finite _ _).mpr
  intro Γ hΓ
  choose stage hstage using fun φ : Γ => Set.mem_iUnion.mp (hΓ φ.property)
  let s := Finset.univ.sup stage
  have hsub : (↑Γ : Set (L.Formula ℕ)) ⊆ (↑(D.conditions s) : Set (L.Formula ℕ)) := by
    intro φ hφ
    exact conditions_mono D (Finset.le_sup (Finset.mem_univ (⟨φ, hφ⟩ : Γ)))
      (hstage ⟨φ, hφ⟩)
  obtain ⟨N, a, ha⟩ := (partial_iff_model _ _).mp (D.consistent s)
  exact (partial_iff_model _ _).mpr ⟨N, a, fun φ hφ => ha φ (hsub hφ)⟩


theorem conditionsLimit_properties {p : (i : I) → Set (L.Formula (Fin (n i)))}
    {R : ℕ → Task L I n} (hR : Function.Surjective R)
    (D : ConditionsConstruction (T := T) p R) :
    Complete (conditionsLimit D) ∧ Henkin (conditionsLimit D) ∧
      AvoidsConditions (conditionsLimit D) p := by
  have task (r : Task L I n) : ∃ A ∈ conditionsLimit D, MeetsConditions p r A := by
    obtain ⟨s, hs⟩ := hR r
    obtain ⟨A, hA, hmeet⟩ := D.step s
    refine ⟨A, Set.mem_iUnion.mpr ⟨s + 1, ?_⟩, hs ▸ hmeet⟩
    rw [hA]
    exact Finset.mem_insert_self _ _
  refine ⟨fun σ => ?_, fun η => ?_, fun i t => ?_⟩
  · obtain ⟨A, hA, hmeet⟩ := task (.inl σ)
    rcases hmeet with rfl | rfl
    · exact Or.inl hA
    · exact Or.inr hA
  · obtain ⟨A, hA, c, rfl⟩ := task (.inr (.inl η))
    exact ⟨c, hA⟩
  · obtain ⟨A, hA, φ, hφ, rfl⟩ := task (.inr (.inr ⟨i, t⟩))
    exact ⟨φ, hφ, hA⟩

variable {M : Type w} [L.Structure M]



/-- Compactness uses a single finite stage for each finite fragment of the final theory. -/
theorem limit_isPartial {p : (i : I) → T.CompleteType (Fin (n i))}
    {R : ℕ → Task L I n} (D : FiniteStageConstruction p R) :
    IsPartial T (limitConditions D) := by
  exact conditionsLimit_isPartial D

/-- Surjectivity of the task list preserves all three kinds of completed requests. -/
theorem limit_properties {p : (i : I) → T.CompleteType (Fin (n i))}
    {R : ℕ → Task L I n} (hR : Function.Surjective R)
    (D : FiniteStageConstruction p R) :
    Complete (limitConditions D) ∧ Henkin (limitConditions D) ∧
      AvoidsNamed (limitConditions D) p := by
  exact conditionsLimit_properties hR D

/-- Every old function value of named arguments is named, including zero-ary functions. -/
theorem named_range_closed (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (a : ℕ → M) (ha : Realizes U a) :
    ∀ {k : ℕ} (f : L.Functions k) (x : Fin k → M),
      (∀ i, x i ∈ Set.range a) → funMap f x ∈ Set.range a := by
  classical
  intro k f x hx
  choose t ht using hx
  let η : L.BoundedFormula ℕ 1 := .equal (.var (.inr 0))
    (.func f fun i => .var (.inl (t i)))
  obtain ⟨c, hc⟩ := hU η
  have hax := ha _ hc
  rw [witnessAxiom, Formula.realize_imp,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.instantiate_realize] at hax
  have hex : Formula.Realize η.ex a := BoundedFormula.realize_ex.mpr
    ⟨funMap f (a ∘ t), by rfl⟩
  refine ⟨c, ?_⟩
  have heq : a ∘ t = x := funext ht
  rw [← heq]
  exact hax hex

/-- The actual range of the new-name interpretation, with closure supplied by witness requests. -/
def namedSubstructure (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (a : ℕ → M) (ha : Realizes U a) : L.Substructure M where
  carrier := Set.range a
  fun_mem := named_range_closed U hU a ha

/-- The named carrier contains the value of c₀. -/
theorem named_nonempty (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (a : ℕ → M) (ha : Realizes U a) : Nonempty (namedSubstructure U hU a ha) := by
  exact ⟨⟨a 0, ⟨0, rfl⟩⟩⟩

/-- The displayed sequence of new-name values enumerates the named carrier. -/
theorem named_countable (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (a : ℕ → M) (ha : Realizes U a) : Countable (namedSubstructure U hU a ha) := by
  exact Set.countable_range a

/-- Tarski–Vaught applies to the particular inclusion of the range of names. -/
theorem named_elementary (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (a : ℕ → M) (ha : Realizes U a) :
    ∃ e : namedSubstructure U hU a ha ↪ₑ[L] M, ∀ x, e x = x.val := by
  classical
  refine ⟨(namedSubstructure U hU a ha).subtype.toElementaryEmbedding ?_, fun _ => rfl⟩
  intro k φ x d hd
  choose t ht using fun i => (x i).property
  let g : Empty ⊕ Fin (k + 1) → ℕ ⊕ Fin 1 :=
    Sum.elim Empty.elim (Fin.lastCases (.inr 0) (fun i => .inl (t i)))
  let η : L.BoundedFormula ℕ 1 := BoundedFormula.relabel g φ.toFormula
  have truth (b : M) :
      η.Realize a (fun _ => b) ↔ φ.Realize default (Fin.snoc (Subtype.val ∘ x) b) := by
    dsimp only [η]
    rw [BoundedFormula.realize_relabel]
    have hzero : (fun _ : Fin 1 => b) ∘ Fin.natAdd 1 = (default : Fin 0 → M) :=
      Subsingleton.elim _ _
    rw [hzero]
    change φ.toFormula.Realize (Sum.elim a (fun _ => b) ∘ g) ↔ _
    rw [BoundedFormula.realize_toFormula]
    have hfree : (Sum.elim a (fun _ => b) ∘ g) ∘ Sum.inl =
        (default : Empty → M) := Subsingleton.elim _ _
    have htuple : (Sum.elim a (fun _ => b) ∘ g) ∘ Sum.inr =
        Fin.snoc (Subtype.val ∘ x) b := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [g]
      · simpa [g] using ht j
    rw [hfree, htuple]
  obtain ⟨c, hc⟩ := hU η
  have hw := ha _ hc
  rw [witnessAxiom, Formula.realize_imp,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.instantiate_realize] at hw
  have hex : Formula.Realize η.ex a := BoundedFormula.realize_ex.mpr ⟨d, (truth d).mpr hd⟩
  refine ⟨⟨a c, ⟨c, rfl⟩⟩, ?_⟩
  exact (truth (a c)).mp (hw hex)

/-- Agreement on sentences makes the named elementary carrier a model of the background theory. -/
theorem named_models [M ⊨ T] (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (a : ℕ → M) (ha : Realizes U a) : namedSubstructure U hU a ha ⊨ T := by
  obtain ⟨e, _⟩ := named_elementary U hU a ha
  exact (e.theory_model_iff T).mpr (inferInstance : M ⊨ T)

/-- The exact named carrier omits every original partial condition set. -/
theorem named_omits_conditions (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (p : (i : I) → Set (L.Formula (Fin (n i)))) (havoid : AvoidsConditions U p)
    (a : ℕ → M) (ha : Realizes U a) :
    ∀ i, Omits (namedSubstructure U hU a ha) (p i) := by
  classical
  obtain ⟨e, he⟩ := named_elementary U hU a ha
  intro i hreal
  obtain ⟨x, hx⟩ := hreal
  choose t ht using fun j => (x j).property
  obtain ⟨φ, hφ, hnφ⟩ := havoid i t
  have heq : a ∘ t = e ∘ x := by
    funext j
    exact (ht j).trans (he (x j)).symm
  apply Formula.realize_not.mp (ha _ hnφ)
  rw [Formula.realize_relabel, heq]
  exact (e.map_formula φ x).mpr (hx φ hφ)


/-- Every tuple in this specified carrier has the failed formula scheduled for its names. -/
theorem named_omits (U : Set (L.Formula ℕ)) (hU : Henkin U)
    (p : (i : I) → T.CompleteType (Fin (n i))) (havoid : AvoidsNamed U p)
    (a : ℕ → M) (ha : Realizes U a) :
    ∀ i, Omits (namedSubstructure U hU a ha) (formulas (p i)) := by
  exact named_omits_conditions U hU (fun i => formulas (p i)) havoid a ha


/-- Nonprincipality suffices to omit the original formula sets over arbitrary satisfiable T. -/
theorem exists_countable_omitting_conditions [Countable L.Symbols] [Countable I]
    (hsat : T.IsSatisfiable) (p : (i : I) → Set (L.Formula (Fin (n i))))
    (hp : ∀ i, Nonprincipal T (p i)) :
    ∃ N : Type (max u v), ∃ _ : L.Structure N,
      Nonempty N ∧ Countable N ∧ N ⊨ T ∧ ∀ i, Omits N (p i) := by
  obtain ⟨R, hR⟩ := task_enumeration (L := L) (I := I) (n := n)
  obtain ⟨D⟩ := exists_conditionsConstruction hsat p hp R
  obtain ⟨N, a, ha⟩ := (partial_iff_model T (conditionsLimit D)).mp (conditionsLimit_isPartial D)
  obtain ⟨_, hH, havoid⟩ := conditionsLimit_properties hR D
  refine ⟨namedSubstructure (conditionsLimit D) hH a ha, inferInstance,
    named_nonempty _ _ _ _, named_countable _ _ _ _, named_models _ _ _ _, ?_⟩
  exact named_omits_conditions _ hH p havoid a ha


/-- In particular all jointly consistent nonprincipal partial types are omitted together. -/
theorem exists_countable_omitting_partial_types [Countable L.Symbols] [Countable I]
    (hsat : T.IsSatisfiable) (p : (i : I) → Set (L.Formula (Fin (n i))))
    (_hp : ∀ i, IsPartial T (p i)) (hn : ∀ i, Nonprincipal T (p i)) :
    ∃ N : Type (max u v), ∃ _ : L.Structure N,
      Nonempty N ∧ Countable N ∧ N ⊨ T ∧ ∀ i, Omits N (p i) := by
  exact exists_countable_omitting_conditions hsat p hn


/-- Complete-type omission itself needs no completeness assumption on the background theory. -/
theorem exists_countable_omitting_nonisolated [Countable L.Symbols] [Countable I]
    (hsat : T.IsSatisfiable) (p : (i : I) → T.CompleteType (Fin (n i)))
    (hp : ∀ i, ¬Isolated T (p i)) :
    ∃ N : Type (max u v), ∃ _ : L.Structure N,
      Nonempty N ∧ Countable N ∧ N ⊨ T ∧ ∀ i, Omits N (formulas (p i)) := by
  exact exists_countable_omitting_conditions hsat (fun i => formulas (p i))
    (fun i h => hp i ((principal_complete_iff (p i)).mp h))


/-- Simultaneous omission for a countable family with arbitrary varying finite arities. -/
theorem exists_countable_omitting [Countable L.Symbols] [Countable I]
    (_hT : T.IsComplete) (hsat : T.IsSatisfiable)
    (p : (i : I) → T.CompleteType (Fin (n i))) (hp : ∀ i, ¬Isolated T (p i)) :
    ∃ N : Type (max u v), ∃ _ : L.Structure N,
      Nonempty N ∧ Countable N ∧ N ⊨ T ∧ ∀ i, Omits N (formulas (p i)) := by
  exact exists_countable_omitting_nonisolated hsat p hp

/-- Over a countable complete theory, every countable model realizes exactly the unavoidable types. -/
theorem isolated_iff_countable_realized [Countable L.Symbols]
    (hT : T.IsComplete) (hsat : T.IsSatisfiable) {k : ℕ}
    (p : T.CompleteType (Fin k)) :
    Isolated T p ↔ ∀ N : Type (max u v), ∀ _ : L.Structure N,
      Nonempty N → Countable N → N ⊨ T → ∃ x : Fin k → N, Realizes (formulas p) x := by
  constructor
  · intro hp N hN hne _ hmodel
    let := hN
    let := hne
    let := hmodel
    exact isolated_realized hT p hp
  · intro hall
    by_contra hp
    obtain ⟨N, hN, hne, hcount, hmodel, homit⟩ :=
      exists_countable_omitting (I := Unit) (n := fun _ => k) hT hsat (fun _ => p)
        (fun _ => hp)
    exact homit () (hall N hN hne hcount hmodel)

/-- The equivalent omission formulation keeps the specified theory and finite tuple context. -/
theorem nonisolated_iff_countable_omitted [Countable L.Symbols]
    (hT : T.IsComplete) (hsat : T.IsSatisfiable) {k : ℕ}
    (p : T.CompleteType (Fin k)) :
    ¬Isolated T p ↔ ∃ N : Type (max u v), ∃ _ : L.Structure N,
      Nonempty N ∧ Countable N ∧ N ⊨ T ∧ Omits N (formulas p) := by
  constructor
  · intro hp
    obtain ⟨N, hN, hne, hcount, hmodel, homit⟩ :=
      exists_countable_omitting (I := Unit) (n := fun _ => k) hT hsat (fun _ => p)
        (fun _ => hp)
    exact ⟨N, hN, hne, hcount, hmodel, homit ()⟩
  · rintro ⟨N, hN, hne, hcount, hmodel, homit⟩ hp
    exact homit ((isolated_iff_countable_realized hT hsat p).mp hp N hN hne hcount hmodel)

end
end Lemmatheca.ModelTheory.OmittingTypes
