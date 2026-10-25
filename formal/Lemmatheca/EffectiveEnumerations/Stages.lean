import Lemmatheca.UniversalComputation.UniversalComputation
import Lemmatheca.UniversalComputation.RecursiveFunctionConventions
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion
import Mathlib.Order.WellFounded

/-! Finite snapshots in the existing numerical program numbering. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveEnumerations

open UniversalComputation

def indexSet (e : ℕ) : Set ℕ := {x | (phi e x).Dom}

def stage (e s : ℕ) : Set ℕ :=
  {x | x < s ∧ ∃ k < s, certificate e x k}

noncomputable def stageTest (e s x : ℕ) : ℕ :=
  PrimitiveRecursion.characteristic (stage e s) x

theorem stage_bounds (e s : ℕ) :
    stage e s ⊆ Set.Iio s ∧ (stage e s).Finite ∧ stage e 0 = ∅ := by
  have hb : stage e s ⊆ Set.Iio s := fun _ hx => hx.1
  refine ⟨hb, (Set.finite_Iio s).subset hb, ?_⟩
  ext x
  simp [stage]

theorem stage_predicate_primitive :
    PrimrecPred (fun p : (ℕ × ℕ) × ℕ => p.2 ∈ stage p.1.1 p.1.2) := by
  have hR : PrimrecRel (fun p : (ℕ × ℕ) × ℕ => fun k => certificate p.1.1 p.2 k) :=
    certificate_primitive.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)
  have hB := PrimitiveRecursion.bounded_exists_primrec hR
  exact (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).and
    (hB.comp Primrec.id (Primrec.snd.comp Primrec.fst))

theorem stage_test_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => stageTest p.1.1 p.1.2 p.2) := by
  classical
  exact (Primrec.ite stage_predicate_primitive (Primrec.const 1) (Primrec.const 0)).of_eq
    (fun _ => rfl)

theorem stage_test_spec (e s x : ℕ) :
    (stageTest e s x = 0 ∨ stageTest e s x = 1) ∧
      (stageTest e s x = 1 ↔ x ∈ stage e s) := by
  exact ⟨FiniteDescriptions.characteristic_values (stage e s) x,
    (PrimitiveRecursion.characteristic_spec (stage e s) x).1⟩

theorem stage_monotone (e : ℕ) : Monotone (stage e) := by
  intro s t hst x hx
  obtain ⟨hxs, k, hks, hk⟩ := hx
  exact ⟨hxs.trans_le hst, k, hks.trans_le hst, hk⟩

theorem certificate_mem_stage (e x k : ℕ) (h : certificate e x k) :
    x ∈ stage e (max x k + 1) := by
  exact ⟨Nat.lt_succ_of_le (le_max_left x k), k,
    Nat.lt_succ_of_le (le_max_right x k), h⟩

theorem stage_union (e x : ℕ) :
    x ∈ indexSet e ↔ ∃ s, x ∈ stage e s := by
  change (phi e x).Dom ↔ _
  rw [phi_domain]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨max x k + 1, certificate_mem_stage e x k hk⟩
  · rintro ⟨s, _, k, _, hk⟩
    exact ⟨k, hk⟩

/-- All finite bounds and zero-one tests are supplied as actual computable data. -/
structure ComputableApproximation (A : Set ℕ) where
  bound : ℕ → ℕ
  test : ℕ → ℕ → ℕ
  bound_computable : Computable bound
  test_computable : Computable₂ test
  binary : ∀ s x, test s x = 0 ∨ test s x = 1
  bounded : ∀ s x, test s x = 1 → x < bound s
  increasing : ∀ s x, test s x = 1 → test (s + 1) x = 1
  exhaustive : ∀ x, x ∈ A ↔ ∃ s, test s x = 1

def ComputableApproximation.atStage {A : Set ℕ} (F : ComputableApproximation A)
    (s : ℕ) : Set ℕ := {x | F.test s x = 1}

theorem approximation_stages {A : Set ℕ} (F : ComputableApproximation A) :
    (∀ s, (F.atStage s).Finite ∧ F.atStage s ⊆ A) ∧ Monotone F.atStage ∧
      (∀ x, x ∈ A ↔ ∃ s, x ∈ F.atStage s) := by
  refine ⟨?_, ?_, F.exhaustive⟩
  · intro s
    exact ⟨(Set.finite_Iio (F.bound s)).subset (F.bounded s),
      fun x hx => (F.exhaustive x).mpr ⟨s, hx⟩⟩
  · apply monotone_nat_of_le_succ
    intro s x hx
    exact F.increasing s x hx

theorem canonical_test_data (e : ℕ) :
    Computable₂ (stageTest e) ∧
      (∀ s x, stageTest e s x = 0 ∨ stageTest e s x = 1) ∧
      (∀ s x, stageTest e s x = 1 → x < s) ∧
      (∀ s x, stageTest e s x = 1 → stageTest e (s + 1) x = 1) ∧
      (∀ x, x ∈ indexSet e ↔ ∃ s, stageTest e s x = 1) := by
  refine ⟨stage_test_primitive.to_comp.comp
    (((Computable.const e).pair Computable.fst).pair Computable.snd),
    fun s x => (stage_test_spec e s x).1, ?_, ?_, ?_⟩
  · intro s x hx
    exact ((stage_test_spec e s x).2.mp hx).1
  · intro s x hx
    exact (stage_test_spec e (s + 1) x).2.mpr
      (stage_monotone e (Nat.le_succ s) ((stage_test_spec e s x).2.mp hx))
  · intro x
    rw [stage_union]
    exact exists_congr (fun s => (stage_test_spec e s x).2.symm)

noncomputable def canonicalApproximation (e : ℕ) : ComputableApproximation (indexSet e) where
  bound := id
  test := stageTest e
  bound_computable := Computable.id
  test_computable := (canonical_test_data e).1
  binary := (canonical_test_data e).2.1
  bounded := (canonical_test_data e).2.2.1
  increasing := (canonical_test_data e).2.2.2.1
  exhaustive := (canonical_test_data e).2.2.2.2

theorem canonical_stages (e s : ℕ) :
    (canonicalApproximation e).bound s = s ∧
      (canonicalApproximation e).atStage s = stage e s := by
  refine ⟨rfl, ?_⟩
  ext x
  exact (stage_test_spec e s x).2

theorem approximation_enumerable {A : Set ℕ} (F : ComputableApproximation A) :
    REPred A := by
  classical
  apply (enumerable_iff_decidable_certificate A).mpr
  refine ⟨fun x s => F.test s x = 1, ?_, F.exhaustive⟩
  apply Computable.computablePred
  exact Primrec.eq.decide.to_comp.comp
    (F.test_computable.comp Computable.snd Computable.fst) (Computable.const 1)

end Lemmatheca.ComputabilityTheory.EffectiveEnumerations
