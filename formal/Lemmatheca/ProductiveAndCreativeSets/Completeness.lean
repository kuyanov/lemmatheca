import Lemmatheca.ProductiveAndCreativeSets.Productivity
import Lemmatheca.UniformSelfReference.Uniform

/-! The uniform singleton-domain construction and its specified many-one map. -/
namespace Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets

open UniversalComputation EffectiveEnumerations UniformSelfReference RecursionTheorem

def singletonProgram (a : ℕ) (p : ℕ → ℕ) (e y x : ℕ) : Part ℕ :=
  if x = p e then (phi a y).map (fun _ => 0) else Part.none

def SingletonIndex (a : ℕ) (p : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ e y x, phi v (Nat.pair e (Nat.pair y x)) = singletonProgram a p e y x

def IsSingletonSelector (a : ℕ) (p h : ℕ → ℕ) : Prop :=
  Primrec h ∧ ∀ y x, phi (h y) x = singletonProgram a p (h y) y x

theorem singleton_program_partial (a : ℕ) {p : ℕ → ℕ} (hp : Computable p) :
    Partrec (fun t : ℕ × (ℕ × ℕ) => singletonProgram a p t.1 t.2.1 t.2.2) := by
  have htest : Computable (fun t : ℕ × (ℕ × ℕ) => decide (t.2.2 = p t.1)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.snd)
      (hp.comp Computable.fst)
  have hr : Partrec (fun t : ℕ × (ℕ × ℕ) => phi a t.2.1) :=
    phi_recursive.comp (Computable.const a) (Computable.fst.comp Computable.snd)
  exact (Partrec.cond htest (hr.map (Computable.const 0).to₂) Partrec.none).of_eq
    (fun t => by simp [singletonProgram])

theorem singleton_program_domain (a : ℕ) (p : ℕ → ℕ) (e y x : ℕ) :
    (singletonProgram a p e y x).Dom ↔ x = p e ∧ y ∈ indexSet a := by
  by_cases he : x = p e <;> simp [singletonProgram, he, indexSet]

theorem singleton_program_certificate (a : ℕ) (p : ℕ → ℕ) (e y x : ℕ) :
    (singletonProgram a p e y x).Dom ↔
      x = p e ∧ ∃ k, certificate a y k := by
  rw [singleton_program_domain]
  exact and_congr_right (fun _ => phi_domain a y)

theorem singleton_index_exists (a : ℕ) {p : ℕ → ℕ} (hp : Computable p) :
    ∃ v, SingletonIndex a p v := by
  exact partial_family_index (singleton_program_partial a hp)

theorem specified_singleton_selector (a : ℕ) (p : ℕ → ℕ) (v : ℕ)
    (hv : SingletonIndex a p v) :
    ∃ r, AuxiliaryIndex (partialFamilyCompiler v) r ∧
      IsSingletonSelector a p (selector (selfSpecialize r)) := by
  obtain ⟨r, hr, hprim, he⟩ := specified_partial_family_selector v hv
  exact ⟨r, hr, hprim, he⟩

theorem singleton_selector_exists (a : ℕ) {p : ℕ → ℕ} (hp : Computable p) :
    ∃ v, SingletonIndex a p v ∧
      ∃ r, AuxiliaryIndex (partialFamilyCompiler v) r ∧
        IsSingletonSelector a p (selector (selfSpecialize r)) := by
  obtain ⟨v, hv⟩ := singleton_index_exists a hp
  obtain ⟨r, hr, hh⟩ := specified_singleton_selector a p v hv
  exact ⟨v, hv, r, hr, hh⟩

theorem singleton_selector_domains (a : ℕ) (p h : ℕ → ℕ)
    (hh : IsSingletonSelector a p h) (y : ℕ) :
    (y ∈ indexSet a → indexSet (h y) = {p (h y)}) ∧
      (y ∉ indexSet a → indexSet (h y) = ∅) := by
  constructor
  · intro hy
    ext x
    change (phi (h y) x).Dom ↔ x ∈ {p (h y)}
    rw [hh.2 y x, singleton_program_domain]
    simp [hy]
  · intro hy
    ext x
    change (phi (h y) x).Dom ↔ x ∈ (∅ : Set ℕ)
    rw [hh.2 y x, singleton_program_domain]
    simp [hy]

def creativeReduction (p h : ℕ → ℕ) (y : ℕ) : ℕ := p (h y)

theorem specified_creative_reduction {C : Set ℕ} {p : ℕ → ℕ}
    (hp : ProductiveFunction Cᶜ p) (a : ℕ) (h : ℕ → ℕ)
    (hh : IsSingletonSelector a p h) :
    Computable (creativeReduction p h) ∧
      ∀ y, y ∈ indexSet a ↔ creativeReduction p h y ∈ C := by
  classical
  refine ⟨hp.1.comp hh.1.to_comp, ?_⟩
  intro y
  constructor
  · intro hy
    by_contra hnC
    have hsingle := (singleton_selector_domains a p h hh y).1 hy
    have hsub : indexSet (h y) ⊆ Cᶜ := by
      rw [hsingle]
      exact Set.singleton_subset_iff.mpr hnC
    exact (hp.2 (h y) hsub).2 (by rw [hsingle]; exact Set.mem_singleton _)
  · intro hc
    by_contra hny
    have hempty := (singleton_selector_domains a p h hh y).2 hny
    have hsub : indexSet (h y) ⊆ Cᶜ := by simp [hempty]
    exact (hp.2 (h y) hsub).1 hc

theorem creative_complete {C : Set ℕ} (hC : Creative C) {A : ℕ → Prop}
    (hA : REPred A) : A ≤₀ C := by
  obtain ⟨p, hp⟩ := hC.2
  obtain ⟨a, ha⟩ := (enumerable_iff_index A).mp hA
  obtain ⟨v, hv, r, _, hh⟩ := singleton_selector_exists a hp.1
  obtain ⟨hcomp, hiff⟩ := specified_creative_reduction hp a
    (selector (selfSpecialize r)) hh
  exact ⟨creativeReduction p (selector (selfSpecialize r)), hcomp,
    fun y => (ha y).trans (hiff y)⟩

theorem creative_iff_complete {C : Set ℕ} (hC : REPred C) :
    Creative C ↔ ∀ A : ℕ → Prop, REPred A → A ≤₀ C := by
  constructor
  · intro hc A ha
    exact creative_complete hc ha
  · intro hc
    exact complete_implies_creative hC (hc haltingDiagonal haltingDiagonal_enumerable)

theorem creative_iff_diagonal_reduces {C : Set ℕ} (hC : REPred C) :
    Creative C ↔ haltingDiagonal ≤₀ C := by
  exact ⟨fun hc => creative_complete hc haltingDiagonal_enumerable,
    complete_implies_creative hC⟩

end Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets
