import Lemmatheca.PaddingAndInjectiveReductions.Padding
import Lemmatheca.ProductiveAndCreativeSets.Productivity
import Lemmatheca.RicesTheorem.RicesTheorem

/-! Injective translations using the already specified constant-run map. -/
namespace Lemmatheca.ComputabilityTheory.PaddingAndInjectiveReductions

open UniversalComputation ProductiveAndCreativeSets RicesTheorem

theorem constantRunMap_injective (v : ℕ) : Function.Injective (constantRunMap v) := by
  intro w w' h
  exact (specialize_injective h).2

def diagonalPair (e : ℕ) : ℕ := Nat.pair e e

def zeroPair (e : ℕ) : ℕ := Nat.pair e 0

theorem diagonalPair_contract :
    Primrec diagonalPair ∧ Function.Injective diagonalPair ∧
      ∀ e, e ∈ haltingDiagonal ↔ diagonalPair e ∈ haltingPairs := by
  refine ⟨Primrec₂.natPair.comp Primrec.id Primrec.id, ?_, ?_⟩
  · intro e f h
    exact (Nat.pair_eq_pair.mp h).1
  · intro e
    simp [diagonalPair, haltingDiagonal, haltingPairs]

theorem zeroPair_contract :
    Primrec zeroPair ∧ Function.Injective zeroPair ∧
      ∀ e, e ∈ haltsZero ↔ zeroPair e ∈ haltingPairs := by
  refine ⟨Primrec₂.natPair.comp Primrec.id (Primrec.const 0), ?_, ?_⟩
  · intro e f h
    exact (Nat.pair_eq_pair.mp h).1
  · intro e
    simp [zeroPair, haltsZero, haltingPairs]

theorem constant_run_zero_membership (v : ℕ) (hv : ConstantRunIndex v) :
    ∀ w, w ∈ haltingPairs ↔ constantRunMap v w ∈ haltsZero := by
  intro w
  have he : phi (constantRunMap v w) 0 = phi w.unpair.1 w.unpair.2 :=
    (specialize_eval v w 0).trans (hv w 0)
  change (phi w.unpair.1 w.unpair.2).Dom ↔ (phi (constantRunMap v w) 0).Dom
  rw [he]

def enumerableMap (v a x : ℕ) : ℕ := constantRunMap v (Nat.pair a x)

theorem enumerableMap_primitive (v a : ℕ) : Primrec (enumerableMap v a) := by
  exact (constant_run_map_primitive v).comp
    (Primrec₂.natPair.comp (Primrec.const a) Primrec.id)

theorem enumerableMap_injective (v a : ℕ) : Function.Injective (enumerableMap v a) := by
  apply (constantRunMap_injective v).comp
  intro x y h
  exact (Nat.pair_eq_pair.mp h).2

theorem enumerableMap_membership (v : ℕ) (hv : ConstantRunIndex v) (a x : ℕ) :
    x ∈ EffectiveEnumerations.indexSet a ↔ enumerableMap v a x ∈ haltingDiagonal := by
  simpa [enumerableMap, EffectiveEnumerations.indexSet, haltingPairs] using
    constant_run_reduction v hv (Nat.pair a x)

theorem oneone_complete (A : Set ℕ) : REPred A ↔ A ≤₁ haltingDiagonal := by
  constructor
  · intro hA
    obtain ⟨a, ha⟩ := (enumerable_iff_index A).mp hA
    obtain ⟨v, hv⟩ := constant_run_index_exists
    exact ⟨enumerableMap v a, (enumerableMap_primitive v a).to_comp,
      enumerableMap_injective v a, fun x => (ha x).trans (enumerableMap_membership v hv a x)⟩
  · intro h
    exact ComputableReductions.enumerable_preimage h.to_many_one haltingDiagonal_enumerable

end Lemmatheca.ComputabilityTheory.PaddingAndInjectiveReductions
