import Lemmatheca.EffectiveEnumerations.Stages

/-! Uniform preimage indices, first used in effective inseparability. -/
namespace Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets

open UniversalComputation EffectiveEnumerations

def preimageProgram (f : ℕ → ℕ) (e x : ℕ) : Part ℕ := phi e (f x)

def PreimageIndex (f : ℕ → ℕ) (a : ℕ) : Prop :=
  ∀ e x, phi a (Nat.pair e x) = preimageProgram f e x

def preimageMap (a e : ℕ) : ℕ := specialize a e

theorem preimage_program_partial {f : ℕ → ℕ} (hf : Computable f) :
    Partrec₂ (preimageProgram f) := by
  exact phi_recursive.comp Computable.fst (hf.comp Computable.snd)

theorem preimage_index_exists {f : ℕ → ℕ} (hf : Computable f) :
    ∃ a, PreimageIndex f a := by
  obtain ⟨a, ha⟩ := phi_complete (Partrec₂.unpaired'.mpr (preimage_program_partial hf))
  refine ⟨a, fun e x => ?_⟩
  simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun ha (Nat.pair e x)

theorem preimage_map_primitive (a : ℕ) : Primrec (preimageMap a) := by
  exact specialize_primitive.comp (Primrec.const a) Primrec.id

theorem preimage_map_eval (f : ℕ → ℕ) (a : ℕ) (ha : PreimageIndex f a) (e x : ℕ) :
    phi (preimageMap a e) x = phi e (f x) := by
  exact (specialize_eval a e x).trans (ha e x)

theorem preimage_map_domain (f : ℕ → ℕ) (a : ℕ) (ha : PreimageIndex f a) (e : ℕ) :
    indexSet (preimageMap a e) = f ⁻¹' indexSet e := by
  ext x
  change (phi (preimageMap a e) x).Dom ↔ (phi e (f x)).Dom
  rw [preimage_map_eval f a ha e x]

end Lemmatheca.ComputabilityTheory.ProductiveAndCreativeSets
