import Lemmatheca.UniformSelfReference.Uniform
import Lemmatheca.RicesTheorem.RicesTheorem

/-! The specified constant-runtime-input reduction into the existing zero-input halting set. -/
namespace Lemmatheca.ComputabilityTheory.UniformSelfReference

open UniversalComputation

theorem diagonal_to_zero_compiler :
    ∃ p, (∀ e z, phi p (Nat.pair e z) = phi e e) ∧
      Primrec (selector p) ∧
      (∀ e z, phi (selector p e) z = phi e e) ∧
      ∀ e, e ∈ haltingDiagonal ↔ selector p e ∈ RicesTheorem.haltsZero := by
  have hh : Partrec₂ (fun e _ : ℕ => phi e e) :=
    phi_recursive.comp Computable.fst Computable.fst
  obtain ⟨p, hp⟩ := phi_complete (Partrec₂.unpaired'.mpr hh)
  have hp' : ∀ e z, phi p (Nat.pair e z) = phi e e := by
    intro e z
    simpa only [Nat.unpaired, Nat.unpair_pair] using congrFun hp (Nat.pair e z)
  have he : ∀ e z, phi (selector p e) z = phi e e :=
    fun e z => (specialize_eval p e z).trans (hp' e z)
  refine ⟨p, hp', selector_primitive p, he, fun e => ?_⟩
  change (phi e e).Dom ↔ (phi (selector p e) 0).Dom
  rw [he]

end Lemmatheca.ComputabilityTheory.UniformSelfReference
