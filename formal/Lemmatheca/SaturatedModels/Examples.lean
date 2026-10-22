import Lemmatheca.SaturatedModels.Saturation
import Lemmatheca.TypesAndRealization.Examples

namespace Lemmatheca.Entry.SaturatedModels

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory

theorem standard_arithmetic_not_omega :
    ¬ Saturation.OmegaSaturated ArithmeticTheories.language ℕ := by
  classical
  intro h
  let L := ArithmeticTheories.language
  let A : Set ℕ := ∅
  let k := L.lhomWithConstants A
  let p := k.onFormula '' TypesAndRealization.nonstandardConditions
  have hp : Types.IsPartial (L[[A]].completeTheory ℕ) p := by
    apply (Types.partial_iff_finitelyRealized_completeTheory _).mpr
    intro s hs
    let pick (ψ : s) := Classical.choose (hs ψ.property)
    have hpick (ψ : s) : pick ψ ∈ TypesAndRealization.nonstandardConditions ∧
        k.onFormula (pick ψ) = ψ := Classical.choose_spec (hs ψ.property)
    let t := s.attach.image pick
    obtain ⟨a, ha⟩ := TypesAndRealization.nonstandard_finitely_realized t (by
      rintro φ hφ
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
      exact (hpick ψ).1)
    refine ⟨a, fun ψ hψ => ?_⟩
    have hh := (LHom.realize_onFormula k (pick ⟨ψ, hψ⟩)).mpr
      (ha _ (Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩))
    rwa [(hpick ⟨ψ, hψ⟩).2] at hh
  obtain ⟨a, ha⟩ := (Saturation.omega_iff_partial.mp h) A Set.finite_empty p hp
  apply TypesAndRealization.nonstandard_omitted
  exact ⟨a, fun φ hφ => (LHom.realize_onFormula k φ).mp (ha _ ⟨φ, hφ, rfl⟩)⟩

end Lemmatheca.Entry.SaturatedModels
