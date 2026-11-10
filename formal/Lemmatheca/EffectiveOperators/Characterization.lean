import Lemmatheca.EffectiveOperators.Canonical

/-! Uniqueness on arbitrary partial functions and the Myhill–Shepherdson theorem. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveOperators

open UniversalComputation RiceShapiroTheorem
open RicesTheorem (PartialFunction)

noncomputable section
open Classical

theorem effective_unique_from_fragments (Φ Ψ : PartialFunction → PartialFunction)
    (hΦ : IsEffective Φ) (hΨ : IsEffective Ψ)
    (hfinite : ∀ d, Valid d → Φ (fragment d) = Ψ (fragment d)) : Φ = Ψ := by
  obtain ⟨R, hpR, hcR, _, rfl⟩ := hΦ
  obtain ⟨S, hpS, hcS, _, rfl⟩ := hΨ
  funext f x
  apply Part.ext
  intro y
  constructor
  · intro hy
    obtain ⟨d, hd, hdf, hdy⟩ := (operator_finite_information R hpR hcR f x y).mp hy
    rw [hfinite d hd] at hdy
    exact operator_monotone S hpS hcS (fragment d) f hdf x y hdy
  · intro hy
    obtain ⟨d, hd, hdf, hdy⟩ := (operator_finite_information S hpS hcS f x y).mp hy
    rw [← hfinite d hd] at hdy
    exact operator_monotone R hpR hcR (fragment d) f hdf x y hdy

theorem effective_unique_from_computable (Φ Ψ : PartialFunction → PartialFunction)
    (hΦ : IsEffective Φ) (hΨ : IsEffective Ψ)
    (hcomp : ∀ e, Φ (phi e) = Ψ (phi e)) : Φ = Ψ := by
  apply effective_unique_from_fragments Φ Ψ hΦ hΨ
  intro d _
  have hf : phi (fragmentIndex d) = fragment d := funext (fragmentIndex_eval d)
  simpa only [hf] using hcomp (fragmentIndex d)

theorem myhill_shepherdson (H : ℕ → ℕ) (hH : Computable H) (hext : IndexExtensional H) :
    ∃! Φ : PartialFunction → PartialFunction,
      IsEffective Φ ∧ ∀ e, Φ (phi e) = phi (H e) := by
  refine ⟨operator (canonicalRules H),
    ⟨canonical_operator_effective H hH hext, canonical_operator_correct H hH hext⟩, ?_⟩
  intro Ψ hΨ
  apply effective_unique_from_computable Ψ (operator (canonicalRules H)) hΨ.1
    (canonical_operator_effective H hH hext)
  intro e
  exact (hΨ.2 e).trans (canonical_operator_correct H hH hext e).symm

theorem effective_compiler_exists (Φ : PartialFunction → PartialFunction)
    (hΦ : IsEffective Φ) :
    ∃ r, (∃ R, Positive R ∧ Coherent R ∧ EnumeratesRules r R ∧ Φ = operator R) ∧
      Primrec (compiler r) ∧ IndexExtensional (compiler r) ∧
        ∀ e x, phi (compiler r e) x = Φ (phi e) x := by
  obtain ⟨R, hp, hc, hce, heq⟩ := hΦ
  obtain ⟨r, hr⟩ := (jointly_enumerable_iff_index R).mp hce
  refine ⟨r, ⟨R, hp, hc, hr, heq⟩, ?_, compiler_extensional R r hr hp hc, ?_⟩
  · exact (UniformSelfReference.partial_family_compiler_primitive ruleSearchProgram).comp
      (Primrec.const r) Primrec.id
  · intro e x
    rw [heq]
    exact compiler_correct R r hr hp hc e x

end
end Lemmatheca.ComputabilityTheory.EffectiveOperators
