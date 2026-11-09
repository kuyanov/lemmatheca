import Lemmatheca.EffectiveInseparability.Universality

/-! Pulling back separators and retaining unconstrained inputs. -/
namespace Lemmatheca.Entry.EffectiveInseparability

open Lemmatheca.ComputabilityTheory
open UniversalComputation ComputableSeparation EffectiveInseparability

theorem separator_preimage {C D A B S : Set ℕ} {f : ℕ → ℕ}
    (hf : PairReduction C D A B f) (hS : Separator A B S) :
    Separator C D (f ⁻¹' S) ∧
      (∀ x, indicator (f ⁻¹' S) x = indicator S (f x)) ∧
      (ComputablePred S → ComputablePred (f ⁻¹' S)) := by
  classical
  refine ⟨⟨fun x hx => hS.1 ((hf.2.1 x).mp hx), Set.disjoint_left.mpr ?_⟩,
    fun _ => rfl, ?_⟩
  · intro x hx hd
    exact Set.disjoint_left.mp hS.2 hx ((hf.2.2 x).mp hd)
  · rintro ⟨hdec, hcomp⟩
    exact ⟨fun x => hdec (f x), hcomp.comp hf.1⟩

theorem empty_source_separator_counterexample {A B : Set ℕ}
    (hAB : EffectivelyInseparable A B) :
    ∃ z, z ∉ A ∪ B ∧ PairReduction ∅ ∅ A B (fun _ => z) ∧
      Separator A B (A ∪ {z}) ∧ (fun _ : ℕ => z) ⁻¹' (A ∪ {z}) = Set.univ ∧
      (fun _ : ℕ => z) ⁻¹' (A ∪ {z}) ≠ (∅ : Set ℕ) := by
  obtain ⟨z, hz⟩ := complement_nonempty hAB
  have hza : z ∉ A := fun ha => hz (Or.inl ha)
  have hzb : z ∉ B := fun hb => hz (Or.inr hb)
  refine ⟨z, hz, ⟨Computable.const z, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hza]
  · simp [hzb]
  · refine ⟨Set.subset_union_left, Set.disjoint_left.mpr ?_⟩
    intro x hx hb
    rcases hx with ha | hx
    · exact Set.disjoint_left.mp hAB.2.2.1 ha hb
    · exact hzb ((Set.mem_singleton_iff.mp hx) ▸ hb)
  · ext x
    simp
  · intro he
    have hmem : (0 : ℕ) ∈ (fun _ : ℕ => z) ⁻¹' (A ∪ {z}) := by simp
    rw [he] at hmem
    exact hmem

end Lemmatheca.Entry.EffectiveInseparability
