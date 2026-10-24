import Lemmatheca.RecursionTheorem.RecursionTheorem

namespace Lemmatheca.Entry.RecursionTheorem

open Lemmatheca.ComputabilityTheory.UniversalComputation
open Lemmatheca.ComputabilityTheory.RecursionTheorem

theorem successor_semantic_fixed_point :
    ∃ e, SemanticFixedPoint Nat.succ e ∧ e ≠ e + 1 := by
  obtain ⟨e, he⟩ := transformer_fixed_point Computable.succ
  exact ⟨e, he, by omega⟩

/-- Existence of an auxiliary index, and correctness for every such index. -/
theorem self_output :
    (∃ q, ∀ a x, phi q (Nat.pair a x) = Part.some (selfSpecialize a)) ∧
      ∀ q, (∀ a x, phi q (Nat.pair a x) = Part.some (selfSpecialize a)) →
        ∀ x, phi (selfSpecialize q) x = Part.some (selfSpecialize q) := by
  have hg : Partrec₂ (fun a (_ : ℕ) => Part.some a) :=
    (Primrec₂.left (α := ℕ) (β := ℕ)).to_comp.partrec₂
  obtain ⟨q, hq, _⟩ := recursion_theorem hg
  refine ⟨⟨q, hq⟩, ?_⟩
  intro q hq
  exact specified_fixed_point (g := fun a (_ : ℕ) => Part.some a) q hq

theorem shifted_self_reference :
    (∃ q, ∀ a x, phi q (Nat.pair a x) = Part.some (selfSpecialize a + x)) ∧
      ∀ q, (∀ a x, phi q (Nat.pair a x) = Part.some (selfSpecialize a + x)) →
        ∀ x, phi (selfSpecialize q) x = Part.some (selfSpecialize q + x) := by
  have hg : Partrec₂ (fun a x => Part.some (a + x)) :=
    Primrec.nat_add.to_comp.partrec₂
  obtain ⟨q, hq, _⟩ := recursion_theorem hg
  refine ⟨⟨q, hq⟩, ?_⟩
  intro q hq
  exact specified_fixed_point (g := fun a x => Part.some (a + x)) q hq

theorem divergent_fixed_point :
    (∃ e, ∀ x, phi e x = (phi e x).map Nat.succ) ∧
      ∀ e, (∀ x, phi e x = (phi e x).map Nat.succ) →
        ∀ x, ¬ (phi e x).Dom := by
  have hg : Partrec₂ (fun e x => (phi e x).map Nat.succ) :=
    (phi_recursive.map (Computable.succ.comp Computable.snd).to₂).to₂
  obtain ⟨q, _, he⟩ := recursion_theorem hg
  refine ⟨⟨selfSpecialize q, he⟩, ?_⟩
  intro e h x hd
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hd
  have hs : n + 1 ∈ phi e x := by
    rw [h x]
    exact Part.mem_map _ hn
  have := Part.mem_unique hs hn
  omega

end Lemmatheca.Entry.RecursionTheorem
