import Mathlib.ModelTheory.DirectLimit

/-! Construct a structure on an unstructured union carrier, retaining the given maps. -/

namespace Lemmatheca.ModelTheory.ElementaryChains

open FirstOrder FirstOrder.Language

universe u v w w'

/-- A compatible sequence of structures puts a structure on any set-theoretic
union carrier. The maps into that carrier are specified before its structure. -/
theorem exists_union_structure {L : Language.{u, v}} (G : ℕ → Type w)
    [∀ n, L.Structure (G n)] (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem G (fun i j h => f i j h)] {U : Type w'}
    (j : ∀ n, G n ↪ U)
    (hcompat : ∀ a b (h : a ≤ b) x, j b (f a b h x) = j a x)
    (hcover : ∀ x : U, ∃ n a, j n a = x) :
    ∃ S : L.Structure U, ∀ n,
      ∃ e : @Language.Embedding L (G n) U (inferInstance : L.Structure (G n)) S,
        (e : G n → U) = j n := by
  classical
  let q : FirstOrder.Language.DirectLimit G f → U := Quotient.lift
    (fun x : Structure.Sigma f => j x.1 x.2)
    (fun x y h => by
      obtain ⟨k, hx, hy, hxy⟩ := h
      exact (hcompat x.1 k hx x.2).symm.trans
        ((congrArg (j k) hxy).trans (hcompat y.1 k hy y.2)))
  have hq (n : ℕ) (a : G n) : q (FirstOrder.Language.DirectLimit.of L ℕ G f n a) = j n a := rfl
  have hqin : Function.Injective q := by
    intro a b hab
    obtain ⟨n, x, rfl⟩ := FirstOrder.Language.DirectLimit.exists_of a
    obtain ⟨m, y, rfl⟩ := FirstOrder.Language.DirectLimit.exists_of b
    apply Quotient.sound
    refine ⟨max n m, le_max_left _ _, le_max_right _ _, ?_⟩
    apply (j (max n m)).injective
    rw [hcompat n (max n m) (le_max_left _ _) x,
      hcompat m (max n m) (le_max_right _ _) y]
    exact hab
  have hqsur : Function.Surjective q := by
    intro x
    obtain ⟨n, a, rfl⟩ := hcover x
    exact ⟨FirstOrder.Language.DirectLimit.of L ℕ G f n a, hq n a⟩
  let e : FirstOrder.Language.DirectLimit G f ≃ U := Equiv.ofBijective q ⟨hqin, hqsur⟩
  let : L.Structure U := e.inducedStructure
  refine ⟨inferInstance, fun n => ?_⟩
  refine ⟨e.inducedStructureEquiv.toEmbedding.comp (FirstOrder.Language.DirectLimit.of L ℕ G f n), ?_⟩
  funext a
  exact hq n a

end Lemmatheca.ModelTheory.ElementaryChains
