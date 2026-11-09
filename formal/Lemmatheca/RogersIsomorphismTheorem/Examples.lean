import Lemmatheca.RogersIsomorphismTheorem.Translation

/-! The two questions about collapsed padding and changed runtime inputs. -/
namespace Lemmatheca.Entry.RogersIsomorphismTheorem

open Lemmatheca.ComputabilityTheory
open UniversalComputation UniformSelfReference Rogers PaddingAndInjectiveReductions

noncomputable section

def collapsingCompiler (e j : ℕ) : ℕ :=
  if j = pad e 1 then pad e 0 else j

theorem padding_can_collapse (e : ℕ) :
    pad e 0 ≠ pad e 1 ∧ Computable (collapsingCompiler e) ∧
      (∀ j x, phi (collapsingCompiler e j) x = phi j x) ∧
      collapsingCompiler e (pad e 0) = collapsingCompiler e (pad e 1) := by
  have hne : pad e 0 ≠ pad e 1 := by
    intro h
    exact Nat.zero_ne_one (pad_injective h).2
  have hb : Computable (collapsingCompiler e) :=
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const (pad e 1)))
      (Primrec.const (pad e 0)) Primrec.id).to_comp
  refine ⟨hne, hb, ?_, ?_⟩
  · intro j x
    by_cases hj : j = pad e 1
    · subst j
      simpa [collapsingCompiler] using
        (pad_eval e 0 x).trans (pad_eval e 1 x).symm
    · simp only [collapsingCompiler, ite_eq_right hj]
  · simp [collapsingCompiler, hne]

theorem halting_inputs {ψ : ℕ → ℕ → Part ℕ} (C : Compilers ψ) :
    (∀ e, (ψ (permutation C e) 0).Dom ↔ (phi e 0).Dom) ∧
      Set.image (permutation C) {e | (phi e 0).Dom} = {n | (ψ n 0).Dom} ∧
      (∀ e, (ψ (permutation C e) (permutation C e)).Dom ↔
        (phi e (permutation C e)).Dom) ∧
      (Set.image (permutation C) {e | (phi e e).Dom} = {n | (ψ n n).Dom} ↔
        ∀ e, (phi e e).Dom ↔ (phi e (permutation C e)).Dom) := by
  have h := rogers_isomorphism C
  have hzero (e : ℕ) : (ψ (permutation C e) 0).Dom ↔ (phi e 0).Dom := by
    rw [h.2.2.2.2 e 0]
  have hdiag (e : ℕ) : (ψ (permutation C e) (permutation C e)).Dom ↔
      (phi e (permutation C e)).Dom := by
    rw [h.2.2.2.2 e (permutation C e)]
  have himage (A B : Set ℕ) : Set.image (permutation C) A = B ↔
      ∀ e, e ∈ A ↔ permutation C e ∈ B := by
    constructor
    · intro heq e
      constructor
      · intro he
        rw [← heq]
        exact ⟨e, he, rfl⟩
      · intro he
        rw [← heq] at he
        obtain ⟨j, hj, hje⟩ := he
        have hje' : j = e := h.2.2.1.injective hje
        simpa only [hje'] using hj
    · intro hi
      ext n
      constructor
      · rintro ⟨e, he, rfl⟩
        exact (hi e).mp he
      · intro hn
        refine ⟨inversePermutation C n, ?_, h.2.2.2.1 n⟩
        apply (hi _).mpr
        exact (h.2.2.2.1 n).symm ▸ hn
  refine ⟨hzero, (himage _ _).mpr (fun e => (hzero e).symm), hdiag, ?_⟩
  rw [himage]
  constructor
  · intro hall e
    exact (hall e).trans (hdiag e)
  · intro hall e
    exact (hall e).trans (hdiag e).symm

end
end Lemmatheca.Entry.RogersIsomorphismTheorem
