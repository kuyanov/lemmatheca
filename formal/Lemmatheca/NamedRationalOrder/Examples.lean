import Lemmatheca.NamedRationalOrder.Types

namespace Lemmatheca.Entry.NamedRationalOrder

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.NamedRationalOrder
open Lemmatheca.ModelTheory.Types
open Lemmatheca.MathematicalLogic.FirstOrderSyntax

/-- The named rational order has a proper countable elementary extension realizing the request. -/
theorem another_countable_model :
    ∃ M : theory.ModelType.{0, 0, 0}, Countable M ∧ ∃ b : Fin 1 → M,
      Realizes aboveAll b ∧
      (∀ q : ℚ, (binaryRelLanguage.con q : M) ≠ b 0) ∧
      ¬ Nonempty (rationalModel ≃[rationalLanguage] M) := by
  obtain ⟨p, hp⟩ := exists_complete_extension aboveAll aboveAll_partial
  obtain ⟨M, hc, b, hb⟩ := Lemmatheca.ModelTheory.CountableCategoricity.countable_realization p
  have hreal : Realizes aboveAll b := fun φ hφ => hb φ (hp hφ)
  refine ⟨M, hc, b, hreal, fun q hq => ?_, fun ⟨e⟩ => ?_⟩
  · let a : Fin 1 → rationalModel := fun _ => q
    have he : b = canonicalEmbedding M ∘ a := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hq.symm
    have ht : (aboveFormula q).Realize (canonicalEmbedding M ∘ a) :=
      he ▸ hreal _ (Set.mem_range_self q)
    have hn := ((canonicalEmbedding M).map_formula (aboveFormula q) a).mp ht
    exact lt_irrefl (α := ℚ) q ((aboveFormula_realize q a).mp hn)
  · apply aboveAll_omitted
    refine ⟨e.symm ∘ b, fun φ hφ => ?_⟩
    exact (e.symm.toElementaryEmbedding.map_formula φ b).mpr (hreal φ hφ)

/-- Some complete type extends the above-all-names request and is omitted by the named real model. -/
theorem not_only_real_types : ∃ p : theory.CompleteType (Fin 1),
    aboveAll ⊆ formulas p ∧ ∀ r : ℝ, p ≠ realType r := by
  obtain ⟨p, hp⟩ := exists_complete_extension aboveAll aboveAll_partial
  refine ⟨p, hp, fun r he => ?_⟩
  obtain ⟨q, hrq, _⟩ := exists_rat_btwn (lt_add_one r)
  have hφ : aboveFormula q ∈ formulas (realType r) := he ▸ hp (Set.mem_range_self q)
  have h := Theory.CompleteType.formula_mem_typeOf.mp hφ
  change (q : ℝ) < r at h
  exact lt_asymm hrq h

end Lemmatheca.Entry.NamedRationalOrder
