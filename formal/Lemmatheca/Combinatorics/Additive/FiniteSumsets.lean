import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Cardinality bounds for finite sumsets

The first proof follows the two translations in the human lemma. The second
explicitly applies that lemma twice. Only elementary group, finite-set, and order
infrastructure is used from mathlib; neither proof calls an upstream sumset bound.
-/

namespace Lemmatheca

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The nonemptiness lemma in the first note. -/
theorem finite_sumset_nonempty (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) : (A + B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a + b, Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩⟩

/-- A nonempty finite sumset is at least as large as either summand. -/
theorem sumset_card_lower_bound (A B : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) :
    max A.card B.card ≤ (A + B).card := by
  obtain ⟨b₀, hb₀⟩ := hB
  have hleft : A.card ≤ (A + B).card := by
    apply Finset.card_le_card_of_injOn (fun a => a + b₀)
    · intro a ha
      exact Finset.mem_add.mpr ⟨a, ha, b₀, hb₀, rfl⟩
    · intro a _ a' _ h
      exact add_right_cancel h
  obtain ⟨a₀, ha₀⟩ := hA
  have hright : B.card ≤ (A + B).card := by
    apply Finset.card_le_card_of_injOn (fun b => a₀ + b)
    · intro b hb
      exact Finset.mem_add.mpr ⟨a₀, ha₀, b, hb, rfl⟩
    · intro b _ b' _ h
      exact add_left_cancel h
  exact max_le hleft hright

/-- Adding the singleton zero does not change a finite set. -/
theorem sumset_zero (A : Finset G) : A + {0} = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
    have hb0 : b = 0 := Finset.mem_singleton.mp hb
    have hax : a = x := by simpa only [hb0, add_zero] using hab
    exact hax ▸ ha
  · intro hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, Finset.mem_singleton_self 0, add_zero x⟩

/-- Both intermediate sums in the second note are nonempty. -/
theorem triple_sumset_nonempty (A B C : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    (A + B).Nonempty ∧ ((A + B) + C).Nonempty := by
  have hAB := finite_sumset_nonempty A B hA hB
  exact ⟨hAB, finite_sumset_nonempty (A + B) C hAB hC⟩

/-- Applying the sumset lower bound twice bounds a triple sumset. -/
theorem triple_sumset_card_lower_bound (A B C : Finset G)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    max (max A.card B.card) C.card ≤ ((A + B) + C).card := by
  have hAB := (triple_sumset_nonempty A B C hA hB hC).1
  have hfirst := sumset_card_lower_bound A B hA hB
  have hsecond := sumset_card_lower_bound (A + B) C hAB hC
  have hAB_le : (A + B).card ≤ ((A + B) + C).card :=
    (le_max_left _ _).trans hsecond
  have hC_le : C.card ≤ ((A + B) + C).card :=
    (le_max_right _ _).trans hsecond
  exact max_le (hfirst.trans hAB_le) hC_le

/-- The answer to the first question: nonemptiness cannot be omitted. -/
theorem sumset_empty_counterexample :
    ¬ max (∅ : Finset Int).card ({0} : Finset Int).card ≤
      ((∅ : Finset Int) + {0}).card := by
  decide

/-- The answer to the second question: a third summand need not cause growth. -/
theorem triple_sumset_no_strict_growth :
    (({0} : Finset Int) + {0}) + {0} = {0} := by
  rw [sumset_zero, sumset_zero]

end Lemmatheca
