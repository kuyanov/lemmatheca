import Lemmatheca.ForcingChainConditions.Orders
import Lemmatheca.Cofinality.Cofinality

namespace Lemmatheca.SetTheory.ForcingChainConditions
open Set Cardinal Ordinal Order
universe u
noncomputable section
variable {ι β : Type u}

theorem countable_union_cardinality (C : ι → Set β) (hC : ∀ i, (C i).Countable) :
    #(⋃ i, C i) ≤ max ℵ₀ #ι := by
  classical
  by_cases hi : Nonempty ι
  · let : Nonempty ι := hi
    have hs : (⨆ i, #(C i)) ≤ ℵ₀ := ciSup_le fun i =>
      Cardinal.mk_le_aleph0_iff.mpr (hC i).to_subtype
    calc
      #(⋃ i, C i) ≤ #ι * ⨆ i, #(C i) := Cardinal.mk_iUnion_le _
      _ ≤ max ℵ₀ #ι * ℵ₀ := mul_le_mul' (le_max_right _ _) hs
      _ = max ℵ₀ #ι := Cardinal.mul_aleph0_eq (le_max_left _ _)
  · let : IsEmpty ι := not_nonempty_iff.mp hi
    simp

theorem range_in_union (f : ι → β) (C : ι → Set β) (hf : ∀ i, f i ∈ C i) :
    Set.range f ⊆ ⋃ i, C i := by
  rintro b ⟨i, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, hf i⟩

theorem countable_range_cardinality (f : ι → β) (C : ι → Set β)
    (hC : ∀ i, (C i).Countable) (hf : ∀ i, f i ∈ C i) :
    #(Set.range f) ≤ max ℵ₀ #ι := by
  exact (Cardinal.mk_le_mk_of_subset (range_in_union f C hf)).trans
    (countable_union_cardinality C hC)

theorem countable_union_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hι : #ι < κ)
    (C : ι → Set β) (hC : ∀ i, (C i).Countable) : #(⋃ i, C i) < κ := by
  exact (countable_union_cardinality C hC).trans_lt (max_lt hκ hι)

theorem countable_cover_omits {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hι : #ι < κ)
    (hβ : #β = κ) (f : ι → β) (C : ι → Set β)
    (hC : ∀ i, (C i).Countable) (hf : ∀ i, f i ∈ C i) :
    ∃ b : β, ∀ i, f i ≠ b := by
  classical
  have hsmall : #(⋃ i, C i) < #β := by
    rw [hβ]
    exact countable_union_lt hκ hι C hC
  obtain ⟨b, hb⟩ : ∃ b : β, b ∉ ⋃ i, C i := by
    by_contra hn
    push Not at hn
    have he : (⋃ i, C i) = Set.univ := Set.eq_univ_of_forall hn
    simp only [he, Cardinal.mk_univ, lt_self_iff_false] at hsmall
  refine ⟨b, ?_⟩
  intro i he
  apply hb
  rw [← he]
  exact Set.mem_iUnion.mpr ⟨i, hf i⟩

theorem countable_union_bounded {δ : Ordinal.{u}} (hδ : ℵ₀ < δ.cof)
    (hι : #ι < δ.cof) (C : ι → Set δ.ToType) (hC : ∀ i, (C i).Countable) :
    ∃ b : δ.ToType, ∀ x ∈ ⋃ i, C i, x < b := by
  classical
  have hsmall := countable_union_lt hδ hι C hC
  by_contra hn
  have hc : IsCofinal (⋃ i, C i) := by
    intro b
    by_contra hb
    apply hn
    refine ⟨b, ?_⟩
    intro x hx
    apply lt_of_not_ge
    intro hbx
    exact hb ⟨x, hx, hbx⟩
  have hcf := Order.cof_le hc
  rw [Ordinal.cof_toType] at hcf
  exact (not_lt_of_ge hcf) hsmall

end
end Lemmatheca.SetTheory.ForcingChainConditions
