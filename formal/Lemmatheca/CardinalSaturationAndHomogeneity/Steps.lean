import Lemmatheca.CardinalSaturationAndHomogeneity.Recursion

namespace Lemmatheca.ModelTheory.CardinalSaturation
open FirstOrder FirstOrder.Language PartialElementaryMaps Cardinal Ordinal
universe u v w w' z
noncomputable section
local instance cardinalStepsPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
variable {κ : Cardinal.{z}}

private theorem small_step_exists (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N)
    (p : Map L M N) (hp : Below κ p.dom) (a : M) :
    ∃ q : Map L M N, p ≤ q ∧ q.dom = insert a p.dom ∧
      ∃ b : N, q.range = insert b p.range := by
  obtain ⟨b, q, hd, hr, he, _⟩ := one_point_extension hκ hN p hp a
  exact ⟨q, he, hd, b, hr⟩

def stepAt (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N) (p : Map L M N) (a : M) : Map L M N :=
  if hp : Below κ p.dom then (small_step_exists hκ hN p hp a).choose else p

theorem stepAt_extends (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N) (p : Map L M N) (a : M) :
    p ≤ stepAt hκ hN p a := by
  unfold stepAt
  split_ifs with hp
  · exact (small_step_exists hκ hN p hp a).choose_spec.1
  · exact le_rfl

theorem stepAt_dom (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N) (p : Map L M N)
    (hp : Below κ p.dom) (a : M) : (stepAt hκ hN p a).dom = insert a p.dom := by
  unfold stepAt
  rw [dite_eq_left hp]
  exact (small_step_exists hκ hN p hp a).choose_spec.2.1

theorem stepAt_sets (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N) (p : Map L M N) (a : M) :
    (stepAt hκ hN p a).dom ⊆ insert a p.dom ∧
      ∃ b : N, (stepAt hκ hN p a).range ⊆ insert b p.range := by
  unfold stepAt
  split_ifs with hp
  · obtain ⟨he, hd, b, hr⟩ := (small_step_exists hκ hN p hp a).choose_spec
    exact ⟨le_of_eq hd, b, le_of_eq hr⟩
  · exact ⟨Set.subset_insert a _, Classical.choice ‹Nonempty N›, Set.subset_insert _ _⟩

omit [Nonempty M] [Nonempty N] in
 theorem two_point_difference (A B : Set M) (a b : M) (h : B ⊆ insert a (insert b A)) :
    #(B \ A : Set M) ≤ 2 := by
  have hs : B \ A ⊆ ({a, b} : Set M) := by
    intro x hx
    rcases h hx.1 with h | h
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
      · exact False.elim (hx.2 h)
  apply (Cardinal.mk_le_mk_of_subset hs).trans
  calc
    #({a, b} : Set M) ≤ #({b} : Set M) + 1 := Cardinal.mk_insert_le
    _ = 2 := by simp only [Cardinal.mk_singleton]; norm_num

def roundAt (hκ : ℵ₀ ≤ κ) (hM : IsSaturated κ L M) (hN : IsSaturated κ L N)
    (p : Map L M N) (a : M) (b : N) : Map L M N :=
  (stepAt hκ hM (stepAt hκ hN p a).symm b).symm

theorem roundAt_extends (hκ : ℵ₀ ≤ κ) (hM : IsSaturated κ L M) (hN : IsSaturated κ L N)
    (p : Map L M N) (a : M) (b : N) : p ≤ roundAt hκ hM hN p a b := by
  have h := Map.symm_mono (stepAt_extends hκ hM (stepAt hκ hN p a).symm b)
  rw [inverse_inverse] at h
  exact (stepAt_extends hκ hN p a).trans h

theorem roundAt_sets (hκ : ℵ₀ ≤ κ) (hM : IsSaturated κ L M) (hN : IsSaturated κ L N)
    (p : Map L M N) (a : M) (b : N) :
    (∃ c : M, (roundAt hκ hM hN p a b).dom ⊆ insert c (insert a p.dom)) ∧
      ∃ d : N, (roundAt hκ hM hN p a b).range ⊆ insert b (insert d p.range) := by
  let q := stepAt hκ hN p a
  let r := stepAt hκ hM q.symm b
  obtain ⟨hqd, d, hqr⟩ := stepAt_sets hκ hN p a
  obtain ⟨hrd, c, hrr⟩ := stepAt_sets hκ hM q.symm b
  constructor
  · refine ⟨c, ?_⟩
    change r.symm.dom ⊆ _
    change r.range ⊆ _
    rw [Map.symm_range] at hrr
    exact hrr.trans (Set.insert_subset_insert hqd)
  · refine ⟨d, ?_⟩
    change r.symm.range ⊆ _
    rw [Map.symm_range]
    exact hrd.trans (Set.insert_subset_insert hqr)

theorem roundAt_requests (hκ : ℵ₀ ≤ κ) (hM : IsSaturated κ L M) (hN : IsSaturated κ L N)
    (p : Map L M N) (hp : Below κ p.dom) (a : M) (b : N) :
    a ∈ (roundAt hκ hM hN p a b).dom ∧ b ∈ (roundAt hκ hM hN p a b).range := by
  let q := stepAt hκ hN p a
  have hqd : q.dom = insert a p.dom := stepAt_dom hκ hN p hp a
  have hqsmall : Below κ q.dom := hqd.symm ▸ below_insert hκ p.dom hp a
  have hqrsmall : Below κ q.symm.dom := (below_equiv q.rangeEquiv).mp hqsmall
  let r := stepAt hκ hM q.symm b
  have hrd : r.dom = insert b q.symm.dom := stepAt_dom hκ hM q.symm hqrsmall b
  have hqr : q ≤ r.symm := by
    have h := Map.symm_mono (stepAt_extends hκ hM q.symm b)
    rw [inverse_inverse] at h
    exact h
  constructor
  · exact Map.dom_mono hqr (hqd.symm ▸ Set.mem_insert a p.dom)
  · change b ∈ r.symm.range
    rw [Map.symm_range, hrd]
    exact Set.mem_insert _ _

end
end Lemmatheca.ModelTheory.CardinalSaturation
