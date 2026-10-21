import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-! Finite-support binary coding used to enumerate finite subsets. -/
namespace Lemmatheca.SetTheory

def FiniteSupportBinary := {s : ℕ → Bool // {j | s j = true}.Finite}

noncomputable def finiteSupportCode (s : FiniteSupportBinary) : ℕ :=
  ∑ j ∈ s.property.toFinset, 2 ^ j

private theorem binary_sum_range (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

private theorem binary_sum_bound (s : Finset ℕ) (n : ℕ) (hs : s ⊆ Finset.range n) :
    (∑ i ∈ s, 2 ^ i) < 2 ^ n := by
  have hle : (∑ i ∈ s, 2 ^ i) ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
    Finset.sum_le_sum_of_subset hs
  have := binary_sum_range n
  omega

private theorem binary_sum_injective (s t : Finset ℕ) (n : ℕ)
    (hs : s ⊆ Finset.range n) (ht : t ⊆ Finset.range n)
    (he : (∑ i ∈ s, 2 ^ i) = ∑ i ∈ t, 2 ^ i) : s = t := by
  classical
  induction n generalizing s t with
  | zero =>
    have : s = ∅ := Finset.subset_empty.mp (by simpa using hs)
    have : t = ∅ := Finset.subset_empty.mp (by simpa using ht)
    simp_all
  | succ n ih =>
    have hse : s.erase n ⊆ Finset.range n := by
      intro i hi
      have := hs (Finset.mem_of_mem_erase hi)
      simp only [Finset.mem_range] at this ⊢
      have := (Finset.mem_erase.mp hi).1
      omega
    have hte : t.erase n ⊆ Finset.range n := by
      intro i hi
      have := ht (Finset.mem_of_mem_erase hi)
      simp only [Finset.mem_range] at this ⊢
      have := (Finset.mem_erase.mp hi).1
      omega
    have hbs := binary_sum_bound (s.erase n) n hse
    have hbt := binary_sum_bound (t.erase n) n hte
    have split (u : Finset ℕ) :
        (∑ i ∈ u, 2 ^ i) = (∑ i ∈ u.erase n, 2 ^ i) + (if n ∈ u then 2 ^ n else 0) := by
      by_cases hn : n ∈ u
      · simpa [hn] using (Finset.sum_erase_add u (fun i => 2 ^ i) hn).symm
      · simp [hn]
    rw [split s, split t] at he
    have hm : n ∈ s ↔ n ∈ t := by
      by_cases hns : n ∈ s <;> by_cases hnt : n ∈ t <;>
        simp only [hns, hnt, ite_true, ite_false] at he ⊢ <;> omega
    have he' : (∑ i ∈ s.erase n, 2 ^ i) = ∑ i ∈ t.erase n, 2 ^ i := by
      simp only [hm] at he
      omega
    have herase := ih (s.erase n) (t.erase n) hse hte he'
    ext i
    by_cases hi : i = n
    · simpa [hi] using hm
    · have := Finset.ext_iff.mp herase i
      simpa [Finset.mem_erase, hi] using this

theorem finiteSupportCode_spec : Function.Injective finiteSupportCode ∧
    ∀ s : FiniteSupportBinary, s.val = (fun _ => false) → finiteSupportCode s = 0 := by
  classical
  constructor
  · intro s t h
    let a := s.property.toFinset
    let b := t.property.toFinset
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range (a ∪ b)
    have ha : a ⊆ Finset.range n := Finset.Subset.trans Finset.subset_union_left hn
    have hb : b ⊆ Finset.range n := Finset.Subset.trans Finset.subset_union_right hn
    have he : a = b := binary_sum_injective a b n ha hb h
    apply Subtype.ext
    funext j
    have hj := Finset.ext_iff.mp he j
    change (j ∈ s.property.toFinset ↔ j ∈ t.property.toFinset) at hj
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hj
    cases hs : s.val j <;> cases ht : t.val j <;> simp_all
  · intro s hs
    have he : s.property.toFinset = ∅ := by
      ext j
      simp [hs]
    simp [finiteSupportCode, he]

end Lemmatheca.SetTheory
