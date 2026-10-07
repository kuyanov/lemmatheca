import Lemmatheca.SetTheory.InfiniteTrees

/-! The finite-word antichain and decreasing-natural-number counterexample. -/
noncomputable section

namespace Lemmatheca.Entry.InfiniteTrees

open Set
open Lemmatheca.SetTheory.InfiniteTrees

def binaryComb : Set (fullWordTree Bool) :=
  {w | ∃ n : ℕ, w.1 = List.replicate n true ++ [false]}

def binaryZeroPath : Set (fullWordTree Bool) :=
  {w | ∃ n : ℕ, w.1 = List.replicate n false}

private theorem word_comb_prefix {n m : ℕ}
    (h : (List.replicate n true ++ [false]).IsPrefix (List.replicate m true ++ [false])) :
    n = m := by
  have hl : n ≤ m := by simpa using h.length_le
  by_contra hn
  have hnm : n < m := lt_of_le_of_ne hl hn
  have he := h.getElem (i := n) (by simp)
  have hleft : (List.replicate n true ++ [false])[n] = false := by simp
  have hright : (List.replicate m true ++ [false])[n]'(by simp; omega) = true := by
    rw [List.getElem_append_left (by simpa using hnm)]
    simp
  rw [hleft, hright] at he
  contradiction

theorem binaryComb_antichain :
    binaryComb.Infinite ∧ IsAntichain (· ≤ ·) binaryComb := by
  let f : ℕ → fullWordTree Bool := fun n => ⟨List.replicate n true ++ [false], Set.mem_univ _⟩
  refine ⟨Set.infinite_of_injective_forall_mem (f := f) ?_ (fun n => ⟨n, rfl⟩), ?_⟩
  · intro n m he
    have hh := congrArg (fun w : fullWordTree Bool => w.1.length) he
    simpa [f, WordNode] using hh
  · rintro s ⟨n, hn⟩ t ⟨m, hm⟩ hne hst
    have h : n = m := word_comb_prefix (by
      change s.1.IsPrefix t.1 at hst
      rwa [hn, hm] at hst)
    apply hne
    exact Subtype.ext (hn.trans (h ▸ hm.symm))

theorem binaryZeroPath_cofinal :
    IsCofinalBranch (fullWordTree Bool) binaryZeroPath := by
  have he : binaryZeroPath = binaryBranches (fun _ => false) := by
    ext w
    simp [binaryZeroPath, binaryBranches, Lemmatheca.SetTheory.AlmostDisjoint.binaryPrefix,
      List.ofFn_const]
  rw [he]
  exact word_binaryBranch_cofinal _

def decreasingWords : Set (WordNode ℕ) := {w | w.Pairwise (· > ·)}

theorem decreasingWords_prefixClosed : PrefixClosed decreasingWords := by
  intro t ht s hs
  exact (show t.Pairwise (· > ·) from ht).sublist hs.sublist

def decreasingTree : Tree := wordTree decreasingWords decreasingWords_prefixClosed

/-- The displayed level-n witness (n-1,n-2,...,0), including [] at n=0. -/
def decreasingLevelWitness (n : ℕ) : List ℕ := (List.range n).reverse

theorem decreasingLevelWitness_spec (n : ℕ) :
    decreasingLevelWitness n ∈ decreasingWords ∧
      (decreasingLevelWitness n).length = n := by
  refine ⟨?_, by simp [decreasingLevelWitness]⟩
  exact List.pairwise_lt_range.reverse

theorem decreasing_start_bound (m : ℕ) (w : List ℕ)
    (hw : (m :: w) ∈ decreasingWords) : (m :: w).length ≤ m + 1 := by
  induction w generalizing m with
  | nil => simp
  | cons k w ih =>
      have hh := List.pairwise_cons.mp (show (m :: k :: w).Pairwise (· > ·) from hw)
      have hkm : k < m := hh.1 k (List.mem_cons_self ..)
      have hl := ih k hh.2
      simp only [List.length_cons] at hl ⊢
      omega

private theorem word_decreasing_height : treeHeight decreasingTree = Ordinal.omega 0 := by
  rw [Ordinal.omega_zero]
  apply le_antisymm
  · apply Ordinal.iSup_le
    intro t
    have he : nodeHeight decreasingTree t = t.1.length := wordTree_nodeHeight _ _ t
    rw [he]
    have hh : (t.1.length : Ordinal) + 1 < Ordinal.omega0 := by
      simpa using Ordinal.natCast_lt_omega0 (t.1.length + 1)
    exact hh.le
  · apply Ordinal.omega0_le.mpr
    intro n
    let t : decreasingTree := ⟨decreasingLevelWitness n, (decreasingLevelWitness_spec n).1⟩
    have he : nodeHeight decreasingTree t = (n : Ordinal) := by
      have hh : nodeHeight decreasingTree t = t.1.length := wordTree_nodeHeight _ _ t
      rw [hh, (decreasingLevelWitness_spec n).2]
    have hh := Ordinal.le_iSup (fun s : decreasingTree => nodeHeight decreasingTree s + 1) t
    rw [he] at hh
    exact (show (n : Ordinal) ≤ (n : Ordinal) + 1 from le_self_add).trans hh

private theorem word_decreasing_branch_bound (B : Set decreasingTree) (hB : IsBranch decreasingTree B) :
    ∃ N : ℕ, ∀ t ∈ B, t.1.length ≤ N := by
  classical
  by_cases hex : ∃ t ∈ B, t.1 ≠ []
  · obtain ⟨t, ht, hne⟩ := hex
    obtain ⟨m, w, he⟩ : ∃ m w, t.1 = m :: w := List.exists_cons_of_ne_nil hne
    have htl : t.1.length ≤ m + 1 := by
      rw [he]
      exact decreasing_start_bound m w (he ▸ t.2)
    refine ⟨m + 1, ?_⟩
    intro s hs
    rcases hB.1.total hs ht with h | h
    · exact h.length_le.trans htl
    · obtain ⟨r, hr⟩ := (show t.1.IsPrefix s.1 from h)
      have hsr : s.1 = m :: (w ++ r) := by rw [← hr, he]; rfl
      rw [hsr]
      exact decreasing_start_bound m (w ++ r) (hsr ▸ s.2)
  · refine ⟨0, ?_⟩
    intro t ht
    have he : t.1 = [] := by by_contra hn; exact hex ⟨t, ht, hn⟩
    rw [he]
    exact le_rfl

private theorem word_decreasing_branch_finite (B : Set decreasingTree)
    (hB : IsBranch decreasingTree B) : B.Finite := by
  obtain ⟨N, hN⟩ := word_decreasing_branch_bound B hB
  let f : B → Fin (N + 1) := fun t => ⟨t.1.1.length, Nat.lt_succ_of_le (hN t.1 t.2)⟩
  have hi : Function.Injective f := by
    intro s t he
    have hl : s.1.1.length = t.1.1.length := congrArg Fin.val he
    apply Subtype.ext
    apply Subtype.ext
    rcases hB.1.total s.2 t.2 with h | h
    · exact h.eq_of_length hl
    · exact (h.eq_of_length hl.symm).symm
  let := Finite.of_injective f hi
  exact Set.toFinite B

theorem decreasingTree_spec :
    (∃! r : decreasingTree, nodeHeight decreasingTree r = 0) ∧
      treeHeight decreasingTree = Ordinal.omega 0 ∧
      (∀ n : ℕ, (level decreasingTree n).Countable ∧ (level decreasingTree n).Nonempty) ∧
      (¬ ∃ B, IsCofinalBranch decreasingTree B) ∧
      ∀ B, IsBranch decreasingTree B → B.Finite := by
  refine ⟨?_, word_decreasing_height, ?_, ?_, word_decreasing_branch_finite⟩
  · let r : decreasingTree := ⟨[], by change ([] : List ℕ).Pairwise (· > ·); constructor⟩
    refine ⟨r, ?_, ?_⟩
    · exact wordTree_nodeHeight _ _ r
    · intro t ht
      have hh : nodeHeight decreasingTree t = t.1.length := wordTree_nodeHeight _ _ t
      have hl : t.1.length = 0 := by exact_mod_cast hh.symm.trans ht
      exact Subtype.ext (List.length_eq_zero_iff.mp hl)
  · intro n
    refine ⟨?_, ?_⟩
    · let : Countable decreasingTree := by
        change Countable {w : List ℕ // w ∈ decreasingWords}
        exact Subtype.val_injective.countable
      exact Set.to_countable _
    · exact ⟨⟨decreasingLevelWitness n, (decreasingLevelWitness_spec n).1⟩,
        (word_level_iff _ _ _ n).mpr (decreasingLevelWitness_spec n).2⟩
  · rintro ⟨B, hB⟩
    obtain ⟨N, hN⟩ := word_decreasing_branch_bound B hB.1
    obtain ⟨t, ht, hl⟩ := hB.2 (N + 1) (by
      rw [word_decreasing_height, Ordinal.omega_zero]
      simpa using Ordinal.natCast_lt_omega0 (N + 1))
    have he : t.1.length = N + 1 := (word_level_iff _ _ t (N + 1)).mp hl
    have hh := hN t ht
    omega

end Lemmatheca.Entry.InfiniteTrees
