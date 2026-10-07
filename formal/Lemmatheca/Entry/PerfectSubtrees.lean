import Lemmatheca.SetTheory.PerfectSubtrees

/-! Binary-word examples illustrating perfect kernels and added prefix-tree paths. -/

noncomputable section

namespace Lemmatheca.Entry.PerfectSubtrees

open Set Cardinal Lemmatheca.SetTheory.PerfectSubtrees

def binaryTree : Set (List ℕ) := {s | ∀ a ∈ s, a = 0 ∨ a = 1}

def zeroTree : Set (List ℕ) := {s | ∀ a ∈ s, a = 0}

def zeroPath : ℕ → ℕ := fun _ => 0

private theorem append_bits_incompatible (s : List ℕ) :
    Incompatible (s ++ [0]) (s ++ [1]) := by
  constructor
  · intro h
    have he := h.eq_of_length (by simp)
    simp at he
  · intro h
    have he := h.eq_of_length (by simp)
    simp at he

private theorem prefix_value_mem (x : ℕ → ℕ) (n : ℕ) :
    x n ∈ natPrefix x (n + 1) := by
  exact List.mem_ofFn.mpr ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩

private theorem zero_prefix (n : ℕ) : natPrefix zeroPath n = List.replicate n 0 := by
  simp [natPrefix, zeroPath]

theorem binaryTree_spec :
    IsPerfect binaryTree ∧ body binaryTree = {x | ∀ n, x n = 0 ∨ x n = 1} := by
  have htree : IsSequenceTree binaryTree := by
    intro s hs t ht a ha
    exact hs a (ht.sublist.subset ha)
  constructor
  · refine ⟨htree, ?_⟩
    intro s hs
    have hchild (b : ℕ) (hb : b = 0 ∨ b = 1) : s ++ [b] ∈ binaryTree := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hs a ha
      · simpa using (List.mem_singleton.mp ha) ▸ hb
    exact ⟨s ++ [0], hchild 0 (Or.inl rfl), s ++ [1], hchild 1 (Or.inr rfl),
      s.prefix_append [0], s.prefix_append [1], append_bits_incompatible s⟩
  · ext x
    constructor
    · intro hx n
      exact hx (n + 1) (x n) (prefix_value_mem x n)
    · intro hx n a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hx i

theorem zeroTree_spec :
    IsSequenceTree zeroTree ∧ body zeroTree = {zeroPath} ∧ ¬IsPerfect zeroTree := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs t ht a ha
    exact hs a (ht.sublist.subset ha)
  · ext x
    constructor
    · intro hx
      apply Set.mem_singleton_iff.mpr
      funext n
      exact hx (n + 1) (x n) (prefix_value_mem x n)
    · rintro rfl n
      simp [zeroTree, zero_prefix]
  · intro hp
    obtain ⟨u, hu, v, hv, _, _, huv⟩ := hp.2 [] (by simp [zeroTree])
    have hu' : Extends u zeroPath := by
      rw [Extends, zero_prefix]
      exact (List.eq_replicate_iff.mpr ⟨rfl, hu⟩).symm
    have hv' : Extends v zeroPath := by
      rw [Extends, zero_prefix]
      exact (List.eq_replicate_iff.mpr ⟨rfl, hv⟩).symm
    exact (extends_comparable hu' hv').elim huv.1 huv.2

def oneTree : Set (List ℕ) := {s | s ∈ binaryTree ∧ s.count 1 ≤ 1}

def oneAt (n : ℕ) : ℕ → ℕ := fun m => if m = n then 1 else 0

private theorem count_one_unique {s : List ℕ} (hc : s.count 1 ≤ 1)
    {i j : ℕ} (hi : i < s.length) (hj : j < s.length)
    (hiv : s[i] = 1) (hjv : s[j] = 1) : i = j := by
  induction s generalizing i j with
  | nil => simp at hi
  | cons a s ih =>
    have htail : s.count 1 ≤ 1 := (List.count_tail_le (l := a :: s)).trans hc
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have ha : a = 1 := by simpa using hiv
        have hj' : j < s.length := by simpa using hj
        have hm : 1 ∈ s := hjv ▸ List.getElem_mem hj'
        have hp := List.count_pos_iff.mpr hm
        simp [ha] at hc
        omega
    | succ i =>
      cases j with
      | zero =>
        have ha : a = 1 := by simpa using hjv
        have hi' : i < s.length := by simpa using hi
        have hm : 1 ∈ s := hiv ▸ List.getElem_mem hi'
        have hp := List.count_pos_iff.mpr hm
        simp [ha] at hc
        omega
      | succ j =>
        exact congrArg Nat.succ (ih htail (by simpa using hi) (by simpa using hj)
          (by simpa using hiv) (by simpa using hjv))

private theorem natPrefix_succ (x : ℕ → ℕ) (n : ℕ) :
    natPrefix x (n + 1) = natPrefix x n ++ [x n] := by
  simpa [natPrefix] using List.ofFn_succ' (fun i : Fin (n + 1) => x i)

private theorem oneAt_prefix_count (n k : ℕ) : (natPrefix (oneAt n) k).count 1 ≤ 1 := by
  induction k with
  | zero => simp [natPrefix]
  | succ k ih =>
    rw [natPrefix_succ]
    by_cases hk : k = n
    · have hz : (natPrefix (oneAt n) k).count 1 = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
        have hin : (i : ℕ) ≠ n := by omega
        simp [oneAt, hin] at hi
      rw [List.count_append, hz]
      simp [oneAt, hk]
    · simpa [oneAt, hk] using ih

private theorem oneAt_binary (n k : ℕ) : oneAt n k = 0 ∨ oneAt n k = 1 := by
  by_cases hk : k = n <;> simp [oneAt, hk]

theorem oneTree_paths :
    IsSequenceTree oneTree ∧ body oneTree = insert zeroPath (Set.range oneAt) := by
  have htree : IsSequenceTree oneTree := by
    intro s hs t ht
    exact ⟨binaryTree_spec.1.1 hs.1 ht, (ht.count_le 1).trans hs.2⟩
  constructor
  · exact htree
  · ext x
    constructor
    · intro hx
      have hb : ∀ n, x n = 0 ∨ x n = 1 := by
        have hx' : x ∈ body binaryTree := fun n => (hx n).1
        simpa only [binaryTree_spec.2, Set.mem_ofPred_eq] using hx'
      by_cases he : ∃ n, x n = 1
      · obtain ⟨n, hn⟩ := he
        apply Set.mem_insert_of_mem
        refine ⟨n, ?_⟩
        funext m
        by_cases hm : m = n
        · simp [oneAt, hm, hn]
        · have hmn : x m ≠ 1 := by
            intro h1
            have hsame := count_one_unique (hx (max m n + 1)).2
              (i := m) (j := n) (by simp) (by simp)
              (by simpa using h1) (by simpa using hn)
            exact hm hsame
          have hz := (hb m).resolve_right hmn
          simp [oneAt, hm, hz]
      · apply Set.mem_insert_iff.mpr
        left
        funext n
        exact (hb n).resolve_right (fun h => he ⟨n, h⟩)
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | ⟨n, rfl⟩
      · intro k
        simp [oneTree, binaryTree, zero_prefix, List.count_replicate]
      · intro k
        refine ⟨?_, oneAt_prefix_count n k⟩
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact oneAt_binary n i

theorem oneTree_countable_infinite :
    (body oneTree).Countable ∧ (body oneTree).Infinite ∧ kernel oneTree = ∅ ∧
      ¬∃ P : Set (List ℕ), IsSubtree P oneTree ∧ IsPerfect P ∧ P.Nonempty := by
  have hc : (body oneTree).Countable := by
    rw [oneTree_paths.2]
    exact (Set.countable_range oneAt).insert zeroPath
  have hi : Function.Injective oneAt := by
    intro n m h
    by_contra hnm
    have he := congrFun h n
    simp [oneAt, hnm] at he
  have hinf : (body oneTree).Infinite := by
    apply (Set.infinite_range_of_injective hi).mono
    rw [oneTree_paths.2]
    exact Set.subset_insert _ _
  exact ⟨hc, hinf, (kernel_empty_iff oneTree_paths.1).mpr hc,
    fun h => (uncountable_iff_perfect_subtree oneTree_paths.1).mpr h hc⟩

theorem oneTree_splitting_zero_path :
    (∀ n, natPrefix zeroPath n ∈ oneTree) ∧
      ∀ n, natPrefix zeroPath n ++ [0] ∈ oneTree ∧
        natPrefix zeroPath n ++ [1] ∈ oneTree ∧
        Incompatible (natPrefix zeroPath n ++ [0]) (natPrefix zeroPath n ++ [1]) := by
  constructor
  · intro n
    simp [oneTree, binaryTree, zero_prefix, List.count_replicate]
  · intro n
    refine ⟨?_, ?_, append_bits_incompatible _⟩
    · constructor
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · have hz : a = 0 := List.eq_of_mem_replicate (zero_prefix n ▸ ha)
          exact Or.inl hz
        · exact Or.inl (List.mem_singleton.mp ha)
      · simp [zero_prefix, List.count_replicate]
    · constructor
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · have hz : a = 0 := List.eq_of_mem_replicate (zero_prefix n ▸ ha)
          exact Or.inl hz
        · exact Or.inr (List.mem_singleton.mp ha)
      · simp [zero_prefix, List.count_replicate]

def eventuallyZero : Set (ℕ → ℕ) :=
  {x | (∀ n, x n = 0 ∨ x n = 1) ∧ ∃ N, ∀ n, N ≤ n → x n = 0}

private def zeroExtension (s : List ℕ) : ℕ → ℕ := fun n => s.getD n 0

private theorem zeroExtension_prefix (s : List ℕ) :
    natPrefix (zeroExtension s) s.length = s := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [natPrefix_get _ _ _ hj]
    exact List.getD_eq_getElem s 0 hj

private theorem eventuallyZero_zeroExtension {x : ℕ → ℕ} (hx : x ∈ eventuallyZero) :
    ∃ s, zeroExtension s = x := by
  obtain ⟨N, hN⟩ := hx.2
  refine ⟨natPrefix x N, ?_⟩
  funext n
  by_cases hn : n < N
  · change (natPrefix x N).getD n 0 = x n
    rw [List.getD_eq_getElem (natPrefix x N) 0 (by simpa using hn)]
    exact natPrefix_get x N n hn
  · change (natPrefix x N).getD n 0 = x n
    rw [List.getD_eq_default (natPrefix x N) 0 (by simpa using Nat.le_of_not_gt hn)]
    exact (hN n (Nat.le_of_not_gt hn)).symm

theorem eventuallyZero_countable : eventuallyZero.Countable := by
  exact (Set.countable_range zeroExtension).mono (fun _ hx => eventuallyZero_zeroExtension hx)

theorem eventuallyZero_prefixTree : prefixTree eventuallyZero = binaryTree := by
  ext s
  constructor
  · rintro ⟨x, hx, n, rfl⟩ a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hx.1 i
  · intro hs
    refine ⟨zeroExtension s, ⟨?_, s.length, ?_⟩, s.length, zeroExtension_prefix s⟩
    · intro n
      by_cases hn : n < s.length
      · change s.getD n 0 = 0 ∨ s.getD n 0 = 1
        rw [List.getD_eq_getElem s 0 hn]
        exact hs _ (List.getElem_mem hn)
      · change s.getD n 0 = 0 ∨ s.getD n 0 = 1
        rw [List.getD_eq_default s 0 (Nat.le_of_not_gt hn)]
        exact Or.inl rfl
    · intro n hn
      exact List.getD_eq_default s 0 hn

theorem eventuallyZero_added_paths :
    (fun _ : ℕ => 1) ∈ body (prefixTree eventuallyZero) ∧
      (fun _ : ℕ => 1) ∉ eventuallyZero ∧
      Cardinal.mk (body (prefixTree eventuallyZero)) = Cardinal.continuum := by
  rw [eventuallyZero_prefixTree]
  refine ⟨?_, ?_, ?_⟩
  · rw [binaryTree_spec.2]
    exact fun _ => Or.inr rfl
  · rintro ⟨_, N, hN⟩
    have he := hN N (le_refl N)
    simp at he
  · obtain ⟨f, hf⟩ := perfect_cone_injection binaryTree_spec.1
      (r := []) (by simp [binaryTree])
    have hl : Cardinal.continuum ≤ Cardinal.mk (cone binaryTree []) := by
      simpa only [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat,
        Cardinal.lift_id, Cardinal.lift_aleph0, Cardinal.two_power_aleph0]
        using Cardinal.mk_le_of_injective hf
    have hm : Cardinal.mk (cone binaryTree []) ≤ Cardinal.mk (body binaryTree) := by
      apply Cardinal.mk_le_of_injective
        (f := fun x : cone binaryTree [] => (⟨x.val, x.property.1⟩ : body binaryTree))
      intro x y h
      exact Subtype.ext (congrArg (fun z : body binaryTree => z.val) h)
    exact (body_cardinality_le binaryTree).antisymm (hl.trans hm)

end Lemmatheca.Entry.PerfectSubtrees
