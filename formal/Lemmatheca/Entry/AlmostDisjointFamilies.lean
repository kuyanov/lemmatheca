import Lemmatheca.SetTheory.AlmostDisjoint

/-! Particular prefix and finite maximal-family examples. -/

namespace Lemmatheca.Entry.AlmostDisjointFamilies

open Set Lemmatheca.SetTheory.AlmostDisjoint

private theorem zero_prefix_code (n : ℕ) :
    Lemmatheca.SetTheory.binaryWordCode (binaryPrefix (fun _ => false) n) = 2 ^ n := by
  have hf : ∀ m : ℕ, (List.replicate m false).foldr
      (fun b acc => b.toNat + 2 * acc) 0 = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, ih]
  simp [binaryPrefix, List.ofFn_const, Lemmatheca.SetTheory.binaryWordCode, hf]

theorem prefix_examples :
    prefixCodes (fun _ => false) = Set.range (fun n : ℕ => 2 ^ n) ∧
    prefixCodes (fun _ => false) ∩ prefixCodes (fun _ => true) = {1} ∧
    prefixCodes (fun _ => false) ∩ prefixCodes (fun n => n == 1) = {1, 2} := by
  have hzero : prefixCodes (fun _ => false) = range (fun n : ℕ => 2 ^ n) := by
    unfold prefixCodes
    congr 1
    funext n
    exact zero_prefix_code n
  have hfirst := (prefixCodes_intersection (fun _ => false) (fun _ => true) 0
    (by simp) (by decide)).1
  have hsecond := (prefixCodes_intersection (fun _ => false) (fun n => n == 1) 1
    (by
      intro i hi
      have h : i = 0 := Nat.lt_one_iff.mp hi
      simp [h]) (by decide)).1
  refine ⟨hzero, ?_, ?_⟩
  · rw [hfirst]
    ext v
    simp [show (Iic 0 : Set ℕ) = {0} by ext n; simp, zero_prefix_code]
  · rw [hsecond]
    have hi : (Iic 1 : Set ℕ) = {0, 1} := by ext n; simp; omega
    rw [hi]
    simp [zero_prefix_code, Set.image_singleton]

theorem finite_maximal_examples :
    let E : Set ℕ := {n | n % 2 = 0}
    let O : Set ℕ := {n | n % 2 = 1}
    E.Infinite ∧ O.Infinite ∧ E ∩ O = ∅ ∧
    IsMaximalAlmostDisjoint {Set.univ} ∧ IsMaximalAlmostDisjoint {E, O} ∧
    ¬ ({Set.univ} : Set (Set ℕ)) ⊆ {E, O} ∧
    ¬ ({E, O} : Set (Set ℕ)) ⊆ {Set.univ} := by
  classical
  dsimp
  let E : Set ℕ := {n | n % 2 = 0}
  let O : Set ℕ := {n | n % 2 = 1}
  have hE : E.Infinite := Lemmatheca.SetTheory.FiniteErrors.parity_partition.1
  have hO : O.Infinite := Lemmatheca.SetTheory.FiniteErrors.parity_partition.2.1
  have hEO : E ∩ O = ∅ := Lemmatheca.SetTheory.FiniteErrors.parity_partition.2.2.1
  have hEO' : E ∪ O = univ := Lemmatheca.SetTheory.FiniteErrors.parity_partition.2.2.2
  have ha : IsAlmostDisjoint {E, O} := by
    constructor
    · intro S hS
      simp only [mem_insert_iff, mem_singleton_iff] at hS
      rcases hS with rfl | rfl
      · exact hE
      · exact hO
    · intro S hS T hT hn
      simp only [mem_insert_iff, mem_singleton_iff] at hS hT
      rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
      · exact (hn rfl).elim
      · rw [hEO]; exact finite_empty
      · rw [inter_comm, hEO]; exact finite_empty
      · exact (hn rfl).elim
  have hmax : IsMaximalAlmostDisjoint {E, O} := by
    apply (maximal_iff_infinite_intersection _ ha).mpr
    intro B hB
    by_contra hn
    have he : (E ∩ B).Finite := by
      by_contra h; exact hn ⟨E, by simp, h⟩
    have ho : (O ∩ B).Finite := by
      by_contra h; exact hn ⟨O, by simp, h⟩
    have hu : E ∩ B ∪ O ∩ B = B := by rw [← union_inter_distrib_right, hEO', univ_inter]
    exact hB (hu ▸ he.union ho)
  have hsingle : IsMaximalAlmostDisjoint {univ} := by
    have ha' : IsAlmostDisjoint {univ} := by
      constructor
      · intro S hS; simpa only [mem_singleton_iff.mp hS] using (infinite_univ : (univ : Set ℕ).Infinite)
      · intro S hS T hT hn
        exact (hn ((mem_singleton_iff.mp hS).trans (mem_singleton_iff.mp hT).symm)).elim
    apply (maximal_iff_infinite_intersection _ ha').mpr
    intro B hB
    exact ⟨univ, by simp, by simpa using hB⟩
  have hUE : (univ : Set ℕ) ≠ E := by
    intro h
    have : 1 ∈ E := h ▸ mem_univ 1
    norm_num [E] at this
  have hUO : (univ : Set ℕ) ≠ O := by
    intro h
    have : 0 ∈ O := h ▸ mem_univ 0
    norm_num [O] at this
  refine ⟨hE, hO, hEO, hsingle, hmax, ?_, ?_⟩
  · intro h
    have := h (mem_singleton univ)
    simp only [mem_insert_iff, mem_singleton_iff] at this
    exact this.elim hUE hUO
  · intro h
    exact hUE (mem_singleton_iff.mp (h (by simp : E ∈ ({E, O} : Set (Set ℕ))))).symm

end Lemmatheca.Entry.AlmostDisjointFamilies
