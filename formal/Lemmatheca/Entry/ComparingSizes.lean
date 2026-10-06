import Lemmatheca.SetTheory.Cardinality

namespace Lemmatheca.Entry.ComparingSizes

open Lemmatheca.SetTheory

/-- The concrete residue-class rearrangement of blocks of three naturals. -/
def bernsteinExample (n : ℕ) : ℕ := if n % 3 = 2 then n - 2 else n + 1

theorem bernstein_example_regions :
    (∀ k, bernsteinStage (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) k =
      {3 * k, 3 * k + 1}) ∧
    bernsteinRegion (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) =
      {n | n % 3 = 0 ∨ n % 3 = 1} := by
  have hstage : ∀ k, bernsteinStage (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) k =
      {3 * k, 3 * k + 1} := by
    intro k
    induction k with
    | zero =>
      ext n
      change (n ∉ Set.range (fun m : ℕ => m + 2)) ↔ n = 0 ∨ n = 1
      constructor
      · intro h
        by_contra hn
        apply h
        exact ⟨n - 2, by dsimp; omega⟩
      · rintro (rfl | rfl) ⟨m, hm⟩ <;> dsimp at hm <;> omega
    | succ k ih =>
      rw [bernsteinStage, ih]
      simp only [Set.image_pair]
      congr 1
  refine ⟨hstage, ?_⟩
  ext n
  simp only [bernsteinRegion, Set.mem_iUnion, hstage, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl | rfl⟩ <;> omega
  · intro h
    refine ⟨n / 3, ?_⟩
    omega

theorem bernstein_example_values :
    (∀ hg : Function.Injective (fun n : ℕ => n + 2),
      bernsteinMap (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) hg = bernsteinExample) ∧
    (List.range 6).map bernsteinExample = [1, 2, 0, 4, 5, 3] ∧
    Function.Bijective bernsteinExample ∧
    ¬ Function.Surjective (fun n : ℕ => n + 1) ∧
    ¬ Function.Surjective (fun n : ℕ => n + 2) := by
  have hregion := bernstein_example_regions.2
  have hmap : ∀ hg : Function.Injective (fun n : ℕ => n + 2),
      bernsteinMap (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) hg = bernsteinExample := by
    intro hg
    funext n
    obtain ⟨hon, hoff⟩ := bernstein_map_spec (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) hg
    by_cases hn : n % 3 = 2
    · have hc : n ∉ bernsteinRegion (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) := by
        rw [hregion]
        simp only [Set.mem_ofPred_eq]
        omega
      have hh := (hoff n hc).2
      simp only [bernsteinExample, hn, ite_true]
      omega
    · have hc : n ∈ bernsteinRegion (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) := by
        rw [hregion]
        simp only [Set.mem_ofPred_eq]
        omega
      simpa [bernsteinExample, hn] using hon n hc
  refine ⟨hmap, by decide, ?_, ?_, ?_⟩
  · have hf : Function.Injective (fun n : ℕ => n + 1) := by intro a b h; dsimp at h; omega
    have hg : Function.Injective (fun n : ℕ => n + 2) := by intro a b h; dsimp at h; omega
    rw [← hmap hg]
    exact bernstein_map_bijective _ _ hf hg
  · intro h
    obtain ⟨n, hn⟩ := h 0
    dsimp at hn
    omega
  · intro h
    obtain ⟨n, hn⟩ := h 0
    dsimp at hn
    omega

theorem positive_even_inverse_laws :
    (∀ n : ℕ, (n + 1) - 1 = n) ∧
    (∀ k : ℕ, 0 < k → k - 1 + 1 = k) ∧
    (∀ n : ℕ, (2 * n) / 2 = n) ∧
    (∀ k : ℕ, Even k → 2 * (k / 2) = k) := by
  refine ⟨(fun n => by omega), (fun k hk => by omega), (fun n => by omega), ?_⟩
  rintro k ⟨m, rfl⟩
  omega

theorem diagonal_subset_examples :
    diagonalSubset (fun n : ℕ => {n}) = ∅ ∧
    diagonalSubset (fun n : ℕ => Set.Iio n) = Set.univ ∧
    diagonalSubset (fun n : ℕ => Set.Iio (n + 1)) = ∅ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext n <;> simp [diagonalSubset]

/-- The finite part of the sample array, completed by zero outside the shown square. -/
def sampleBinaryList (row col : ℕ) : Bool :=
  match row, col with
  | 0, 2 | 1, 0 | 1, 1 | 2, 1 | 2, 2 | 3, 0 => true
  | _, _ => false

theorem sample_binary_diagonal :
    (List.range 4).map (fun n => sampleBinaryList n n) = [false, true, true, false] ∧
    (List.range 4).map (binaryDiagonal sampleBinaryList) = [true, false, false, true] := by
  decide

theorem decimal_half_example :
    decimalValue (fun n => if n = 0 then 5 else 0) = (1 / 2 : ℝ) ∧
    CanonicalDecimal (fun n => if n = 0 then 5 else 0) ∧
    decimalValue (fun n => if n = 0 then 4 else 9) = (1 / 2 : ℝ) ∧
    ¬ CanonicalDecimal (fun n => if n = 0 then 4 else 9) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := decimalValue_head (fun n => if n = 0 then 5 else 0)
    norm_num [decimalValue_const] at h
    exact h
  · rintro ⟨n, hn⟩
    have h := hn (n + 1) (by omega)
    norm_num at h
  · have h := decimalValue_head (fun n => if n = 0 then 4 else 9)
    norm_num [decimalValue_const] at h
    exact h
  · exact fun h => h ⟨1, fun n hn => by simp [show n ≠ 0 by omega]⟩

end Lemmatheca.Entry.ComparingSizes
