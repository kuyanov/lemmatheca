import Lemmatheca.SetTheory.Cardinality
import Lemmatheca.Entry.FiniteAndCountableSets

namespace Lemmatheca.Entry.ComparingSizes

open Lemmatheca.SetTheory

/-- The concrete residue-class rearrangement of blocks of three naturals. -/
def bernsteinExample (n : ℕ) : ℕ := if n % 3 = 2 then n - 2 else n + 1

theorem bernstein_example_regions :
    (∀ k, bernsteinStage (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) k =
      {3 * k, 3 * k + 1}) ∧
    bernsteinRegion (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) =
      {n | n % 3 = 0 ∨ n % 3 = 1} := by
  sorry

theorem bernstein_example_values :
    (∀ hg : Function.Injective (fun n : ℕ => n + 2),
      bernsteinMap (fun n : ℕ => n + 1) (fun n : ℕ => n + 2) hg = bernsteinExample) ∧
    (List.range 6).map bernsteinExample = [1, 2, 0, 4, 5, 3] ∧
    Function.Bijective bernsteinExample ∧
    ¬ Function.Surjective (fun n : ℕ => n + 1) ∧
    ¬ Function.Surjective (fun n : ℕ => n + 2) := by
  sorry

theorem positive_even_inverse_laws :
    (∀ n : ℕ, (n + 1) - 1 = n) ∧
    (∀ k : ℕ, 0 < k → k - 1 + 1 = k) ∧
    (∀ n : ℕ, (2 * n) / 2 = n) ∧
    (∀ k : ℕ, Even k → 2 * (k / 2) = k) := by
  sorry

theorem diagonal_subset_examples :
    diagonalSubset (fun n : ℕ => {n}) = ∅ ∧
    diagonalSubset (fun n : ℕ => Set.Iio n) = Set.univ ∧
    diagonalSubset (fun n : ℕ => Set.Iio (n + 1)) = ∅ := by
  sorry

/-- The finite part of the sample array, completed by zero outside the shown square. -/
def sampleBinaryList (row col : ℕ) : Bool :=
  match row, col with
  | 0, 2 | 1, 0 | 1, 1 | 2, 1 | 2, 2 | 3, 0 => true
  | _, _ => false

theorem sample_binary_diagonal :
    (List.range 4).map (fun n => sampleBinaryList n n) = [false, true, true, false] ∧
    (List.range 4).map (binaryDiagonal sampleBinaryList) = [true, false, false, true] := by
  sorry

theorem decimal_half_example :
    decimalValue (fun n => if n = 0 then 5 else 0) = (1 / 2 : ℝ) ∧
    CanonicalDecimal (fun n => if n = 0 then 5 else 0) ∧
    decimalValue (fun n => if n = 0 then 4 else 9) = (1 / 2 : ℝ) ∧
    ¬ CanonicalDecimal (fun n => if n = 0 then 4 else 9) := by
  sorry

end Lemmatheca.Entry.ComparingSizes
