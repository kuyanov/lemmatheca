import Mathlib.Data.Set.Countable
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Sqrt
import Mathlib.Basic.Denumerable
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Lemmatheca.SetTheory.Cardinality

/-!
# Explicit lists and the diagonal enumeration

General finiteness and countability results are bound directly to mathlib.
These constructions retain the particular witnesses used in the human entry.
`Nat.pair` uses square shells, so it cannot represent the entry's diagonals.
The proofs preserve the explicit first-occurrence and diagonal witnesses.
-/

namespace Lemmatheca.SetTheory

universe u v

variable {α : Type u} {β : Type v}

/-- The least index at which a value of a surjective list occurs. -/
noncomputable def firstOccurrence (f : ℕ → α) (hf : Function.Surjective f) (a : α) : ℕ := by
  classical
  exact Nat.find (hf a)

theorem firstOccurrence_spec (f : ℕ → α) (hf : Function.Surjective f) :
    Function.Injective (firstOccurrence f hf) ∧
      ∀ a, f (firstOccurrence f hf a) = a ∧
        ∀ n < firstOccurrence f hf a, f n ≠ a := by
  classical
  have hval (a : α) : f (firstOccurrence f hf a) = a := Nat.find_spec (hf a)
  refine ⟨?_, fun a => ⟨hval a, ?_⟩⟩
  · intro a b hab
    rw [← hval a, ← hval b, hab]
  · intro n hn
    exact Nat.find_min (hf a) hn

/-- Indices that are the first occurrence of their value. -/
def firstIndices (f : ℕ → α) : Set ℕ := {n | ∀ m < n, f m ≠ f n}

/-- Increasing enumeration of first-occurrence indices; only the infinite case is used. -/
noncomputable def dedupIndex (f : ℕ → α) (n : ℕ) : ℕ :=
  Nat.nth (· ∈ firstIndices f) n

/-- The list obtained by retaining first occurrences, in their original order. -/
noncomputable def dedup (f : ℕ → α) (n : ℕ) : α := f (dedupIndex f n)

private theorem firstOccurrence_of_firstIndex (f : ℕ → α) (hf : Function.Surjective f)
    {n : ℕ} (hn : n ∈ firstIndices f) : firstOccurrence f hf (f n) = n := by
  classical
  exact (Nat.find_eq_iff (hf (f n))).mpr ⟨rfl, hn⟩

private theorem firstIndices_eq_range (f : ℕ → α) (hf : Function.Surjective f) :
    firstIndices f = Set.range (firstOccurrence f hf) := by
  ext n
  constructor
  · intro hn
    exact ⟨f n, firstOccurrence_of_firstIndex f hf hn⟩
  · rintro ⟨a, rfl⟩ m hm heq
    exact ((firstOccurrence_spec f hf).2 a).2 m hm
      (heq.trans ((firstOccurrence_spec f hf).2 a).1)

private theorem firstIndices_infinite [Infinite α] (f : ℕ → α)
    (hf : Function.Surjective f) : (firstIndices f).Infinite := by
  rw [firstIndices_eq_range f hf]
  exact Set.infinite_range_of_injective (firstOccurrence_spec f hf).1

theorem dedup_spec [Infinite α] (f : ℕ → α) (hf : Function.Surjective f) :
    StrictMono (dedupIndex f) ∧ Set.range (dedupIndex f) = firstIndices f ∧
      Function.Bijective (dedup f) ∧
        ∀ n, firstOccurrence f hf (dedup f n) = dedupIndex f n := by
  have hi : (Set.ofPred (· ∈ firstIndices f)).Infinite := firstIndices_infinite f hf
  have hmono : StrictMono (dedupIndex f) := Nat.nth_strictMono hi
  have hrange : Set.range (dedupIndex f) = firstIndices f := Nat.range_nth_of_infinite hi
  have hfirst (n : ℕ) : firstOccurrence f hf (dedup f n) = dedupIndex f n :=
    firstOccurrence_of_firstIndex f hf (hrange ▸ Set.mem_range_self n)
  refine ⟨hmono, hrange, ⟨?_, ?_⟩, hfirst⟩
  · intro m n h
    apply hmono.injective
    rw [← hfirst m, ← hfirst n, h]
  · intro a
    have ha : firstOccurrence f hf a ∈ firstIndices f := by
      rw [firstIndices_eq_range f hf]
      exact Set.mem_range_self a
    obtain ⟨n, hn⟩ := hrange.symm ▸ ha
    refine ⟨n, ?_⟩
    change f (dedupIndex f n) = a
    rw [hn]
    exact ((firstOccurrence_spec f hf).2 a).1

/-- Repeat a nonempty finite enumeration periodically. -/
def periodicList {r : ℕ} (hr : 0 < r) (e : Fin r ≃ α) (n : ℕ) : α :=
  e ⟨n % r, Nat.mod_lt n hr⟩

theorem periodicList_surjective {r : ℕ} (hr : 0 < r) (e : Fin r ≃ α) :
    Function.Surjective (periodicList hr e) := by
  intro a
  refine ⟨(e.symm a).val, ?_⟩
  simp only [periodicList, Nat.mod_eq_of_lt (e.symm a).isLt]
  exact e.apply_symm_apply a

/-- Number of pairs on diagonals whose sum is less than s. -/
def triangular (s : ℕ) : ℕ := s * (s + 1) / 2

private theorem twice_triangular (s : ℕ) : 2 * triangular s = s * (s + 1) := by
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self s)

theorem triangular_recurrence :
    triangular 0 = 0 ∧ ∀ s, triangular (s + 1) = triangular s + s + 1 := by
  refine ⟨rfl, fun s => ?_⟩
  have h₀ := twice_triangular s
  have h₁ := twice_triangular (s + 1)
  nlinarith

private theorem triangular_strictMono : StrictMono triangular := by
  apply strictMono_nat_of_lt_succ
  intro s
  rw [triangular_recurrence.2]
  omega

theorem triangular_intervals (n : ℕ) :
    ∃! s, triangular s ≤ n ∧ n < triangular (s + 1) := by
  have hex : ∃ s, n < triangular (s + 1) := by
    refine ⟨n, ?_⟩
    have h := twice_triangular (n + 1)
    nlinarith
  let s := Nat.find hex
  have hu : n < triangular (s + 1) := Nat.find_spec hex
  have hl : triangular s ≤ n := by
    cases hs : s with
    | zero => simp [triangular]
    | succ k =>
      have h := Nat.find_min hex (show k < Nat.find hex by omega)
      simpa [hs] using Nat.le_of_not_gt h
  refine ⟨s, ⟨hl, hu⟩, ?_⟩
  intro t ht
  apply le_antisymm
  · by_contra h
    have hst : s + 1 ≤ t := by omega
    have := triangular_strictMono.monotone hst
    omega
  · by_contra h
    have hts : t + 1 ≤ s := by omega
    have := triangular_strictMono.monotone hts
    omega

/-- Position of (a,b), increasing coordinate sum and then first coordinate. -/
def cantorPair (a b : ℕ) : ℕ := triangular (a + b) + a

/-- Arithmetic inverse of the entry's diagonal pair code. -/
def cantorUnpair (n : ℕ) : ℕ × ℕ :=
  let s := (Nat.sqrt (8 * n + 1) - 1) / 2
  let a := n - triangular s
  (a, s - a)

/-- The square-root formula identifies the unique triangular interval. -/
private theorem diagonalLevel_eq {n s : ℕ}
    (hs : triangular s ≤ n ∧ n < triangular (s + 1)) :
    (Nat.sqrt (8 * n + 1) - 1) / 2 = s := by
  have h₀ := twice_triangular s
  have h₁ := twice_triangular (s + 1)
  have hl : 2 * s + 1 ≤ Nat.sqrt (8 * n + 1) := by
    apply Nat.le_sqrt.mpr
    nlinarith [hs.1]
  have hu : Nat.sqrt (8 * n + 1) < 2 * s + 3 := by
    apply Nat.sqrt_lt.mpr
    nlinarith [hs.2]
  omega

private theorem cantorUnpair_of_interval {n s : ℕ}
    (hs : triangular s ≤ n ∧ n < triangular (s + 1)) :
    cantorUnpair n = (n - triangular s, s - (n - triangular s)) := by
  simp only [cantorUnpair, diagonalLevel_eq hs]

theorem cantor_inverse_laws :
    Function.LeftInverse cantorUnpair (Function.uncurry cantorPair) ∧
      Function.RightInverse cantorUnpair (Function.uncurry cantorPair) := by
  constructor
  · rintro ⟨a, b⟩
    have hs : triangular (a + b) ≤ cantorPair a b ∧
        cantorPair a b < triangular (a + b + 1) := by
      rw [triangular_recurrence.2]
      dsimp [cantorPair]
      omega
    rw [Function.uncurry_apply_pair, cantorUnpair_of_interval hs]
    simp [cantorPair]
  · intro n
    obtain ⟨s, hs, _⟩ := triangular_intervals n
    rw [cantorUnpair_of_interval hs]
    have ha : n - triangular s ≤ s := by
      rw [triangular_recurrence.2] at hs
      omega
    simp only [Function.uncurry_apply_pair, cantorPair, Nat.add_sub_of_le ha]
    omega

/-- Enumerate a product using the entry's diagonal enumeration. -/
def productEnumeration (e : ℕ ≃ α) (f : ℕ ≃ β) (n : ℕ) : α × β :=
  (e (cantorUnpair n).1, f (cantorUnpair n).2)

theorem productEnumeration_bijective (e : ℕ ≃ α) (f : ℕ ≃ β) :
    Function.Bijective (productEnumeration e f) := by
  have hδ : Function.Bijective cantorUnpair :=
    ⟨cantor_inverse_laws.2.injective, cantor_inverse_laws.1.surjective⟩
  exact (e.prodCongr f).bijective.comp hδ

/-- Encode a finite subset using powers of two at its elements' natural-number codes. -/
def finiteSubsetCode (c : α → ℕ) (s : Finset α) : ℕ :=
  ∑ a ∈ s, 2 ^ c a

/-- Distinct finite subsets have distinct codes when the element code is injective. -/
theorem finiteSubsetCode_injective (c : α → ℕ) (hc : Function.Injective c) :
    Function.Injective (finiteSubsetCode c) := by
  classical
  let binary (s : Finset ℕ) : FiniteSupportBinary :=
    ⟨fun n => decide (n ∈ s), by simp⟩
  have hcode (s : Finset α) :
      finiteSupportCode (binary (s.image c)) = finiteSubsetCode c s := by
    have hs : (binary (s.image c)).property.toFinset = s.image c := by
      ext n
      simp [binary]
    rw [finiteSupportCode, hs, Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact hc hab
  intro s t h
  apply Finset.image_injective hc
  have he : binary (s.image c) = binary (t.image c) :=
    finiteSupportCode_spec.1 ((hcode s).trans (h.trans (hcode t).symm))
  ext n
  have hn := congrArg (fun b : FiniteSupportBinary => b.val n) he
  simpa [binary] using hn

end Lemmatheca.SetTheory
