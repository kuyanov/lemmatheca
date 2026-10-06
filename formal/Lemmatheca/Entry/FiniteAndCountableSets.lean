import Lemmatheca.SetTheory.Basic
import Lemmatheca.SetTheory.Countability

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.FiniteAndCountableSets
open Lemmatheca.SetTheory

open Lemmatheca.SetTheory

/-- The displayed enumeration of {2,5,8}. -/
def threeElementEnumeration (i : Fin 3) : ℕ :=
  if i = 0 then 2 else if i = 1 then 5 else 8

theorem three_element_enumeration :
    Set.BijOn threeElementEnumeration Set.univ ({2, 5, 8} : Set ℕ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    fin_cases i <;> simp [threeElementEnumeration]
  · intro i _ j _ hij
    fin_cases i <;> fin_cases j <;> simp_all [threeElementEnumeration]
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨0, Set.mem_univ _, rfl⟩
    · exact ⟨1, Set.mem_univ _, rfl⟩
    · exact ⟨2, Set.mem_univ _, rfl⟩

theorem predecessor_example :
    Function.Surjective Nat.pred ∧ ¬ Function.Injective Nat.pred ∧
      Nat.pred 0 = 0 ∧ Nat.pred 1 = 0 ∧ ∀ n, Nat.pred (n + 1) = n := by
  refine ⟨fun n => ⟨n + 1, rfl⟩, ?_, rfl, rfl, fun _ => rfl⟩
  intro h
  have := h (show Nat.pred 0 = Nat.pred 1 from rfl)
  omega

theorem even_naturals_enumeration :
    Function.Injective (fun n : ℕ => 2 * n) ∧
      Set.range (fun n : ℕ => 2 * n) = Lemmatheca.SetTheory.evenNaturals ∧
        1 ∉ Lemmatheca.SetTheory.evenNaturals := by
  refine ⟨fun a b h => by change 2 * a = 2 * b at h; omega, ?_, ?_⟩
  · ext n
    constructor
    · rintro ⟨k, rfl⟩
      change Even (2 * k)
      exact ⟨k, by omega⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by change 2 * k = n; omega⟩
  · simp [Lemmatheca.SetTheory.evenNaturals, Nat.even_iff]

theorem repeated_naturals_list :
    Function.Surjective (fun n : ℕ => n / 2) ∧
      ¬ Function.Injective (fun n : ℕ => n / 2) ∧
        (∀ n, (2 * n) / 2 = n ∧ (2 * n + 1) / 2 = n) ∧
          (∀ n, dedupIndex (fun k : ℕ => k / 2) n = 2 * n) ∧
            dedup (fun n : ℕ => n / 2) = id := by
  let f : ℕ → ℕ := fun n => n / 2
  have hsurj : Function.Surjective f := fun n => ⟨2 * n, by dsimp [f]; omega⟩
  have hindices (n : ℕ) : n ∈ firstIndices f ↔ Even n := by
    constructor
    · intro hn
      by_contra he
      have ho := Nat.not_even_iff.mp he
      exact hn (n - 1) (by omega) (by dsimp [f]; omega)
    · rintro ⟨k, rfl⟩ m hm heq
      dsimp [f] at heq
      omega
  have hd := dedup_spec f hsurj
  have hi : (Set.ofPred (· ∈ firstIndices f)).Infinite := by
    rw [← hd.2.1]
    exact Set.infinite_range_of_injective hd.1.injective
  have hindex (n : ℕ) : dedupIndex f n = 2 * n := by
    have h := Nat.nth_comp_of_strictMono (p := (· ∈ firstIndices f))
      (f := fun k => 2 * k) (show StrictMono (fun k : ℕ => 2 * k) by
        intro a b hab; dsimp; omega)
      (fun k hk => by
        obtain ⟨i, hi⟩ := (hindices k).mp hk
        exact ⟨i, by change 2 * i = k; omega⟩)
      (n := n) (fun hfin => False.elim (hi hfin))
    have hp : (fun k => 2 * k ∈ firstIndices f) = (fun _ => True) := by
      funext k
      apply propext
      exact iff_true_intro ((hindices (2 * k)).mpr ⟨k, by omega⟩)
    rw [hp, Nat.nth_true] at h
    exact h.symm
  refine ⟨hsurj, ?_, (fun n => by omega), hindex, ?_⟩
  · intro hinj
    have := hinj (show f 0 = f 1 from rfl)
    omega
  · funext n
    change f (dedupIndex f n) = n
    rw [hindex]
    dsimp [f]
    omega

theorem diagonal_prefix :
    (List.range 15).map cantorUnpair =
      [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0),
        (0, 3), (1, 2), (2, 1), (3, 0),
        (0, 4), (1, 3), (2, 2), (3, 1), (4, 0)] := by decide +kernel

theorem row_first_not_enumeration :
    (1, 0) ∉ Set.range (fun n : ℕ => (0, n)) ∧
      ¬ Function.Surjective (fun n : ℕ => (0, n)) := by
  have hmiss : (1, 0) ∉ Set.range (fun n : ℕ => (0, n)) := by
    rintro ⟨n, hn⟩
    have := congrArg Prod.fst hn
    norm_num at this
  exact ⟨hmiss, fun h => hmiss (h (1, 0))⟩

theorem pair_two_three_position :
    cantorPair 2 3 = 17 ∧ cantorUnpair 17 = (2, 3) := by decide +kernel

theorem rationalList_prefix :
    (List.range 10).map rationalList =
      [0, 0, -1, 0, -(1 / 2), 1, 0, -(1 / 3), 1 / 2, -2] := by decide +kernel

/-- A computable decision procedure for the bounded first-occurrence test. -/
private instance rationalFirstIndicesDecidable :
    DecidablePred (· ∈ firstIndices rationalList) :=
  fun n => inferInstanceAs (Decidable (∀ m < n, rationalList m ≠ rationalList n))

private theorem rational_dedupIndex_initial :
    dedupIndex rationalList 0 = 0 ∧ dedupIndex rationalList 1 = 2 ∧
      dedupIndex rationalList 2 = 4 ∧ dedupIndex rationalList 3 = 5 ∧
        dedupIndex rationalList 4 = 7 := by
  have h (n k : ℕ) (hk : k ∈ firstIndices rationalList)
      (hc : Nat.count (· ∈ firstIndices rationalList) k = n) :
      dedupIndex rationalList n = k := by
    change Nat.nth (· ∈ firstIndices rationalList) n = k
    rw [← hc]
    exact Nat.nth_count hk
  exact ⟨h 0 0 (by decide +kernel) (by decide +kernel), h 1 2 (by decide +kernel) (by decide +kernel),
    h 2 4 (by decide +kernel) (by decide +kernel), h 3 5 (by decide +kernel) (by decide +kernel),
    h 4 7 (by decide +kernel) (by decide +kernel)⟩

theorem rationalList_first_five_distinct :
    (List.range 5).map (dedup rationalList) = [0, -1, -(1 / 2), 1, -(1 / 3)] ∧
      (List.range 5).map (dedupIndex rationalList) = [0, 2, 4, 5, 7] := by
  have hi : (List.range 5).map (dedupIndex rationalList) = [0, 2, 4, 5, 7] := by
    rcases rational_dedupIndex_initial with ⟨h₀, h₁, h₂, h₃, h₄⟩
    simp [List.range_succ, h₀, h₁, h₂, h₃, h₄]
  refine ⟨?_, hi⟩
  calc
    (List.range 5).map (dedup rationalList) =
        ((List.range 5).map (dedupIndex rationalList)).map rationalList := by
      rw [List.map_map]
      rfl
    _ = [0, 2, 4, 5, 7].map rationalList := by rw [hi]
    _ = [0, -1, -(1 / 2), 1, -(1 / 3)] := by decide +kernel

theorem rational_two_thirds_position :
    Equiv.intEquivNat.symm 4 = 2 ∧ cantorPair 4 2 = 25 ∧
      cantorUnpair 25 = (4, 2) ∧ rationalList 25 = 2 / 3 := by decide +kernel

end Lemmatheca.Entry.FiniteAndCountableSets
