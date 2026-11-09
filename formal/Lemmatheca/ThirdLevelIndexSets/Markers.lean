import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Data.List.GetD

/-! Bounded finite-list implementations of ordered complement markers.
Lists need not be sorted; the stage invariant supplies absence of duplicates. -/
namespace Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets

/-- The actual bounded ascending list of omissions below a supplied bound. -/
def missingBelow (B : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).filter (fun z => !B.contains z)

/-- Rank is zero based. The finite bound always contains the requested omission. -/
def marker (B : List ℕ) (n : ℕ) : ℕ :=
  (missingBelow B (n + B.length + 1)).getD n 0

/-- Insert the current value, with a fresh value recomputed on every call. -/
def bump (B : List ℕ) (y : ℕ) : List ℕ := marker B y :: B

private theorem missing_succ (B : List ℕ) (k : ℕ) :
    missingBelow B (k+1) = if k ∈ B then missingBelow B k else missingBelow B k ++ [k] := by
  by_cases h : k ∈ B <;> simp [missingBelow, List.range_succ, h]

private theorem missing_count (B : List ℕ) (k : ℕ) :
    (missingBelow B k).length = Nat.count (fun z => z ∉ B) k := by
  simp [missingBelow, Nat.count, List.countP_eq_length_filter]

private theorem missing_length_bound (B : List ℕ) (k : ℕ) :
    k ≤ B.length + (missingBelow B k).length := by
  let L := (List.range k).filter (fun z => B.contains z)
  have hN : L.Nodup := (List.nodup_range (n := k)).filter _
  have hsub : L.toFinset ⊆ B.toFinset := by
    intro z hz
    simpa [L] using (List.mem_filter.mp (List.mem_toFinset.mp hz)).2
  have hl : L.length ≤ B.length := by
    rw [← List.toFinset_card_of_nodup hN]
    exact (Finset.card_le_card hsub).trans B.toFinset_card_le
  have hp := (List.range k).length_eq_length_filter_add (fun z => B.contains z)
  have he : k = L.length + (missingBelow B k).length := by
    simpa [L, missingBelow] using hp
  omega

private theorem missing_get_spec (B : List ℕ) (k n : ℕ)
    (hn : n < (missingBelow B k).length) :
    let z := (missingBelow B k).getD n 0
    z ∉ B ∧ z < k ∧ (missingBelow B z).length = n := by
  induction k with
  | zero => simp [missingBelow] at hn
  | succ k ih =>
    by_cases hk : k ∈ B
    · rw [missing_succ, ite_eq_left hk] at hn ⊢
      obtain ⟨ha,hb,hc⟩ := ih hn
      exact ⟨ha, by omega, hc⟩
    · rw [missing_succ, ite_eq_right hk] at hn ⊢
      by_cases hl : n < (missingBelow B k).length
      · rw [List.getD_append _ _ _ _ hl]
        obtain ⟨ha,hb,hc⟩ := ih hl
        exact ⟨ha, by omega, hc⟩
      · have he : n = (missingBelow B k).length := by
          simp only [List.length_append, List.length_singleton] at hn
          omega
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp [he, hk]

theorem marker_primitive : Primrec₂ marker := by
  have hmem : PrimrecRel (fun (B : List ℕ) z => z ∈ B) :=
    Primrec.eq.exists_mem_list.of_eq (by simp)
  have hnot : PrimrecRel (fun (z : ℕ) (B : List ℕ) => z ∉ B) := hmem.swap.not
  have hf := hnot.listFilter
  have hm : Primrec₂ missingBelow :=
    (hf.comp (Primrec.list_range.comp Primrec.snd) Primrec.fst).of_eq
      (fun p => by simp [missingBelow])
  have hb : Primrec (fun p : List ℕ × ℕ => p.2 + p.1.length + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp Primrec.snd
      (Primrec.list_length.comp Primrec.fst))
  exact (Primrec.list_getD 0).comp (hm.comp Primrec.fst hb) Primrec.snd

theorem marker_spec (B : List ℕ) (n : ℕ) :
    marker B n ∉ B ∧ (missingBelow B (marker B n)).length = n := by
  have hb := missing_length_bound B (n+B.length+1)
  have hn : n < (missingBelow B (n+B.length+1)).length := by omega
  have h := missing_get_spec B (n+B.length+1) n hn
  exact ⟨h.1,h.2.2⟩

theorem marker_unique (B : List ℕ) (n k : ℕ) :
    marker B n = k ↔ k ∉ B ∧ (missingBelow B k).length = n := by
  constructor
  · rintro rfl
    exact marker_spec B n
  · rintro ⟨hk,hc⟩
    apply Nat.count_injective (p := fun z => z ∉ B) (marker_spec B n).1 hk
    rw [← missing_count, ← missing_count, (marker_spec B n).2, hc]

theorem marker_bound (B : List ℕ) (n : ℕ) : marker B n ≤ n + B.length := by
  have hb := missing_length_bound B (n+B.length+1)
  have hn : n < (missingBelow B (n+B.length+1)).length := by omega
  exact Nat.le_of_lt_succ (missing_get_spec B (n+B.length+1) n hn).2.1

theorem marker_card_bound (B : List ℕ) (hB : B.Nodup) (n : ℕ) :
    marker B n ≤ n + B.toFinset.card := by
  rw [List.toFinset_card_of_nodup hB]
  exact marker_bound B n

theorem marker_strictMono (B : List ℕ) : StrictMono (marker B) := by
  intro i j hij
  apply Nat.lt_of_count_lt_count (p := fun z => z ∉ B)
  simpa only [← missing_count, (marker_spec B i).2, (marker_spec B j).2] using hij

private theorem missing_insert_count (B : List ℕ) (a : ℕ) (ha : a ∉ B) (k : ℕ) :
    Nat.count (fun z => z ∉ a :: B) k + (if a < k then 1 else 0) =
      Nat.count (fun z => z ∉ B) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.count_succ, Nat.count_succ]
    by_cases hka : k = a
    · subst k
      simp [ha] at ih ⊢
      omega
    · by_cases hk : k ∈ B <;> by_cases hak : a < k <;>
        simp [List.mem_cons, hka, hk, hak, show (a < k+1 ↔ a < k) by omega] at ih ⊢ <;> omega

private theorem missing_included_count (B C : List ℕ) (hBC : ∀ z ∈ B, z ∈ C) (k : ℕ) :
    Nat.count (fun z => z ∉ C) k ≤ Nat.count (fun z => z ∉ B) k := by
  exact Nat.count_mono_left (fun z _ h hB => h (hBC z hB))

theorem bump_shift (B : List ℕ) (y i : ℕ) :
    marker (bump B y) i = if i < y then marker B i else marker B (i+1) := by
  split_ifs with hi
  · apply (marker_unique (bump B y) i (marker B i)).mpr
    have hlt := marker_strictMono B hi
    have hc := missing_insert_count B (marker B y) (marker_spec B y).1 (marker B i)
    refine ⟨by simp [bump, (marker_spec B i).1, ne_of_lt hlt], ?_⟩
    have hnot : ¬ marker B y < marker B i := by omega
    rw [← missing_count (marker B y :: B) (marker B i),
      ← missing_count B (marker B i), (marker_spec B i).2] at hc
    simpa only [ite_eq_right hnot, Nat.add_zero, bump] using hc
  · apply (marker_unique (bump B y) i (marker B (i+1))).mpr
    have hlt := marker_strictMono B (show y < i+1 by omega)
    have hc := missing_insert_count B (marker B y) (marker_spec B y).1 (marker B (i+1))
    refine ⟨by simp [bump, (marker_spec B (i+1)).1, ne_of_gt hlt], ?_⟩
    rw [← missing_count (marker B y :: B) (marker B (i+1)),
      ← missing_count B (marker B (i+1)), (marker_spec B (i+1)).2] at hc
    simp only [ite_eq_left hlt] at hc
    change (missingBelow (marker B y :: B) (marker B (i+1))).length = i
    omega

theorem bump_marker_mono (B : List ℕ) (y i : ℕ) :
    marker B i ≤ marker (bump B y) i := by
  rw [bump_shift]
  split
  · exact le_rfl
  · exact (marker_strictMono B).monotone (by omega)

theorem bump_marker_strict (B : List ℕ) (y : ℕ) :
    marker B y < marker (bump B y) y := by
  rw [bump_shift, ite_eq_right (by omega)]
  exact marker_strictMono B (by omega)

theorem bump_prefix (B : List ℕ) (y i : ℕ) (hi : i < y) :
    marker (bump B y) i = marker B i := by
  rw [bump_shift, ite_eq_left hi]

theorem bump_nodup (B : List ℕ) (hB : B.Nodup) (y : ℕ) :
    (bump B y).Nodup := by
  exact List.nodup_cons.mpr ⟨(marker_spec B y).1,hB⟩

theorem bump_primitive : Primrec₂ bump := by
  exact Primrec.list_cons.comp marker_primitive Primrec.fst

/-- Ordinary finite-set inclusion, independent of the insertion order of lists. -/
def Included (B C : List ℕ) : Prop := ∀ z ∈ B, z ∈ C

/-- A routine finite-prefix transport lemma used in the stage stabilization proofs. -/
theorem marker_prefix_of_included (B C : List ℕ) (hBC : Included B C) (n : ℕ)
    (ha : ∀ i ≤ n, marker B i ∉ C) :
    ∀ i ≤ n, marker C i = marker B i := by
  have hlow : ∀ i, i ≤ n → i ≤ Nat.count (fun z => z ∉ C) (marker B i) := by
    intro i
    induction i with
    | zero => exact fun _ => Nat.zero_le _
    | succ i ih =>
      intro hi
      have hlo := ih (by omega)
      have hs := Nat.count_strict_mono (p := fun z => z ∉ C) (ha i (by omega))
        (marker_strictMono B (Nat.lt_succ_self i))
      change Nat.count (fun z => z ∉ C) (marker B i) <
        Nat.count (fun z => z ∉ C) (marker B (i+1)) at hs
      change i+1 ≤ Nat.count (fun z => z ∉ C) (marker B (i+1))
      omega
  intro i hi
  apply (marker_unique C i (marker B i)).mpr
  refine ⟨ha i hi, ?_⟩
  rw [missing_count]
  have hu := missing_included_count B C hBC (marker B i)
  rw [← missing_count B (marker B i), (marker_spec B i).2] at hu
  exact Nat.le_antisymm hu (hlow i hi)

theorem marker_monotone_of_included (B C : List ℕ) (hBC : Included B C) (n : ℕ) :
    marker B n ≤ marker C n := by
  by_contra h
  have hlt : marker C n < marker B n := by omega
  have hnot : marker C n ∉ B := fun hm => (marker_spec C n).1 (hBC _ hm)
  have hs := Nat.count_strict_mono (p := fun z => z ∉ B) hnot hlt
  have hu := missing_included_count B C hBC (marker C n)
  rw [← missing_count B (marker B n), (marker_spec B n).2] at hs
  rw [← missing_count C (marker C n), (marker_spec C n).2] at hu
  omega

end Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets
