import Lemmatheca.EffectiveEnumerations.Settling

/-! Exact finite histories, the displayed stream, and the two-arrival example. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveEnumerations.Examples

open UniversalComputation

def emptyStages (_s : ℕ) : Set ℕ := ∅

def lateStages (N s : ℕ) : Set ℕ := if s ≤ N then ∅ else {0}

theorem finite_quiet_history (N : ℕ) :
    Computable₂ (fun s x => indicator (emptyStages s) x) ∧
      Computable₂ (fun s x => indicator (lateStages N s) x) ∧
      Monotone emptyStages ∧ Monotone (lateStages N) ∧
      (∀ s, emptyStages s ⊆ Set.Iio 1 ∧ lateStages N s ⊆ Set.Iio 1) ∧
      (∀ s ≤ N, emptyStages s = lateStages N s) ∧
      (∀ x, (∃ s, x ∈ emptyStages s) ↔ False) ∧
      (∀ x, (∃ s, x ∈ lateStages N s) ↔ x = 0) := by
  classical
  have hE : Computable₂ (fun s x => indicator (emptyStages s) x) := by
    exact (Computable.const 0).of_eq fun p => by
      dsimp only [indicator, emptyStages]
      split_ifs with h
      · exact False.elim h
      · rfl
  have hP : PrimrecPred (fun p : ℕ × ℕ => N < p.1 ∧ p.2 = 0) :=
    (Primrec.nat_lt.comp (Primrec.const N) Primrec.fst).and
      (Primrec.eq.comp Primrec.snd (Primrec.const 0))
  have hL : Computable₂ (fun s x => indicator (lateStages N s) x) := by
    apply (Primrec.ite hP (Primrec.const 1) (Primrec.const 0)).to_comp.of_eq
    intro p
    change (if N < p.1 ∧ p.2 = 0 then 1 else 0) =
      if p.2 ∈ lateStages N p.1 then 1 else 0
    by_cases hs : p.1 ≤ N
    · simp [lateStages, hs, show ¬ N < p.1 by omega]
    · simp [lateStages, hs, show N < p.1 by omega]
  refine ⟨hE, hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t _
    exact Set.Subset.rfl
  · intro s t hst x hx
    by_cases hs : s ≤ N
    · simp [lateStages, hs] at hx
    · have ht : ¬ t ≤ N := by omega
      simpa [lateStages, ht] using (show x ∈ ({0} : Set ℕ) from by
        simpa [lateStages, hs] using hx)
  · intro s
    refine ⟨by simp [emptyStages], ?_⟩
    intro x hx
    by_cases hs : s ≤ N
    · simp [lateStages, hs] at hx
    · have he : x = 0 := by simpa [lateStages, hs] using hx
      subst x
      exact Nat.zero_lt_one
  · intro s hs
    simp [emptyStages, lateStages, hs]
  · intro x
    simp [emptyStages]
  · intro x
    constructor
    · rintro ⟨s, hs⟩
      by_cases hn : s ≤ N
      · simp [lateStages, hn] at hs
      · simpa [lateStages, hn] using hs
    · intro hx
      subst x
      exact ⟨N + 1, by simp [lateStages]⟩

def sampleStream (j : ℕ) : ℕ :=
  if j = 0 then 4 else if j = 1 then 1 else if j = 2 then 4 else
  if j = 3 then 7 else if j = 4 then 2 else if j = 5 then 7 else
  if j = 6 then 9 else j + 3

theorem sample_stream_computable : Computable sampleStream := by
  have heq (n : ℕ) : PrimrecPred (fun j : ℕ => j = n) :=
    Primrec.eq.comp Primrec.id (Primrec.const n)
  exact (Primrec.ite (heq 0) (Primrec.const 4)
    (Primrec.ite (heq 1) (Primrec.const 1)
    (Primrec.ite (heq 2) (Primrec.const 4)
    (Primrec.ite (heq 3) (Primrec.const 7)
    (Primrec.ite (heq 4) (Primrec.const 2)
    (Primrec.ite (heq 5) (Primrec.const 7)
    (Primrec.ite (heq 6) (Primrec.const 9)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 3))))))))).to_comp

theorem sample_stream_range :
    Set.range sampleStream = ({1, 2, 4, 7} : Set ℕ) ∪ Set.Ici 9 ∧
      (Set.range sampleStream).Infinite := by
  have hr : Set.range sampleStream = ({1, 2, 4, 7} : Set ℕ) ∪ Set.Ici 9 := by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_Ici]
    constructor
    · rintro ⟨j, rfl⟩
      dsimp only [sampleStream]
      split_ifs <;> omega
    · rintro ((rfl | rfl | rfl | rfl) | hx)
      · exact ⟨1, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
      · by_cases h9 : x = 9
        · exact ⟨6, h9.symm⟩
        · refine ⟨x - 3, ?_⟩
          dsimp only [sampleStream]
          split_ifs <;> omega
  refine ⟨hr, ?_⟩
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => n + 9)
    (by intro a b h; change a + 9 = b + 9 at h; omega)
  intro n
  rw [hr]
  exact Or.inr (by change 9 ≤ n + 9; omega)

noncomputable def sampleRecords : ℕ → ℕ :=
  recordSequence sampleStream sample_stream_range.2

theorem sample_record_indices :
    recordIndex sampleStream sample_stream_range.2 4 = 3 ∧
      recordIndex sampleStream sample_stream_range.2 7 = 6 := by
  classical
  constructor
  · unfold recordIndex
    apply (Nat.find_eq_iff _).mpr
    refine ⟨by norm_num [sampleStream], ?_⟩
    intro j hj
    dsimp only [sampleStream]
    split_ifs <;> omega
  · unfold recordIndex
    apply (Nat.find_eq_iff _).mpr
    refine ⟨by norm_num [sampleStream], ?_⟩
    intro j hj
    dsimp only [sampleStream]
    split_ifs <;> omega

private theorem sample_record_index_tail (y : ℕ) (hy : 9 ≤ y) :
    recordIndex sampleStream sample_stream_range.2 y = y - 2 := by
  classical
  unfold recordIndex
  apply (Nat.find_eq_iff _).mpr
  constructor
  · dsimp only [sampleStream]
    split_ifs <;> omega
  · intro j hj
    dsimp only [sampleStream]
    split_ifs <;> omega

private theorem sample_record_high_tail (y : ℕ) (hy : 9 ≤ y) :
    recordHigh sampleStream sample_stream_range.2 y = y + 1 := by
  rw [recordHigh, sample_record_index_tail y hy]
  dsimp only [sampleStream]
  split_ifs <;> omega

theorem sample_records_values :
    sampleRecords 0 = 4 ∧ sampleRecords 1 = 7 ∧ sampleRecords 2 = 9 ∧
      (∀ n, 2 ≤ n → sampleRecords n = n + 7) := by
  have step (n : ℕ) : sampleRecords (n + 1) =
      recordHigh sampleStream sample_stream_range.2 (sampleRecords n) := rfl
  have h0 : sampleRecords 0 = 4 := rfl
  have h1 : sampleRecords 1 = 7 := by
    rw [step, h0, recordHigh, sample_record_indices.1]
    rfl
  have h2 : sampleRecords 2 = 9 := by
    rw [show 2 = 1 + 1 from rfl, step, h1, recordHigh, sample_record_indices.2]
    rfl
  have tail (k : ℕ) : sampleRecords (k + 2) = k + 9 := by
    induction k with
    | zero => exact h2
    | succ k ih =>
      change sampleRecords ((k + 2) + 1) = k + 1 + 9
      rw [step, ih, sample_record_high_tail (k + 9) (by omega)]
  refine ⟨h0, h1, h2, ?_⟩
  intro n hn
  calc
    sampleRecords n = sampleRecords (n - 2 + 2) := by congr 1; omega
    _ = n - 2 + 9 := tail (n - 2)
    _ = n + 7 := by omega

theorem sample_records_range :
    Set.range sampleRecords = ({4, 7} : Set ℕ) ∪ Set.Ici 9 ∧
      Set.range sampleStream \ Set.range sampleRecords = ({1, 2} : Set ℕ) := by
  obtain ⟨h0, h1, _, ht⟩ := sample_records_values
  have hr : Set.range sampleRecords = ({4, 7} : Set ℕ) ∪ Set.Ici 9 := by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_Ici]
    constructor
    · rintro ⟨n, rfl⟩
      by_cases hn0 : n = 0
      · simp [hn0, h0]
      · by_cases hn1 : n = 1
        · simp [hn1, h1]
        · rw [ht n (by omega)]
          omega
    · rintro ((rfl | rfl) | hx)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨x - 7, by rw [ht _ (by omega)]; omega⟩
  refine ⟨hr, ?_⟩
  rw [sample_stream_range.1, hr]
  ext x
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_Ici]
  omega

def arrivalTest (s x : ℕ) : ℕ :=
  if (x = 1 ∧ 3 ≤ s) ∨ (x = 4 ∧ 6 ≤ s) then 1 else 0

theorem arrival_test_data :
    Computable₂ arrivalTest ∧
      (∀ s x, arrivalTest s x = 0 ∨ arrivalTest s x = 1) ∧
      (∀ s x, arrivalTest s x = 1 → x < 5) ∧
      (∀ s x, arrivalTest s x = 1 → arrivalTest (s + 1) x = 1) ∧
      (∀ x, x ∈ ({1, 4} : Set ℕ) ↔ ∃ s, arrivalTest s x = 1) := by
  have hp : PrimrecPred (fun p : ℕ × ℕ =>
      (p.2 = 1 ∧ 3 ≤ p.1) ∨ (p.2 = 4 ∧ 6 ≤ p.1)) :=
    ((Primrec.eq.comp Primrec.snd (Primrec.const 1)).and
      (Primrec.nat_le.comp (Primrec.const 3) Primrec.fst)).or
    ((Primrec.eq.comp Primrec.snd (Primrec.const 4)).and
      (Primrec.nat_le.comp (Primrec.const 6) Primrec.fst))
  have hs (s x : ℕ) : arrivalTest s x = 1 ↔
      (x = 1 ∧ 3 ≤ s) ∨ (x = 4 ∧ 6 ≤ s) := by
    unfold arrivalTest
    split_ifs <;> simp_all
  refine ⟨(Primrec.ite hp (Primrec.const 1) (Primrec.const 0)).to_comp, ?_, ?_, ?_, ?_⟩
  · intro s x
    unfold arrivalTest
    split_ifs <;> simp
  · intro s x hx
    have h := (hs s x).mp hx
    omega
  · intro s x hx
    apply (hs (s + 1) x).mpr
    have h := (hs s x).mp hx
    omega
  · intro x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨3, (hs 3 1).mpr (Or.inl ⟨rfl, le_rfl⟩)⟩
      · exact ⟨6, (hs 6 4).mpr (Or.inr ⟨rfl, le_rfl⟩)⟩
    · rintro ⟨s, ht⟩
      exact ((hs s x).mp ht).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

def arrivalApproximation : ComputableApproximation ({1, 4} : Set ℕ) where
  bound := fun _ => 5
  test := arrivalTest
  bound_computable := Computable.const 5
  test_computable := arrival_test_data.1
  binary := arrival_test_data.2.1
  bounded := arrival_test_data.2.2.1
  increasing := arrival_test_data.2.2.2.1
  exhaustive := arrival_test_data.2.2.2.2

theorem arrival_stages (s x : ℕ) :
    x ∈ arrivalApproximation.atStage s ↔ (x = 1 ∧ 3 ≤ s) ∨ (x = 4 ∧ 6 ≤ s) := by
  change arrivalTest s x = 1 ↔ _
  unfold arrivalTest
  split_ifs <;> simp_all

def arrivalModulus (n : ℕ) : ℕ := if n ≤ 1 then 0 else if n ≤ 4 then 3 else 6

theorem arrival_least_modulus :
    Computable arrivalModulus ∧
      leastSettlingStage arrivalApproximation = arrivalModulus ∧
      arrivalModulus 5 = 6 := by
  have hc : Computable arrivalModulus :=
    (Primrec.ite (Primrec.nat_le.comp Primrec.id (Primrec.const 1)) (Primrec.const 0)
      (Primrec.ite (Primrec.nat_le.comp Primrec.id (Primrec.const 4))
        (Primrec.const 3) (Primrec.const 6))).to_comp
  have hm : SettlingModulus ({1, 4} : Set ℕ) arrivalApproximation.atStage arrivalModulus := by
    intro n x hx
    rw [arrival_stages]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    unfold arrivalModulus
    split_ifs <;> omega
  refine ⟨hc, ?_, rfl⟩
  funext n
  apply Nat.le_antisymm
  · exact (least_settling_spec arrivalApproximation).2.1 n _ (hm n)
  · have hs := (least_settling_spec arrivalApproximation).1 n
    by_cases hn1 : n ≤ 1
    · simp [arrivalModulus, hn1]
    · by_cases hn4 : n ≤ 4
      · have h := (hs 1 (by omega)).mp (by simp)
        rw [arrival_stages] at h
        simp only [arrivalModulus, hn1, hn4, ite_false, ite_true]
        omega
      · have h := (hs 4 (by omega)).mp (by simp)
        rw [arrival_stages] at h
        simp only [arrivalModulus, hn1, hn4, ite_false]
        omega

end Lemmatheca.ComputabilityTheory.EffectiveEnumerations.Examples
