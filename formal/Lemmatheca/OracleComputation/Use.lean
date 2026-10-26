import Lemmatheca.OracleComputation.Traces
import Mathlib.Data.Finset.Max

/-! Exact finite replay and the maximum-query initial-segment bound. -/
namespace Lemmatheca.ComputabilityTheory.OracleComputation

open UniversalComputation

private theorem indicator_eq_iff (A B : Set ℕ) (q : ℕ) :
    indicator (fun n => n ∈ A) q = indicator (fun n => n ∈ B) q ↔
      (q ∈ A ↔ q ∈ B) := by
  classical
  by_cases ha : q ∈ A <;> by_cases hb : q ∈ B <;> simp [indicator,ha,hb]

def querySet (τ : QueryRecord) : Finset ℕ := (τ.map Prod.fst).toFinset

def useBound (τ : QueryRecord) : ℕ := (querySet τ).sup Nat.succ

def truncate (A : Set ℕ) (u : ℕ) : Set ℕ := A ∩ {q | q < u}

private theorem mem_querySet_iff {τ : QueryRecord} {q : ℕ} :
    q ∈ querySet τ ↔ ∃ b, (q,b) ∈ τ := by
  simp only [querySet, List.mem_toFinset, List.mem_map]
  aesop

theorem useBound_spec (τ : QueryRecord) :
    (∀ q ∈ querySet τ, q < useBound τ) ∧
      useBound τ = if h : (querySet τ).Nonempty then (querySet τ).max' h + 1 else 0 := by
  constructor
  · intro q hq
    exact Nat.lt_of_succ_le (Finset.le_sup (f := Nat.succ) hq)
  · classical
    split_ifs with h
    · apply le_antisymm
      · exact Finset.sup_le fun q hq => Nat.succ_le_succ (Finset.le_max' _ q hq)
      · exact Finset.le_sup (Finset.max'_mem _ h)
    · have he : querySet τ = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simp [useBound,he]

theorem consistency_iff_intersection (A B : Set ℕ) (τ : QueryRecord)
    (hA : Consistent A τ) :
    Consistent B τ ↔ B ∩ (↑(querySet τ) : Set ℕ) = A ∩ (↑(querySet τ) : Set ℕ) := by
  constructor
  · intro hB
    ext q
    by_cases hq : q ∈ querySet τ
    · obtain ⟨b,hb⟩ := mem_querySet_iff.mp hq
      have he := (indicator_eq_iff B A q).mp ((hB q b hb).symm.trans (hA q b hb))
      simpa only [Set.mem_inter_iff, Finset.mem_coe, hq, and_true] using he
    · simp [hq]
  · intro he q b hb
    have hq : q ∈ querySet τ := mem_querySet_iff.mpr ⟨b,hb⟩
    have heq : q ∈ B ↔ q ∈ A := by
      have := Set.ext_iff.mp he q
      simpa only [Set.mem_inter_iff,Finset.mem_coe,hq,and_true] using this
    exact (hA q b hb).trans ((indicator_eq_iff A B q).mpr heq.symm)

theorem finite_replay {A : Set ℕ} {c : Code} {x y : ℕ} {τ : QueryRecord}
    (h : Derives c x τ y) (hA : Consistent A τ) (B : Set ℕ)
    (hB : B ∩ (↑(querySet τ) : Set ℕ) = A ∩ (↑(querySet τ) : Set ℕ)) :
    Consistent B τ ∧ y ∈ eval B c x := by
  have hb := (consistency_iff_intersection A B τ hA).mpr hB
  exact ⟨hb,trace_sound h hb⟩

theorem finite_use (A : Set ℕ) (c : Code) (x y : ℕ) (hy : y ∈ eval A c x) :
    ∃ τ : QueryRecord, Derives c x τ y ∧ Consistent A τ ∧
      (∀ B : Set ℕ, B ∩ (↑(querySet τ) : Set ℕ) = A ∩ (↑(querySet τ) : Set ℕ) →
        eval B c x = Part.some y) ∧
      ∀ B : Set ℕ, (∀ q < useBound τ,
        indicator (fun n => n ∈ B) q = indicator (fun n => n ∈ A) q) →
        eval B c x = Part.some y := by
  obtain ⟨τ,hτ,hA⟩ := (trace_complete A c x y).mp hy
  refine ⟨τ,hτ,hA,?_,?_⟩
  · intro B hB
    exact Part.eq_some_iff.mpr (finite_replay hτ hA B hB).2
  · intro B hB
    have hc : Consistent B τ := by
      intro q b hb
      have hq : q ∈ querySet τ := mem_querySet_iff.mpr ⟨b,hb⟩
      exact (hA q b hb).trans (hB q ((useBound_spec τ).1 q hq)).symm
    exact Part.eq_some_iff.mpr (trace_sound hτ hc)

theorem finite_oracle_truncation (A : Set ℕ) (c : Code) (x y : ℕ)
    (hy : y ∈ eval A c x) :
    ∃ τ : QueryRecord, Derives c x τ y ∧ Consistent A τ ∧
      eval (truncate A (useBound τ)) c x = Part.some y ∧
      eval (A ∩ (↑(querySet τ) : Set ℕ)) c x = Part.some y := by
  obtain ⟨τ,hτ,hA,hF,_⟩ := finite_use A c x y hy
  refine ⟨τ,hτ,hA,hF _ ?_,hF _ ?_⟩
  · ext q
    by_cases hq : q ∈ querySet τ
    · have hu := (useBound_spec τ).1 q hq
      simp [truncate,hq,hu]
    · simp [hq]
  · ext q
    simp only [Set.mem_inter_iff, and_assoc, and_self]

end Lemmatheca.ComputabilityTheory.OracleComputation
