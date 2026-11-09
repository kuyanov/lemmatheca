import Lemmatheca.TruthTableAndWeakTruthTableReductions.Definitions

/-! Compiling ordinary numerical computations and finite prefix tables into Code. -/
namespace Lemmatheca.ComputabilityTheory.StrongReductions

open OracleComputation OracleProgramNumberings UniversalComputation PostsTheorem

noncomputable section

set_option backward.isDefEq.respectTransparency false

def totalCode (f : ℕ → ℕ) (hf : Computable f) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec))

theorem totalCode_eval (f : ℕ → ℕ) (hf : Computable f) (x : ℕ) :
    Nat.Partrec.Code.eval (totalCode f hf) x = Part.some (f x) := by
  exact congrFun (Classical.choose_spec
    (Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec))) x

def appendAnswerCode : Code := embed (ordinaryCode
  (fun p => IncomparableTuringDegrees.appendBit p.unpair.1 p.unpair.2)
  (Primrec.nat_iff.mp (IncomparableTuringDegrees.appendBit_primitive.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))))

def prefixProgram : Code := .prec .zero
  (.comp appendAnswerCode
    (.pair (.comp .right .right) (.comp .query (.comp .left .right))))

def tableProgram (s : TableData) (hs : IsScheme s) : Code :=
  .comp (embed (totalCode (fun p => s.table p.unpair.1 p.unpair.2)
    (hs.2.1.comp Computable.unpair)))
    (.pair identityCode (.comp prefixProgram (.pair .zero (embed (totalCode s.bound hs.1)))))

theorem indicator_bits (C : Set ℕ) (x : ℕ) :
    indicator (fun n => n ∈ C) x = 0 ∨ indicator (fun n => n ∈ C) x = 1 := by
  classical
  by_cases h : x ∈ C <;> simp [indicator, h]

theorem consistent_append_iff (C : Set ℕ) (τ ρ : QueryRecord) :
    Consistent C (τ ++ ρ) ↔ Consistent C τ ∧ Consistent C ρ := by
  simp only [Consistent, List.mem_append]
  aesop

theorem useBound_append (τ ρ : QueryRecord) :
    useBound (τ ++ ρ) = max (useBound τ) (useBound ρ) := by
  simp [useBound, querySet, List.toFinset_append, Finset.sup_union]

theorem prefixCode_append (C : Set ℕ) (n : ℕ) :
    IncomparableTuringDegrees.appendBit (prefixCode C n) (indicator (fun i => i ∈ C) n) =
      prefixCode C (n + 1) := by
  classical
  simp only [IncomparableTuringDegrees.appendBit, FiniteSequenceCoding.append,
    prefixCode, FiniteSequenceCoding.decode_code, List.range_succ, List.map_append,
    List.map_singleton]
  rcases indicator_bits C n with h | h <;> simp [h]

private theorem appendAnswer_trace (r b : ℕ) :
    Derives appendAnswerCode (Nat.pair r b) [] (IncomparableTuringDegrees.appendBit r b) := by
  apply (embed_empty_trace _ _ _).mp
  apply Part.eq_some_iff.mp
  rw [ordinaryCode_eval]
  simp only [Nat.unpair_pair]

theorem prefix_program_trace (C : Set ℕ) (a n : ℕ) :
    ∃ τ, Derives prefixProgram (Nat.pair a n) τ (prefixCode C n) ∧
      Consistent C τ ∧ useBound τ ≤ n := by
  induction n with
  | zero =>
    refine ⟨[], ?_, by simp [Consistent], by simp [useBound, querySet]⟩
    simpa [prefixProgram, prefixCode] using
      (Derives.prec_zero (d := .comp appendAnswerCode
        (.pair (.comp .right .right) (.comp .query (.comp .left .right)))) (Derives.zero a))
  | succ n ih =>
    obtain ⟨τ, hτ, hC, hu⟩ := ih
    let r := prefixCode C n
    let b := indicator (fun q => q ∈ C) n
    have hr : Derives .right (Nat.pair a (Nat.pair n r)) [] (Nat.pair n r) := by
      simpa using Derives.right (Nat.pair a (Nat.pair n r))
    have hv : Derives (.comp .right .right) (Nat.pair a (Nat.pair n r)) [] r := by
      simpa using Derives.comp hr (by simpa using Derives.right (Nat.pair n r))
    have hn : Derives (.comp .left .right) (Nat.pair a (Nat.pair n r)) [] n := by
      simpa using Derives.comp hr (by simpa using Derives.left (Nat.pair n r))
    have hq : Derives (.comp .query (.comp .left .right))
        (Nat.pair a (Nat.pair n r)) [(n,b)] b := by
      simpa using Derives.comp hn (Derives.query n b (indicator_bits C n))
    have hs : Derives (.comp appendAnswerCode
        (.pair (.comp .right .right) (.comp .query (.comp .left .right))))
        (Nat.pair a (Nat.pair n r)) [(n,b)] (prefixCode C (n + 1)) := by
      simpa only [List.nil_append, List.append_nil, r, b, prefixCode_append] using
        Derives.comp (Derives.pair hv hq) (appendAnswer_trace r b)
    refine ⟨τ ++ [(n,b)], Derives.prec_succ hτ hs, ?_, ?_⟩
    · exact (consistent_append_iff _ _ _).mpr ⟨hC, by simp [Consistent,b]⟩
    · rw [useBound_append]
      simpa [useBound, querySet] using max_le (hu.trans (Nat.le_succ n)) (le_refl (n+1))

theorem table_program (s : TableData) (hs : IsScheme s) (C : Set ℕ) (x : ℕ) :
    (eval C (tableProgram s hs) x = Part.some (s.table x (prefixCode C (s.bound x)))) ∧
    ∃ τ, Derives (tableProgram s hs) x τ (s.table x (prefixCode C (s.bound x))) ∧
      Consistent C τ ∧ useBound τ ≤ s.bound x := by
  obtain ⟨τ,hτ,hC,hu⟩ := prefix_program_trace C 0 (s.bound x)
  have hb : Derives (embed (totalCode s.bound hs.1)) x [] (s.bound x) :=
    (embed_empty_trace _ _ _).mp (Part.eq_some_iff.mp (totalCode_eval _ _ _))
  have hin : Derives (.pair .zero (embed (totalCode s.bound hs.1))) x []
      (Nat.pair 0 (s.bound x)) := by
    simpa using Derives.pair (Derives.zero x) hb
  have hp : Derives (.comp prefixProgram (.pair .zero (embed (totalCode s.bound hs.1))))
      x τ (prefixCode C (s.bound x)) := by simpa using Derives.comp hin hτ
  have hid : Derives identityCode x [] x := by
    simpa [identityCode] using Derives.pair (Derives.left x) (Derives.right x)
  have hl : Derives (embed (totalCode (fun p => s.table p.unpair.1 p.unpair.2)
      (hs.2.1.comp Computable.unpair))) (Nat.pair x (prefixCode C (s.bound x))) []
      (s.table x (prefixCode C (s.bound x))) := by
    apply (embed_empty_trace _ _ _).mp
    apply Part.eq_some_iff.mp
    simpa using totalCode_eval (fun p => s.table p.unpair.1 p.unpair.2)
      (hs.2.1.comp Computable.unpair) (Nat.pair x (prefixCode C (s.bound x)))
  have ht : Derives (tableProgram s hs) x τ (s.table x (prefixCode C (s.bound x))) := by
    simpa only [tableProgram, List.nil_append, List.append_nil] using
      Derives.comp (Derives.pair hid hp) hl
  exact ⟨Part.eq_some_iff.mpr (trace_sound ht hC), τ, ht, hC, hu⟩

theorem table_program_reduces {s : TableData} {A B : Set ℕ} (h : Presents s A B) :
    BoundedReduction (tableProgram s h.1) s.bound A B ∧
      AllOracleTotal (tableProgram s h.1) := by
  constructor
  · refine ⟨h.1.1, fun x => ?_⟩
    simpa only [h.2 x] using (table_program s h.1 B x).2
  · intro C x
    rw [(table_program s h.1 C x).1]
    trivial

def manyOneData (f : ℕ → ℕ) : TableData :=
  ⟨fun x => f x + 1, fun x w => beta w (f x)⟩

theorem manyOne_scheme {A B : Set ℕ} (f : ℕ → ℕ) (hf : Computable f)
    (hAB : ∀ x, x ∈ A ↔ f x ∈ B) : Presents (manyOneData f) A B := by
  refine ⟨⟨Computable.succ.comp hf, ?_, fun x w => beta_bits w (f x)⟩, ?_⟩
  · exact beta_primitive.to_comp.comp Computable.snd (hf.comp Computable.fst)
  · intro x
    change beta (prefixCode B (f x + 1)) (f x) = indicator (fun n => n ∈ A) x
    rw [(prefixCode_spec B (f x + 1)).2 (f x) (Nat.lt_succ_self _)]
    classical
    simp only [indicator, hAB x]

theorem manyOne_program_trace (f : ℕ → ℕ) (hf : Computable f) (B : Set ℕ) (x : ℕ) :
    Derives (TuringDegrees.preprocess (totalCode f hf)) x
      [(f x, indicator (fun n => n ∈ B) (f x))] (indicator (fun n => n ∈ B) (f x)) ∧
      Consistent B [(f x, indicator (fun n => n ∈ B) (f x))] ∧
      useBound [(f x, indicator (fun n => n ∈ B) (f x))] = f x + 1 := by
  constructor
  · have h := (embed_empty_trace _ _ _).mp
      (Part.eq_some_iff.mp (totalCode_eval f hf x))
    simpa [TuringDegrees.preprocess] using Derives.comp h
      (Derives.query (f x) (indicator (fun n => n ∈ B) (f x)) (indicator_bits B (f x)))
  · constructor
    · simp [Consistent]
    · simp [useBound, querySet]

theorem manyOne_imp_tt {A B : Set ℕ}
    (h : ManyOneReducible (fun n => n ∈ A) (fun n => n ∈ B)) :
    TruthTableReducible A B := by
  obtain ⟨f,hf,hAB⟩ := h
  exact ⟨manyOneData f, manyOne_scheme f hf hAB⟩

theorem tt_imp_wtt {A B : Set ℕ} (h : TruthTableReducible A B) :
    WeakTruthTableReducible A B := by
  obtain ⟨s,hs⟩ := h
  exact ⟨tableProgram s hs.1, s.bound, (table_program_reduces hs).1⟩

theorem wtt_imp_turing {A B : Set ℕ} (h : WeakTruthTableReducible A B) :
    TuringDegrees.Reducible A B := by
  obtain ⟨c,u,hc⟩ := h
  refine ⟨c, fun x => ?_⟩
  obtain ⟨τ,hτ,hB,_⟩ := hc.2 x
  exact Part.eq_some_iff.mpr (trace_sound hτ hB)

end
end Lemmatheca.ComputabilityTheory.StrongReductions
