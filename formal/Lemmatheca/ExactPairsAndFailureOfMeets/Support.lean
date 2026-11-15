import Lemmatheca.OrdinaryMinimalPairsOfTuringDegrees.Core

/-! Actual column programs, finite correction tables, and both finite joins. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs

open OracleComputation OracleProgramNumberings UniversalComputation IncomparableTuringDegrees

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section
local instance exactPairsSupportDecidable : DecidablePred (fun p : Prop => p) :=
  Classical.propDecidable

def column (X : Set ℕ) (i : ℕ) : Set ℕ := {x | Nat.pair i x ∈ X}

def columnCode (i : ℕ) : Code := .comp .query (.pair (constantCode i) identityCode)

theorem column_code_eval (i : ℕ) (X : Set ℕ) (x : ℕ) :
    eval X (columnCode i) x = Part.some (indicator (fun x => x ∈ column X i) x) := by
  simp [columnCode, eval, constant_eval, identity_eval, column, indicator]

theorem column_index_primitive : Primrec (fun i => encodeCode (columnCode i)) := by
  have h := compIndex_primitive.comp (Primrec.const 4)
    (pairIndex_primitive.comp constantIndex_primitive (Primrec.const (encodeCode identityCode)))
  exact h.of_eq (fun _ => by simp [columnCode, compIndex, pairIndex, constantIndex, encodeCode])

theorem column_reducible (X : Set ℕ) (i : ℕ) : TuringDegrees.Reducible (column X i) X := by
  exact ⟨columnCode i, column_code_eval i X⟩

/-- A concrete table of the first m characteristic bits, with length exactly m. -/
def errorTable (U : Set ℕ) (m : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range m).map (indicator (fun x => x ∈ U)))

/-- Input is (x,table), and no oracle query is needed for this finite lookup. -/
def correctionBit (z : ℕ) : ℕ := wordBit z.unpair.2 z.unpair.1

def correctionBranch (z : ℕ) : ℕ :=
  if z.unpair.1 < wordLength z.unpair.2 then 0 else 1

theorem correction_bit_primitive : Nat.Primrec correctionBit := by
  exact Primrec.nat_iff.mp (PostsTheorem.beta_primitive.comp
    (Primrec.snd.comp Primrec.unpair) (Primrec.fst.comp Primrec.unpair))

theorem correction_branch_primitive : Nat.Primrec correctionBranch := by
  exact Primrec.nat_iff.mp (Primrec.ite (Primrec.nat_lt.comp
    (Primrec.fst.comp Primrec.unpair)
    (FiniteSequenceCoding.primrec_length.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.const 0) (Primrec.const 1))

def correctionBitCode : Code := embed (ordinaryCode correctionBit correction_bit_primitive)

def correctionBranchCode : Code := embed (ordinaryCode correctionBranch correction_branch_primitive)

/-- Recursion with a zero-or-one counter queries V exactly in the latter branch. -/
def correctionCode (t : ℕ) : Code :=
  .comp (.prec (.comp correctionBitCode (.pair identityCode (constantCode t)))
      (.comp .query .left))
    (.pair identityCode (.comp correctionBranchCode (.pair identityCode (constantCode t))))

theorem error_table_spec (U : Set ℕ) (m : ℕ) :
    wordLength (errorTable U m) = m ∧
      ∀ x < m, wordBit (errorTable U m) x = indicator (fun x => x ∈ U) x := by
  exact PostsTheorem.prefixCode_spec U m

theorem correction_code_eval (V : Set ℕ) (t x : ℕ) :
    eval V (correctionCode t) x = Part.some
      (if x < wordLength t then wordBit t x else indicator (fun x => x ∈ V) x) := by
  by_cases hx : x < wordLength t <;>
    simp [correctionCode, correctionBitCode, correctionBranchCode, eval, eval_embed,
      ordinaryCode_eval, constant_eval, identity_eval, correctionBranch, correctionBit, hx]

theorem correction_reduces (U V : Set ℕ) (m : ℕ)
    (h : ∀ x, m ≤ x → indicator (fun x => x ∈ U) x = indicator (fun x => x ∈ V) x) :
    TuringDegrees.Reduces (correctionCode (errorTable U m)) U V := by
  intro x
  rw [correction_code_eval, (error_table_spec U m).1]
  by_cases hx : x < m
  · simp [hx, (error_table_spec U m).2 x hx]
  · simp [hx, ← h x (by omega)]

theorem finite_variant_equivalent (U V : Set ℕ) (m : ℕ)
    (h : ∀ x, m ≤ x → indicator (fun x => x ∈ U) x = indicator (fun x => x ∈ V) x) :
    TuringDegrees.Equivalent U V := by
  exact ⟨⟨correctionCode (errorTable U m), correction_reduces U V m h⟩,
    ⟨correctionCode (errorTable V m), correction_reduces V U m (fun x hx => (h x hx).symm)⟩⟩

def finiteJoin (A : ℕ → Set ℕ) : ℕ → Set ℕ
  | 0 => ∅
  | s + 1 => TuringDegrees.join (finiteJoin A s) (A s)

def boundedJoin (A : ℕ → Set ℕ) (s : ℕ) : Set ℕ :=
  {q | q.unpair.1 < s ∧ q.unpair.2 ∈ A q.unpair.1}

theorem bounded_join_indicator (A : ℕ → Set ℕ) (s q : ℕ) :
    indicator (fun x => x ∈ boundedJoin A s) q =
      if q.unpair.1 < s then indicator (fun x => x ∈ A q.unpair.1) q.unpair.2 else 0 := by
  by_cases hi : q.unpair.1 < s <;> simp [indicator, boundedJoin, hi]

theorem finite_join_universal (A : ℕ → Set ℕ) (s : ℕ) (Z : Set ℕ) :
    TuringDegrees.Reducible (finiteJoin A s) Z ↔
      ∀ i < s, TuringDegrees.Reducible (A i) Z := by
  induction s with
  | zero =>
      constructor
      · intro _ i hi; omega
      · intro _
        exact ⟨.zero, fun x => by simp [finiteJoin, eval, indicator]⟩
  | succ s ih =>
      rw [finiteJoin, TuringDegrees.join_reducible_iff, ih]
      constructor
      · rintro ⟨hs,ha⟩ i hi
        by_cases he : i = s
        · simpa [he] using ha
        · exact hs i (by omega)
      · intro h
        exact ⟨fun i hi => h i (by omega), h s (by omega)⟩

/-- Native reducibility, not a parallel finite-join relation. -/
theorem bounded_join_successor (A : ℕ → Set ℕ) (s : ℕ) :
    TuringDegrees.Equivalent (boundedJoin A (s + 1))
      (TuringDegrees.join (boundedJoin A s) (A s)) := by
  let f : ℕ → ℕ := fun q => if q.unpair.1 < s then 2 * q else
    if q.unpair.1 = s then 2 * q.unpair.2 + 1 else 2 * Nat.pair s 0
  have hi : Primrec (fun q : ℕ => q.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hx : Primrec (fun q : ℕ => q.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hf : Primrec f := Primrec.ite (Primrec.nat_lt.comp hi (Primrec.const s))
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.ite (Primrec.eq.comp hi (Primrec.const s))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hx) (Primrec.const 1))
      (Primrec.const (2 * Nat.pair s 0)))
  have hforward : TuringDegrees.Reducible (boundedJoin A (s + 1))
      (TuringDegrees.join (boundedJoin A s) (A s)) := by
    apply TuringDegrees.manyOne_imp_reducible
    refine ⟨f, hf.to_comp, ?_⟩
    intro q
    by_cases hlt : q.unpair.1 < s
    · simp only [f, ite_eq_left hlt]
      rw [← (TuringDegrees.join_even_reduction (boundedJoin A s) (A s)).2 q]
      simp [boundedJoin, hlt, (by omega : q.unpair.1 ≤ s)]
    · by_cases heq : q.unpair.1 = s
      · simp only [f, ite_eq_right hlt, ite_eq_left heq]
        rw [← (TuringDegrees.join_odd_reduction (boundedJoin A s) (A s)).2 q.unpair.2]
        simp [boundedJoin, heq]
      · simp only [f, ite_eq_right hlt, ite_eq_right heq]
        rw [← (TuringDegrees.join_even_reduction (boundedJoin A s) (A s)).2 (Nat.pair s 0)]
        change (q.unpair.1 < s + 1 ∧ q.unpair.2 ∈ A q.unpair.1) ↔
          ((Nat.pair s 0).unpair.1 < s ∧ (Nat.pair s 0).unpair.2 ∈ A (Nat.pair s 0).unpair.1)
        simp only [Nat.unpair_pair, lt_self_iff_false, false_and, iff_false]
        rintro ⟨hi,_⟩
        omega
  have hleft : TuringDegrees.Reducible (boundedJoin A s) (boundedJoin A (s + 1)) := by
    let g : ℕ → ℕ := fun q => if q.unpair.1 < s then q else Nat.pair (s + 1) 0
    have hg : Primrec g := Primrec.ite (Primrec.nat_lt.comp hi (Primrec.const s))
      Primrec.id (Primrec.const (Nat.pair (s + 1) 0))
    apply TuringDegrees.manyOne_imp_reducible
    refine ⟨g, hg.to_comp, ?_⟩
    intro q
    by_cases hlt : q.unpair.1 < s
    · simp [g, boundedJoin, hlt, (by omega : q.unpair.1 ≤ s)]
    · simp [g, boundedJoin, hlt, Nat.unpair_pair]
  have hright : TuringDegrees.Reducible (A s) (boundedJoin A (s + 1)) := by
    apply TuringDegrees.manyOne_imp_reducible
    refine ⟨Nat.pair s, (Primrec₂.natPair.comp (Primrec.const s) Primrec.id).to_comp, ?_⟩
    intro x
    simp [boundedJoin, Nat.unpair_pair]
  exact ⟨hforward, (TuringDegrees.join_reducible_iff _ _ _).mpr ⟨hleft,hright⟩⟩

theorem finite_join_presentations (A : ℕ → Set ℕ) (s : ℕ) :
    TuringDegrees.Equivalent (boundedJoin A s) (finiteJoin A s) := by
  induction s with
  | zero =>
      have hz : boundedJoin A 0 = ∅ := by ext q; simp [boundedJoin]
      rw [hz, finiteJoin]
      exact ⟨TuringDegrees.reducible_refl _, TuringDegrees.reducible_refl _⟩
  | succ s ih =>
      have hs := bounded_join_successor A s
      have hF := (TuringDegrees.join_reducible_iff (finiteJoin A s) (A s) _).mp
        (TuringDegrees.reducible_refl (TuringDegrees.join (finiteJoin A s) (A s)))
      have hJ := (TuringDegrees.join_reducible_iff (boundedJoin A s) (A s) _).mp
        (TuringDegrees.reducible_refl (TuringDegrees.join (boundedJoin A s) (A s)))
      constructor
      · apply TuringDegrees.reducible_trans hs.1
        exact (TuringDegrees.join_reducible_iff _ _ _).mpr
          ⟨TuringDegrees.reducible_trans ih.1 hF.1, hF.2⟩
      · apply TuringDegrees.reducible_trans ?_ hs.2
        exact (TuringDegrees.join_reducible_iff _ _ _).mpr
          ⟨TuringDegrees.reducible_trans ih.2 hJ.1, hJ.2⟩

theorem finite_join_chain_bound (A : ℕ → Set ℕ)
    (h : ∀ i, TuringDegrees.Reducible (A i) (A (i + 1))) (s : ℕ) :
    TuringDegrees.Reducible (finiteJoin A s) (A (s - 1)) ∧
      TuringDegrees.Reducible (boundedJoin A s) (A (s - 1)) := by
  have hc {i j : ℕ} (hij : i ≤ j) : TuringDegrees.Reducible (A i) (A j) := by
    induction j, hij using Nat.le_induction with
    | base => exact TuringDegrees.reducible_refl _
    | succ j hij ih => exact TuringDegrees.reducible_trans ih (h j)
  have hf : TuringDegrees.Reducible (finiteJoin A s) (A (s - 1)) :=
    (finite_join_universal A s _).mpr (fun i hi => hc (by omega))
  exact ⟨hf, TuringDegrees.reducible_trans (finite_join_presentations A s).1 hf⟩

end
end Lemmatheca.ComputabilityTheory.ExactPairs
