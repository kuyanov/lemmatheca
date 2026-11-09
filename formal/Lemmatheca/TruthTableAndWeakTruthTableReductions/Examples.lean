import Lemmatheca.TruthTableAndWeakTruthTableReductions.Closure
import Lemmatheca.OracleComputation.Examples

/-! The exclusive-or table and a bounded-query program partial under other oracles. -/
namespace Lemmatheca.Entry.TruthTableAndWeakTruthTableReductions

open Lemmatheca.ComputabilityTheory
open OracleComputation UniversalComputation StrongReductions PostsTheorem

noncomputable section

open Classical

def exclusiveOrSet (B : Set ℕ) : Set ℕ :=
  {x | (x ∈ B ∧ x + 1 ∉ B) ∨ (x ∉ B ∧ x + 1 ∈ B)}

def exclusiveOrData : TableData :=
  ⟨fun x => x + 2, fun x w =>
    if FiniteSequenceCoding.length w = x + 2 ∧
      (∀ b ∈ FiniteSequenceCoding.decode w, b = 0 ∨ b = 1)
    then (beta w x + beta w (x + 1)) % 2 else 0⟩

theorem exclusive_or_scheme (B : Set ℕ) : Presents exclusiveOrData (exclusiveOrSet B) B := by
  have hlen : PrimrecPred (fun p : ℕ × ℕ => FiniteSequenceCoding.length p.2 = p.1 + 2) :=
    Primrec.eq.comp (FiniteSequenceCoding.primrec_length.comp Primrec.snd)
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
  have hvalid : PrimrecPred (fun p : ℕ × ℕ =>
      ∀ b ∈ FiniteSequenceCoding.decode p.2, b = 0 ∨ b = 1) :=
    ComputableTreesAndPaths.valid_code_primitive.comp Primrec.snd
  have hsum : Primrec (fun p : ℕ × ℕ => (beta p.2 p.1 + beta p.2 (p.1 + 1)) % 2) :=
    Primrec.nat_mod.comp
      (Primrec.nat_add.comp (beta_primitive.comp Primrec.snd Primrec.fst)
        (beta_primitive.comp Primrec.snd (Primrec.succ.comp Primrec.fst))) (Primrec.const 2)
  have htable : Computable (fun p : ℕ × ℕ => exclusiveOrData.table p.1 p.2) :=
    (Primrec.ite (hlen.and hvalid) hsum (Primrec.const 0)).to_comp
  refine ⟨⟨?_, htable, ?_⟩, ?_⟩
  · exact (Primrec.nat_add.comp Primrec.id (Primrec.const 2)).to_comp
  · intro x w
    dsimp only [exclusiveOrData]
    split_ifs
    · exact Nat.mod_two_eq_zero_or_one _
    · exact Or.inl rfl
  · intro x
    have hl := (prefixCode_spec B (x + 2)).1
    have hv := ComputableTreesAndPaths.prefix_code_valid B (x + 2)
    have h0 := (prefixCode_spec B (x + 2)).2 x (by omega)
    have h1 := (prefixCode_spec B (x + 2)).2 (x + 1) (by omega)
    dsimp only [exclusiveOrData]
    rw [ite_eq_left ⟨hl, hv⟩, h0, h1]
    by_cases hx : x ∈ B <;> by_cases hy : x + 1 ∈ B <;>
      simp [indicator, exclusiveOrSet, hx, hy]

theorem exclusive_or_bits (i j : ℕ) (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1) :
    (i + j) % 2 = 1 ↔ i ≠ j := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> decide

def partialOneQuery : Code :=
  .comp (.prec .zero Lemmatheca.Entry.OracleComputation.never)
    (.pair .zero (.comp .query .zero))

theorem partial_one_query_eval (C : Set ℕ) (x : ℕ) :
    eval C partialOneQuery x = if 0 ∈ C then Part.none else Part.some 0 := by
  have hpair : eval C (.pair .zero (.comp .query .zero)) x =
      Part.some (Nat.pair 0 (indicator (fun n => n ∈ C) 0)) := by
    simp [eval]
  change (eval C (.pair .zero (.comp .query .zero)) x).bind
    (eval C (.prec .zero Lemmatheca.Entry.OracleComputation.never)) = _
  rw [hpair, Part.bind_some]
  by_cases h : 0 ∈ C
  · simp only [ite_eq_left h]
    have hb : indicator (fun n => n ∈ C) 0 = 1 := by simp [indicator, h]
    rw [hb, show 1 = 0 + 1 from rfl, eval_prec_succ, eval_prec_zero]
    have hz : eval C Code.zero 0 = Part.some 0 := rfl
    rw [hz, Part.bind_some]
    exact (Lemmatheca.Entry.OracleComputation.partial_replacement_fails C C x).1 _
  · simp only [ite_eq_right h]
    have hb : indicator (fun n => n ∈ C) 0 = 0 := by simp [indicator, h]
    rw [hb, eval_prec_zero]
    rfl

theorem partial_one_query_trace (x : ℕ) :
    Derives partialOneQuery x [(0, 0)] 0 ∧ Consistent (∅ : Set ℕ) [(0, 0)] ∧
      useBound [(0, 0)] = 1 := by
  have hq : Derives (.comp .query .zero) x [(0, 0)] 0 := by
    simpa using (Derives.comp (Derives.zero x) (Derives.query 0 0 (Or.inl rfl)))
  have hp : Derives (.pair .zero (.comp .query .zero)) x [(0, 0)] (Nat.pair 0 0) := by
    simpa using (Derives.pair (Derives.zero x) hq)
  have hr : Derives (.prec .zero Lemmatheca.Entry.OracleComputation.never)
      (Nat.pair 0 0) [] 0 := Derives.prec_zero (Derives.zero 0)
  refine ⟨?_, ?_, ?_⟩
  · simpa [partialOneQuery] using (Derives.comp hp hr)
  · simp [Consistent, indicator]
  · simp [useBound, querySet]

theorem partial_one_query_reduction :
    BoundedReduction partialOneQuery (fun _ => 1) ∅ ∅ := by
  refine ⟨Computable.const 1, fun x => ?_⟩
  obtain ⟨ht, hc, hu⟩ := partial_one_query_trace x
  exact ⟨[(0, 0)], by simpa [indicator] using ht, hc, hu.le⟩

theorem partial_one_query_not_total :
    (∀ x, eval ({0} : Set ℕ) partialOneQuery x = Part.none) ∧
      ¬ AllOracleTotal partialOneQuery := by
  have hdiv : ∀ x, eval ({0} : Set ℕ) partialOneQuery x = Part.none := by
    intro x
    simp [partial_one_query_eval]
  refine ⟨hdiv, fun ht => ?_⟩
  have hd := ht ({0} : Set ℕ) 0
  rw [hdiv 0] at hd
  exact hd

end
end Lemmatheca.Entry.TruthTableAndWeakTruthTableReductions
