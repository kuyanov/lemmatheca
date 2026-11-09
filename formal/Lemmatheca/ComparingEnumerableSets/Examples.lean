import Lemmatheca.ComparingEnumerableSets.Classification

/-! Finite-stage streams, finite partial programs, and different constant outputs. -/
namespace Lemmatheca.Entry.ComparingEnumerableSets

open Lemmatheca.ComputabilityTheory
open ComparingEnumerableSets EffectiveEnumerations UniversalComputation

def toyD (s : ℕ) : Set ℕ := if 1 ≤ s then {0} else ∅

def toyE (s : ℕ) : Set ℕ := if 4 ≤ s then {0} else ∅

def toyF (_s : ℕ) : Set ℕ := ∅


private theorem threshold_monotone (a : ℕ) :
    Monotone (fun s : ℕ => if a ≤ s then ({0} : Set ℕ) else ∅) := by
  intro s t hst
  by_cases hs : a ≤ s
  · simp [hs, hs.trans hst]
  · simp [hs]

private theorem threshold_union (a : ℕ) :
    (⋃ s : ℕ, if a ≤ s then ({0} : Set ℕ) else ∅) = {0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    by_cases h : a ≤ s
    · simpa [h] using hs
    · simp [h] at hs
  · intro hx
    exact Set.mem_iUnion.mpr ⟨a, by simpa using hx⟩

theorem toy_stream_contract :
    Monotone toyD ∧ Monotone toyE ∧ Monotone toyF ∧
      (∀ s, (toyD s).Finite ∧ (toyE s).Finite ∧ (toyF s).Finite) ∧
      toyD 2 = {0} ∧ toyE 2 = ∅ ∧ toyF 2 = ∅ ∧
      toyD 4 = {0} ∧ toyE 4 = {0} ∧ toyF 4 = ∅ ∧
      (⋃ s, toyD s) = {0} ∧ (⋃ s, toyE s) = {0} ∧ (⋃ s, toyF s) = ∅ := by
  refine ⟨threshold_monotone 1, threshold_monotone 4, ?_, ?_,
    by simp [toyD], by simp [toyE], rfl,
    by simp [toyD], by simp [toyE], rfl,
    threshold_union 1, threshold_union 4, ?_⟩
  · intro s t _ x hx
    exact hx
  · intro s
    simp only [toyD, toyE, toyF]
    split_ifs <;> simp
  · simp [toyF]

theorem temporary_disagreement_answer :
    (⋃ s, toyD s) ⊆ (⋃ s, toyE s) ∧
      ¬ (⋃ s, toyD s) ⊆ (⋃ s, toyF s) := by
  simp [toyD, toyE, toyF, threshold_union]

def singletonProcedure (x : ℕ) : Part ℕ :=
  if x = 0 then Part.some 0
  else Nat.rfind (fun _ => Part.some (decide ((1 : ℕ) = 0)))

def doubletonProcedure (x : ℕ) : Part ℕ :=
  if x ≤ 1 then Part.some 0
  else Nat.rfind (fun _ => Part.some (decide ((1 : ℕ) = 0)))


private theorem impossible_search_none :
    Nat.rfind (fun _ => Part.some false) = Part.none := by
  apply Part.eq_none_iff'.mpr
  intro hd
  obtain ⟨n, hn, _⟩ := Nat.rfind_dom.mp hd
  simp at hn

theorem singleton_procedure_partial : Nat.Partrec singletonProcedure := by
  have ht : Computable (fun x : ℕ => decide (x = 0)) :=
    Primrec.eq.decide.to_comp.comp Computable.id (Computable.const 0)
  apply Partrec.nat_iff.mp
  exact (Partrec.cond ht (Partrec.const' (Part.some 0)) Partrec.none).of_eq
    (fun x => by simp [singletonProcedure, impossible_search_none])

theorem doubleton_procedure_partial : Nat.Partrec doubletonProcedure := by
  have ht : Computable (fun x : ℕ => decide (x ≤ 1)) :=
    Primrec.nat_le.decide.to_comp.comp Computable.id (Computable.const 1)
  apply Partrec.nat_iff.mp
  exact (Partrec.cond ht (Partrec.const' (Part.some 0)) Partrec.none).of_eq
    (fun x => by simp [doubletonProcedure, impossible_search_none])

noncomputable def singletonIndex : ℕ :=
  (phi_complete singleton_procedure_partial).choose

noncomputable def doubletonIndex : ℕ :=
  (phi_complete doubleton_procedure_partial).choose

theorem finite_indices_evaluation (x : ℕ) :
    phi singletonIndex x = singletonProcedure x ∧
      phi doubletonIndex x = doubletonProcedure x := by
  exact ⟨congrFun (Exists.choose_spec (phi_complete singleton_procedure_partial)) x,
    congrFun (Exists.choose_spec (phi_complete doubleton_procedure_partial)) x⟩

theorem finite_indices_domains :
    indexSet singletonIndex = {0} ∧ indexSet doubletonIndex = {0, 1} := by
  constructor
  · ext x
    change (phi singletonIndex x).Dom ↔ x ∈ ({0} : Set ℕ)
    rw [(finite_indices_evaluation x).1]
    by_cases h : x = 0 <;> simp [singletonProcedure, h, impossible_search_none]
  · ext x
    change (phi doubletonIndex x).Dom ↔ x ∈ ({0, 1} : Set ℕ)
    rw [(finite_indices_evaluation x).2]
    by_cases h : x ≤ 1 <;> simp [doubletonProcedure, h, impossible_search_none] <;> omega

theorem finite_proper_inclusion (a b : ℕ)
    (ha : indexSet a = {0}) (hb : indexSet b = {0, 1}) :
    Nat.pair a b ∈ Inclusion ∧ Nat.pair a b ∉ Equality ∧
      Nat.pair b a ∈ Noninclusion ∧ Nat.pair b a ∈ Inequality := by
  simp only [Noninclusion, Inequality, Set.mem_compl_iff,
    (coded_comparisons a b).1, (coded_comparisons a b).2,
    (coded_comparisons b a).1, (coded_comparisons b a).2, ha, hb]
  norm_num [Set.subset_def, Set.ext_iff]

def oneIndex : ℕ := Encodable.encode (Nat.Partrec.Code.const 1)

theorem constant_domains_answer :
    (∀ x, phi wholeIndex x = Part.some 0 ∧ phi oneIndex x = Part.some 1) ∧
      indexSet wholeIndex = Set.univ ∧ indexSet oneIndex = Set.univ ∧
      Nat.pair wholeIndex oneIndex ∈ Inclusion ∧
      Nat.pair wholeIndex oneIndex ∈ Equality ∧
      Nat.pair oneIndex wholeIndex ∈ Inclusion ∧
      Nat.pair oneIndex wholeIndex ∈ Equality ∧
      phi wholeIndex ≠ phi oneIndex := by
  have hv (x : ℕ) : phi oneIndex x = Part.some 1 := by
    simp [phi, oneIndex, Nat.Partrec.Code.eval_const]
  have hdv : indexSet oneIndex = Set.univ := by
    ext x
    change (phi oneIndex x).Dom ↔ True
    rw [hv]
    simp
  have he : indexSet wholeIndex = indexSet oneIndex := whole_index_domain.trans hdv.symm
  refine ⟨fun x => ⟨whole_index_output x, hv x⟩, whole_index_domain, hdv,
    (coded_comparisons wholeIndex oneIndex).1.mpr he.subset,
    (coded_comparisons wholeIndex oneIndex).2.mpr he,
    (coded_comparisons oneIndex wholeIndex).1.mpr he.symm.subset,
    (coded_comparisons oneIndex wholeIndex).2.mpr he.symm, ?_⟩
  intro h
  have hh := congrFun h 0
  simp only [whole_index_output, hv, Part.some_inj] at hh
  omega

end Lemmatheca.Entry.ComparingEnumerableSets
