import Lemmatheca.Entry.SetsAndMaps
import Lemmatheca.SetTheory.EquivalenceRelations
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Equivalence-relations entry: finite and parity examples

`Fin 3` represents {0, 1, 2}; the map and output labels are shared with the
sets-and-maps entry. Parity is the kernel of reduction modulo two. The helper
abbreviations introduce no new mathematical objects beyond these library instances.
-/

namespace Lemmatheca.Entry.EquivalenceRelations

open Lemmatheca.Entry.SetsAndMaps

abbrev finiteSetoid : Setoid (Fin 3) := Setoid.ker diagramMap
abbrev paritySetoid : Setoid ℤ := Setoid.ker (fun n : ℤ => n % 2)

theorem finite_relation_iff (a b : Fin 3) :
    finiteSetoid a b ↔ (a = 0 ∧ b = 0) ∨
      (a ∈ ({1, 2} : Set (Fin 3)) ∧ b ∈ ({1, 2} : Set (Fin 3))) := by
  fin_cases a <;> fin_cases b <;> simp [diagramMap]

theorem parity_distinct_equivalent :
    Int.ModEq 2 (-1) 3 ∧ (-1 : ℤ) ≠ 3 := by
  decide

theorem empty_relation_not_reflexive :
    Std.Symm (fun _ _ : Fin 3 => False) ∧
      IsTrans (Fin 3) (fun _ _ : Fin 3 => False) ∧
      ¬ Std.Refl (fun _ _ : Fin 3 => False) := by
  exact ⟨⟨by simp⟩, ⟨by simp⟩, fun h => h.refl 0⟩

theorem le_relation_not_symmetric :
    Std.Refl ((· ≤ ·) : Fin 3 → Fin 3 → Prop) ∧
      IsTrans (Fin 3) ((· ≤ ·) : Fin 3 → Fin 3 → Prop) ∧
      (0 : Fin 3) ≤ 1 ∧ ¬ (1 : Fin 3) ≤ 0 := by
  exact ⟨inferInstance, inferInstance, by decide, by decide⟩

/-- The looped path 0—1—2 used to test transitivity. -/
def adjacent (a b : Fin 3) : Prop :=
  a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

theorem adjacent_not_transitive :
    Std.Refl adjacent ∧ Std.Symm adjacent ∧
      adjacent 0 1 ∧ adjacent 1 2 ∧ ¬ adjacent 0 2 ∧
      {x | adjacent 0 x} = {0, 1} ∧ {x | adjacent 2 x} = {1, 2} := by
  refine ⟨⟨fun a => Or.inl rfl⟩, ⟨?_⟩, by simp [adjacent],
    by simp [adjacent], by simp [adjacent], ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [adjacent]
  · ext x
    fin_cases x <;> simp [adjacent]
  · ext x
    fin_cases x <;> simp [adjacent]

theorem finite_classes :
    {x | finiteSetoid x 0} = {0} ∧
      {x | finiteSetoid x 1} = {1, 2} ∧
      {x | finiteSetoid x 2} = {1, 2} ∧
      finiteSetoid.classes = {{0}, {1, 2}} := by
  have h0 : {x | finiteSetoid x 0} = {0} := by
    apply Set.ext
    intro x
    change finiteSetoid x 0 ↔ x = 0
    rw [finite_relation_iff]
    simp
  have h1 : {x | finiteSetoid x 1} = {1, 2} := by
    apply Set.ext
    intro x
    change finiteSetoid x 1 ↔ x ∈ ({1, 2} : Set (Fin 3))
    rw [finite_relation_iff]
    simp
  have h2 : {x | finiteSetoid x 2} = {1, 2} := by
    apply Set.ext
    intro x
    change finiteSetoid x 2 ↔ x ∈ ({1, 2} : Set (Fin 3))
    rw [finite_relation_iff]
    simp
  refine ⟨h0, h1, h2, ?_⟩
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases a
    · exact Or.inl h0
    · exact Or.inr h1
    · exact Or.inr h2
  · intro hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact ⟨0, h0.symm⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨1, hs.trans h1.symm⟩

theorem parity_classes :
    (∀ n : ℤ, {x | paritySetoid x n} =
      if Even n then Set.range (fun k : ℤ => 2 * k)
      else Set.range (fun k : ℤ => 2 * k + 1)) ∧
      paritySetoid.classes =
        {Set.range (fun k : ℤ => 2 * k), Set.range (fun k : ℤ => 2 * k + 1)} ∧
      Set.range (fun k : ℤ => 2 * k) ≠ Set.range (fun k : ℤ => 2 * k + 1) := by
  have heven (x : ℤ) : x ∈ Set.range (fun k : ℤ => 2 * k) ↔ Even x := by
    simp [even_iff_exists_two_mul]
  have hodd (x : ℤ) : x ∈ Set.range (fun k : ℤ => 2 * k + 1) ↔ Odd x := by
    simp [odd_iff_exists_bit1]
  have hclass (n : ℤ) : {x | paritySetoid x n} =
      if Even n then Set.range (fun k : ℤ => 2 * k)
      else Set.range (fun k : ℤ => 2 * k + 1) := by
    ext x
    change x % 2 = n % 2 ↔ x ∈ _
    by_cases hn : Even n
    · rw [ite_eq_left hn, heven, Int.even_iff, Int.even_iff.mp hn]
    · rw [ite_eq_right hn, hodd, Int.odd_iff, Int.not_even_iff.mp hn]
  refine ⟨hclass, ?_, ?_⟩
  · ext s
    constructor
    · rintro ⟨n, rfl⟩
      rw [hclass]
      split <;> simp
    · intro hs
      rcases Set.mem_insert_iff.mp hs with rfl | hs
      · exact ⟨0, by simpa using (hclass 0).symm⟩
      · rw [Set.mem_singleton_iff] at hs
        refine ⟨1, hs.trans ?_⟩
        simpa using (hclass 1).symm
  · intro h
    have hzero : (0 : ℤ) ∈ Set.range (fun k : ℤ => 2 * k) := ⟨0, by simp⟩
    rw [h] at hzero
    have : Odd (0 : ℤ) := (hodd 0).mp hzero
    simp at this

theorem parity_classes_infinite :
    (Set.range (fun k : ℤ => 2 * k)).Infinite ∧
      (Set.range (fun k : ℤ => 2 * k + 1)).Infinite := by
  constructor <;> apply Set.infinite_range_of_injective <;>
    intro a b h <;> dsimp at h <;> omega

theorem overlapping_parts_not_partition :
    ¬ Setoid.IsPartition ({{0, 1}, {1, 2}} : Set (Set (Fin 3))) ∧
      ({0, 1} : Set (Fin 3)) ∩ {1, 2} = {1} := by
  constructor
  · intro h
    have hne : ({0, 1} : Set (Fin 3)) ≠ {1, 2} := by
      intro heq
      have hz : (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
      rw [heq] at hz
      norm_num at hz
    have hd : Disjoint ({0, 1} : Set (Fin 3)) {1, 2} :=
      h.pairwiseDisjoint (by simp) (by simp) hne
    have hleft : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := by simp
    have hright : (1 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
    exact (Set.disjoint_left.mp hd) hleft hright
  · ext x
    fin_cases x <;> simp

theorem missing_part_not_partition :
    ¬ Setoid.IsPartition ({{0}, {1}} : Set (Set (Fin 3))) ∧
      (2 : Fin 3) ∉ ⋃₀ ({{0}, {1}} : Set (Set (Fin 3))) := by
  have hmissing : (2 : Fin 3) ∉ ⋃₀ ({{0}, {1}} : Set (Set (Fin 3))) := by simp
  refine ⟨fun h => hmissing ?_, hmissing⟩
  rw [h.sUnion_eq_univ]
  trivial

theorem parity_identity_not_descend :
    Quotient.mk paritySetoid 0 = Quotient.mk paritySetoid 2 ∧
      (0 : ℤ) ≠ 2 ∧
      ¬ ∃ u : Quotient paritySetoid → ℤ, ∀ n, u (Quotient.mk paritySetoid n) = n := by
  have h : Quotient.mk paritySetoid 0 = Quotient.mk paritySetoid 2 :=
    Quotient.sound (by change (0 : ℤ) % 2 = 2 % 2; norm_num)
  refine ⟨h, by decide, ?_⟩
  rintro ⟨u, hu⟩
  have heq := congrArg u h
  rw [hu 0, hu 2] at heq
  norm_num at heq

/-- The proposed parity label, with the specified two-element codomain. -/
def parityLabel (n : ℤ) : Fin 2 := if Even n then 0 else 1

theorem parity_label_descends :
    ∃ v : Quotient paritySetoid → Fin 2,
      (∀ n, v (Quotient.mk paritySetoid n) = parityLabel n) ∧
      v (Quotient.mk paritySetoid 0) = 0 ∧ v (Quotient.mk paritySetoid 1) = 1 := by
  have hlabel : ∀ a b, paritySetoid a b → parityLabel a = parityLabel b := by
    intro a b h
    change a % 2 = b % 2 at h
    simp [parityLabel, Int.even_iff, h]
  refine ⟨Quotient.lift parityLabel hlabel, fun _ => rfl, ?_, ?_⟩ <;>
    norm_num [parityLabel]

theorem parity_successor_descends :
    ∃ s : Quotient paritySetoid → Quotient paritySetoid,
      (∀ n, s (Quotient.mk paritySetoid n) = Quotient.mk paritySetoid (n + 1)) ∧
      s (Quotient.mk paritySetoid 0) = Quotient.mk paritySetoid 1 ∧
      s (Quotient.mk paritySetoid 1) = Quotient.mk paritySetoid 0 ∧
      Function.Involutive s := by
  have hsucc : ∀ {a b : ℤ}, paritySetoid a b → paritySetoid (a + 1) (b + 1) := by
    intro a b h
    exact Int.ModEq.add_right 1 h
  let s : Quotient paritySetoid → Quotient paritySetoid :=
    Quotient.map (sa := paritySetoid) (sb := paritySetoid) (· + 1) (fun {_ _} h => hsucc h)
  refine ⟨s, fun _ => rfl, rfl,
    Quotient.sound (by change (1 + 1 : ℤ) % 2 = 0 % 2; norm_num), ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h n =>
    apply Quotient.sound
    change (n + 1 + 1) % 2 = n % 2
    omega

theorem diagram_fiber_p_and_range :
    diagramMap ⁻¹' {MapLabel.p} = {0} ∧
      Set.range diagramMap = {MapLabel.p, MapLabel.q} := by
  constructor
  · ext x
    fin_cases x <;> simp [diagramMap]
  · ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      fin_cases x <;> simp [diagramMap]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

end Lemmatheca.Entry.EquivalenceRelations
