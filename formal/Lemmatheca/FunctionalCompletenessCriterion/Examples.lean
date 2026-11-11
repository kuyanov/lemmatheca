import Lemmatheca.FunctionalCompletenessCriterion.Completeness

namespace Lemmatheca.Entry.FunctionalCompletenessCriterion

open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion

def negOp : Operation := ⟨1, unaryNeg⟩

def andOp : Operation := ⟨2, binaryAnd⟩

def xorOp : Operation := ⟨2, fun row => Bool.xor (row 0) (row 1)⟩

def nandOp : Operation := ⟨2, fun row => !(row 0 && row 1)⟩

def constantOp (b : Bool) : Operation := ⟨0, fun _ => b⟩

def nandBasis : Set Operation := {nandOp}

def xorNegBasis : Set Operation := {xorOp, negOp}

def negAndBasis : Set Operation := {negOp, andOp}

private theorem and_not_affine : ¬ Affine binaryAnd := by
  intro h
  have he := (affine_iff_constant_differences binaryAnd).mp h
    0 (row2 false false) (row2 true true)
  have h0 : difference binaryAnd 0 (row2 false false) = false := by decide
  have h1 : difference binaryAnd 0 (row2 true true) = true := by decide
  rw [h0, h1] at he
  contradiction

theorem nand_failures :
    ¬ PreservesZero nandOp.table ∧ ¬ PreservesOne nandOp.table ∧
    ¬ Monotone nandOp.table ∧ ¬ SelfDual nandOp.table ∧ ¬ Affine nandOp.table := by
  refine ⟨by simp [PreservesZero, nandOp], by simp [PreservesOne, nandOp], ?_, ?_, ?_⟩
  · intro h
    have he := h (a := row2 false false) (b := row2 true true)
      (fun i => by simp [row2])
    change true ≤ false at he
    exact (by decide : ¬ ((true : Bool) ≤ false)) he
  · intro h
    have he := h (row2 false true)
    simp [nandOp, row2] at he
  · intro h
    have he := (affine_iff_constant_differences (n := 2) nandOp.table).mp h
      0 (row2 false false) (row2 true true)
    have h0 : difference (n := 2) nandOp.table 0 (row2 false false) = false := by decide
    have h1 : difference (n := 2) nandOp.table 0 (row2 true true) = true := by decide
    rw [h0, h1] at he
    contradiction

theorem nand_positive_not_full : PositiveComplete nandBasis ∧ ¬ FullComplete nandBasis := by
  have hpos : PositiveComplete nandBasis := by
    apply (post_criterion nandBasis).mpr
    rcases nand_failures with ⟨h0, h1, hm, hd, ha⟩
    exact ⟨⟨nandOp, by simp [nandBasis], h0⟩,
      ⟨nandOp, by simp [nandBasis], h1⟩,
      ⟨nandOp, by simp [nandBasis], hm⟩,
      ⟨nandOp, by simp [nandBasis], hd⟩,
      ⟨nandOp, by simp [nandBasis], ha⟩⟩
  refine ⟨hpos, ?_⟩
  intro hfull
  obtain ⟨g, hg, hzero⟩ := (closed_iff_nullary nandBasis).mp
    ((full_iff_positive_closed nandBasis).mp hfull).2
  have he : g = nandOp := by simpa [nandBasis] using hg
  subst g
  change 2 = 0 at hzero
  cases hzero

theorem nand_with_constant_full (b : Bool) : FullComplete (insert (constantOp b) nandBasis) := by
  apply (full_criterion_nullary _).mpr
  constructor
  · rcases nand_failures with ⟨h0, h1, hm, hd, ha⟩
    exact ⟨⟨nandOp, by simp [nandBasis], h0⟩,
      ⟨nandOp, by simp [nandBasis], h1⟩,
      ⟨nandOp, by simp [nandBasis], hm⟩,
      ⟨nandOp, by simp [nandBasis], hd⟩,
      ⟨nandOp, by simp [nandBasis], ha⟩⟩
  · exact ⟨constantOp b, Set.mem_insert _ _, rfl⟩

theorem xor_affine : Affine xorOp.table := by
  refine ⟨false, fun _ => true, ?_⟩
  funext row
  simp [xorOp, affineValue, parity]

theorem neg_affine_selfDual : Affine negOp.table ∧ SelfDual negOp.table := by
  constructor
  · refine ⟨true, fun _ => true, ?_⟩
    funext row
    simp [negOp, unaryNeg, affineValue, parity]
  · intro row
    simp [negOp, unaryNeg]

theorem constant_affine (b : Bool) : Affine (constantOp b).table := by
  refine ⟨b, fun i => Fin.elim0 i, ?_⟩
  funext row
  simp [constantOp, affineValue, parity]

theorem xor_neg_incomplete :
    ¬ PositiveComplete xorNegBasis ∧
      ¬ PositiveComplete (insert (constantOp false) (insert (constantOp true) xorNegBasis)) := by
  have hincomplete (S : Set Operation) (hS : ∀ g ∈ S, Affine g.table) :
      ¬ PositiveComplete S := by
    intro h
    exact and_not_affine (generated_affine binaryAnd hS (h 2 (by decide) binaryAnd))
  constructor
  · apply hincomplete
    intro g hg
    simp only [xorNegBasis, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact xor_affine
    · exact neg_affine_selfDual.1
  · apply hincomplete
    intro g hg
    simp only [xorNegBasis, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact constant_affine false
    · exact constant_affine true
    · exact xor_affine
    · exact neg_affine_selfDual.1

theorem and_properties :
    PreservesZero andOp.table ∧ PreservesOne andOp.table ∧ Monotone andOp.table ∧
      ¬ SelfDual andOp.table ∧ ¬ Affine andOp.table := by
  refine ⟨by simp [PreservesZero, andOp, binaryAnd],
    by simp [PreservesOne, andOp, binaryAnd], ?_, ?_, and_not_affine⟩
  · change Monotone (binaryAnd : TruthFunction 2)
    intro a b hab
    change (a 0 && a 1) ≤ (b 0 && b 1)
    apply Bool.le_iff_imp.mpr
    intro ha
    change (a 0 && a 1) = true at ha
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at ha
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    exact ⟨(Bool.le_iff_imp.mp (hab 0)) ha.1,
      (Bool.le_iff_imp.mp (hab 1)) ha.2⟩
  · intro h
    have he := h (row2 false true)
    simp [andOp, binaryAnd, row2] at he

theorem neg_and_different_witnesses :
    EscapesAll negAndBasis ∧ PositiveComplete negAndBasis ∧
      ¬ ∃ g ∈ negAndBasis, ¬ PreservesZero g.table ∧ ¬ PreservesOne g.table ∧
        ¬ Monotone g.table ∧ ¬ SelfDual g.table ∧ ¬ Affine g.table := by
  have h0 : ¬ PreservesZero negOp.table := by simp [PreservesZero, negOp, unaryNeg]
  have h1 : ¬ PreservesOne negOp.table := by simp [PreservesOne, negOp, unaryNeg]
  have hm : ¬ Monotone negOp.table := by
    intro h
    have he := h (a := fun _ => false) (b := fun _ => true) (fun _ => Bool.false_le true)
    change true ≤ false at he
    exact (by decide : ¬ ((true : Bool) ≤ false)) he
  have he : EscapesAll negAndBasis :=
    ⟨⟨negOp, by simp [negAndBasis], h0⟩,
      ⟨negOp, by simp [negAndBasis], h1⟩,
      ⟨negOp, by simp [negAndBasis], hm⟩,
      ⟨andOp, by simp [negAndBasis], and_properties.2.2.2.1⟩,
      ⟨andOp, by simp [negAndBasis], and_properties.2.2.2.2⟩⟩
  refine ⟨he, (post_criterion negAndBasis).mpr he, ?_⟩
  rintro ⟨g, hg, hg0, _, _, hgd, _⟩
  simp only [negAndBasis, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact hgd neg_affine_selfDual.2
  · exact hg0 and_properties.1

end Lemmatheca.Entry.FunctionalCompletenessCriterion
