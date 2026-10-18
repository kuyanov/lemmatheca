import Lemmatheca.MathematicalLogic.ElementaryChains
import Lemmatheca.MathematicalLogic.QuantifierEliminationShared
import Mathlib.Tactic

/-! Isomorphic integer tails whose inclusions fail to be elementary. -/

namespace Lemmatheca.Entry.ElementaryChains

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.MathematicalLogic.ElementaryChains

local instance integerOrderStructure : binaryRelLanguage.Structure ℤ :=
  binaryRelStructure ℤ (fun a b => a < b)

def integerTail (n : ℕ) : binaryRelLanguage.Substructure ℤ where
  carrier := {z | -(n : ℤ) ≤ z}
  fun_mem f := Empty.elim f

private theorem integerTail_monotone : Monotone integerTail := by
  intro i j hij z hz
  change -(i : ℤ) ≤ z at hz
  change -(j : ℤ) ≤ z
  omega

def tailLeast (n : ℕ) : integerTail n :=
  ⟨-(n : ℤ), by change -(n : ℤ) ≤ -(n : ℤ); exact le_rfl⟩

abbrev integerTails : IncreasingChain binaryRelLanguage ℤ where
  stage := ⟨integerTail, integerTail_monotone⟩
  nonempty_stage n := ⟨-(n : ℤ), by change -(n : ℤ) ≤ -(n : ℤ); exact le_rfl⟩

/-- A witness to having something strictly smaller than the single parameter. -/
def hasPredecessor : binaryRelLanguage.BoundedFormula Empty 1 :=
  (.rel .rel ![.var (.inr 1), .var (.inr 0)] :
    binaryRelLanguage.BoundedFormula Empty 2).ex

/-- The universal formula asserting that no element is below the parameter. -/
def isLeast : binaryRelLanguage.BoundedFormula Empty 1 :=
  (.rel .rel ![.var (.inr 1), .var (.inr 0)] :
    binaryRelLanguage.BoundedFormula Empty 2).not.all

def hasLeast : binaryRelLanguage.Sentence := isLeast.ex

theorem isLeast_isUniversal : isLeast.IsUniversal := by
  apply BoundedFormula.IsUniversal.all
  exact (BoundedFormula.IsAtomic.rel _ _).isQF.not.isUniversal

theorem hasPredecessor_isExistential : hasPredecessor.IsExistential := by
  apply BoundedFormula.IsExistential.ex
  exact (BoundedFormula.IsAtomic.rel _ _).isQF.isExistential

theorem integer_tail_shift (n : ℕ) :
    ∃ e : integerTail n ≃[binaryRelLanguage] integerTail 0,
      (∀ z, (e z : ℤ) = (z : ℤ) + n) ∧
      (∀ z, (e.symm z : ℤ) = (z : ℤ) - n) := by
  let e : integerTail n ≃ integerTail 0 :=
    { toFun := fun z => ⟨(z : ℤ) + n, by
        have hz := z.property
        change -(n : ℤ) ≤ (z : ℤ) at hz
        change -(0 : ℤ) ≤ (z : ℤ) + n
        omega⟩
      invFun := fun z => ⟨(z : ℤ) - n, by
        have hz := z.property
        change -(0 : ℤ) ≤ (z : ℤ) at hz
        change -(n : ℤ) ≤ (z : ℤ) - n
        omega⟩
      left_inv := by intro z; apply Subtype.ext; dsimp; omega
      right_inv := by intro z; apply Subtype.ext; dsimp; omega }
  let E : integerTail n ≃[binaryRelLanguage] integerTail 0 :=
    { toEquiv := e
      map_fun' := fun f => Empty.elim f
      map_rel' := by
        intro k R a
        cases R
        change (a 0 : ℤ) + n < (a 1 : ℤ) + n ↔ (a 0 : ℤ) < (a 1 : ℤ)
        omega }
  exact ⟨E, fun _ => rfl, fun _ => rfl⟩

theorem integer_tails_union : integerTails.unionSubstructure = ⊤ := by
  apply top_unique
  intro z _
  apply (Substructure.mem_iSup_of_directed integerTails.stage.monotone.directed_le).mpr
  obtain ⟨n, hn⟩ := exists_nat_ge (-z)
  refine ⟨n, ?_⟩
  change -(n : ℤ) ≤ z
  omega

private theorem tail_isLeast_realize (n : ℕ) (a : integerTail n) :
    isLeast.Realize default ![a] ↔ ∀ b : integerTail n, (a : ℤ) ≤ (b : ℤ) := by
  unfold isLeast
  rw [BoundedFormula.realize_all]
  change (∀ b : integerTail n, ¬ (b : ℤ) < (a : ℤ)) ↔ _
  simp only [not_lt]

private theorem tail_hasPredecessor_realize (n : ℕ) (a : integerTail n) :
    hasPredecessor.Realize default ![a] ↔ ∃ b : integerTail n, (b : ℤ) < (a : ℤ) := by
  unfold hasPredecessor
  rw [BoundedFormula.realize_ex]
  rfl

theorem integer_tail_has_least (n : ℕ) : integerTail n ⊨ hasLeast := by
  rw [Sentence.Realize, Formula.Realize, hasLeast, BoundedFormula.realize_ex]
  refine ⟨tailLeast n, ?_⟩
  have hx : Fin.snoc (default : Fin 0 → integerTail n) (tailLeast n) = ![tailLeast n] := by
    funext k
    fin_cases k
    rfl
  rw [hx]
  apply (tail_isLeast_realize n (tailLeast n)).mpr
  intro b
  exact b.property

theorem integers_no_least : ¬ (ℤ ⊨ hasLeast) := by
  intro h
  rw [Sentence.Realize, Formula.Realize, hasLeast, BoundedFormula.realize_ex] at h
  obtain ⟨z, hz⟩ := h
  unfold isLeast at hz
  have hb := BoundedFormula.realize_all.mp hz (z - 1)
  change ¬ (z - 1 < z) at hb
  exact hb (by omega)

/-- Both failed reverse-preservation directions use the same specified old element. -/
theorem integer_tail_boundaries (n : ℕ) :
    isLeast.Realize default ![tailLeast n] ∧
    ¬ isLeast.Realize default
      ![integerTails.inclusion n (n + 1) (Nat.le_succ n) (tailLeast n)] ∧
    ¬ hasPredecessor.Realize default ![tailLeast n] ∧
    hasPredecessor.Realize default
      ![integerTails.inclusion n (n + 1) (Nat.le_succ n) (tailLeast n)] := by
  have hleast : isLeast.Realize default ![tailLeast n] := by
    apply (tail_isLeast_realize n (tailLeast n)).mpr
    intro b
    exact b.property
  have hnopred : ¬ hasPredecessor.Realize default ![tailLeast n] := by
    rw [tail_hasPredecessor_realize]
    rintro ⟨b, hb⟩
    have hmem := b.property
    change -(n : ℤ) ≤ (b : ℤ) at hmem
    change (b : ℤ) < -(n : ℤ) at hb
    omega
  have hpred : hasPredecessor.Realize default
      ![integerTails.inclusion n (n + 1) (Nat.le_succ n) (tailLeast n)] := by
    apply (tail_hasPredecessor_realize (n + 1) _).mpr
    refine ⟨tailLeast (n + 1), ?_⟩
    change -((n + 1 : ℕ) : ℤ) < -(n : ℤ)
    omega
  refine ⟨hleast, ?_, hnopred, hpred⟩
  rw [tail_isLeast_realize]
  intro h
  have hb := h (tailLeast (n + 1))
  change -(n : ℤ) ≤ -((n + 1 : ℕ) : ℤ) at hb
  omega

/-- No elementary embedding has the underlying map of an adjacent inclusion. -/
theorem integer_tail_inclusion_not_elementary (n : ℕ) :
    ¬ ∃ e : integerTail n ↪ₑ[binaryRelLanguage] integerTail (n + 1),
      (e : integerTail n → integerTail (n + 1)) =
        integerTails.inclusion n (n + 1) (Nat.le_succ n) := by
  rintro ⟨e, he⟩
  have h := e.map_boundedFormula hasPredecessor default ![tailLeast n]
  have hv : e ∘ (default : Empty → integerTail n) =
      (default : Empty → integerTail (n + 1)) := Subsingleton.elim _ _
  have hx : e ∘ ![tailLeast n] =
      ![integerTails.inclusion n (n + 1) (Nat.le_succ n) (tailLeast n)] := by
    rw [he]
    funext k
    fin_cases k
    rfl
  rw [hv, hx] at h
  exact (integer_tail_boundaries n).2.2.1
    (h.mp (integer_tail_boundaries n).2.2.2)

section RationalTails

local instance rationalOrderStructure : binaryRelLanguage.Structure ℚ :=
  binaryRelStructure ℚ (fun a b => a < b)

/-- The open rational tail above the negative integer indexed by n. -/
def rationalTail (n : ℕ) : binaryRelLanguage.Substructure ℚ where
  carrier := {q | -(n : ℚ) < q}
  fun_mem f := Empty.elim f

private theorem rationalTail_monotone : Monotone rationalTail := by
  intro i j hij q hq
  change -(i : ℚ) < q at hq
  change -(j : ℚ) < q
  have h : (i : ℚ) ≤ (j : ℚ) := by exact_mod_cast hij
  linarith

private theorem rationalTail_nonempty (n : ℕ) : (rationalTail n : Set ℚ).Nonempty := by
  refine ⟨1, ?_⟩
  change -(n : ℚ) < 1
  have hn : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
  linarith

/-- The increasing sequence of open rational tails. -/
abbrev rationalTails : IncreasingChain binaryRelLanguage ℚ where
  stage := ⟨rationalTail, rationalTail_monotone⟩
  nonempty_stage := rationalTail_nonempty

private theorem rationalTail_model (n : ℕ) :
    rationalTail n ⊨ Lemmatheca.MathematicalLogic.QuantifierElimination.Shared.strictDloTheory := by
  apply Lemmatheca.MathematicalLogic.QuantifierElimination.Shared.model_strictDloTheory_iff.mpr
  change Lemmatheca.MathematicalLogic.QuantifierElimination.DloAxioms
    (fun a b : rationalTail n => (a : ℚ) < (b : ℚ))
  constructor
  · intro a
    exact lt_irrefl (a : ℚ)
  · intro a b c hab hbc
    exact lt_trans hab hbc
  · intro a b
    rcases lt_trichotomy (a : ℚ) (b : ℚ) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr h)
  · intro a b hab
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    refine ⟨⟨c, ?_⟩, hac, hcb⟩
    exact lt_trans a.property hac
  · intro a
    have ha : -(n : ℚ) < (a : ℚ) := a.property
    obtain ⟨b, hb, hba⟩ := exists_between ha
    exact ⟨⟨b, hb⟩, hba⟩
  · intro a
    refine ⟨⟨(a : ℚ) + 1, ?_⟩, ?_⟩
    · have ha := a.property
      change -(n : ℚ) < (a : ℚ) at ha
      change -(n : ℚ) < (a : ℚ) + 1
      linarith
    · change (a : ℚ) < (a : ℚ) + 1
      linarith

/-- The rational tails are elementary under their actual inclusions. -/
theorem rational_tails_elementary : rationalTails.IsElementary := by
  intro i j hij
  have := rationalTail_model i
  have := rationalTail_model j
  have : Nonempty (rationalTail i) := (rationalTail_nonempty i).to_subtype
  have : Nonempty (rationalTail j) := (rationalTail_nonempty j).to_subtype
  exact Lemmatheca.MathematicalLogic.QuantifierElimination.Shared.strictDlo_embedding_isElementary
    (rationalTails.inclusion i j hij)

/-- The rational tails exhaust the rational strict order. -/
theorem rational_tails_union : rationalTails.unionSubstructure = ⊤ := by
  apply top_unique
  intro q _
  apply (Substructure.mem_iSup_of_directed rationalTails.stage.monotone.directed_le).mpr
  obtain ⟨n, hn⟩ := exists_nat_gt (-q)
  refine ⟨n, ?_⟩
  change -(n : ℚ) < q
  linarith

/-- Every rational tail is elementary in the rational strict-order structure. -/
theorem rational_tail_elementary (n : ℕ) : (rationalTail n).IsElementary := by
  have := rationalTail_model n
  have : Nonempty (rationalTail n) := (rationalTail_nonempty n).to_subtype
  have : ℚ ⊨ Lemmatheca.MathematicalLogic.QuantifierElimination.Shared.strictDloTheory :=
    Lemmatheca.MathematicalLogic.QuantifierElimination.Shared.model_strictDloTheory
  obtain ⟨e, he⟩ :=
    Lemmatheca.MathematicalLogic.QuantifierElimination.Shared.strictDlo_embedding_isElementary
      (rationalTail n).subtype
  intro k φ a
  convert e.map_formula φ a using 1
  rw [he]
  rfl

end RationalTails

end Lemmatheca.Entry.ElementaryChains
