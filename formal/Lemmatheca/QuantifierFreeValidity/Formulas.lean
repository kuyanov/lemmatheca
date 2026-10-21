import Lemmatheca.QuantifierFreeValidity.Literals
import Lemmatheca.PropositionalLogic.Propositional

/-! Propositional skeletons of actual shared formulas and finite realizable-row search. -/
namespace Lemmatheca.MathematicalLogic.QuantifierFreeValidity

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional

universe u v w
variable {L : Language.{u, v}}

/-- Remove the two empty variable types from a term in a sentence atom. -/
def groundTerm (t : L.Term (Empty ⊕ Fin 0)) : GroundEquality.GroundTerm L :=
  t.relabel (Sum.elim Empty.elim Fin.elim0)

/-- Total recursion on actual sentences; the quantified case is irrelevant under IsQF. -/
def skeleton : L.Sentence → PropFormula (Atom L)
  | .falsum => .falsum
  | .equal t s => .atom (.equal (groundTerm t) (groundTerm s))
  | .rel R ts => .atom (.rel R (fun i => groundTerm (ts i)))
  | .imp A B => .impl (skeleton A) (skeleton B)
  | .all _ => .falsum

/-- Rebuild a shared first-order sentence from its propositional combination of atoms. -/
def fromSkeleton : PropFormula (Atom L) → L.Sentence
  | .atom a => a.formula
  | .falsum => .falsum
  | .neg A => (fromSkeleton A).not
  | .conj A B => fromSkeleton A ⊓ fromSkeleton B
  | .disj A B => fromSkeleton A ⊔ fromSkeleton B
  | .impl A B => (fromSkeleton A).imp (fromSkeleton B)

theorem fromSkeleton_qf (B : PropFormula (Atom L)) : (fromSkeleton B).IsQF := by
  induction B with
  | atom a => exact atom_formula_qf a
  | falsum => exact BoundedFormula.isQF_bot
  | neg B ih => exact ih.not
  | conj B C ihB ihC => exact ihB.inf ihC
  | disj B C ihB ihC => exact ihB.sup ihC
  | impl B C ihB ihC => exact ihB.imp ihC

private theorem groundTerm_recover (t : L.Term (Empty ⊕ Fin 0)) :
    (groundTerm t).relabel Sum.inl = t := by
  rw [groundTerm, Term.relabel_relabel]
  have h : ((Sum.inl : Empty → Empty ⊕ Fin 0) ∘ Sum.elim Empty.elim Fin.elim0) = id := by
    funext x
    rcases x with e | i
    · exact e.elim
    · exact Fin.elim0 i
  rw [h, Term.relabel_id]

theorem skeleton_roundtrip (A : L.Sentence) (hA : A.IsQF) : fromSkeleton (skeleton A) = A := by
  induction hA with
  | falsum => rw [skeleton.eq_1]; rfl
  | of_isAtomic h =>
    cases h with
    | equal t s => simp only [Term.bdEqual]; rw [skeleton.eq_2]; simp only [fromSkeleton, Atom.formula, groundTerm_recover]
    | rel R ts => simp only [Relations.boundedFormula]; rw [skeleton.eq_3]; simp only [fromSkeleton, Atom.formula, groundTerm_recover]
  | imp hB hC ihB ihC => simp only [skeleton.eq_4, fromSkeleton, ihB, ihC]

/-- The actual atomic truth valuation, used in correctness proofs, never by the algorithm. -/
noncomputable def truthValuation (M : Type w) [L.Structure M] : Atom L → Bool :=
  fun a => @decide (a.Realize M) (Classical.propDecidable _)

private theorem fromSkeleton_truth (B : PropFormula (Atom L)) (M : Type w) [L.Structure M] :
    (fromSkeleton B).Realize M ↔ Propositional.eval (truthValuation M) B = true := by
  classical
  induction B with
  | atom a => exact decide_eq_true_iff.symm
  | falsum => simp [fromSkeleton, Sentence.Realize, Formula.Realize, BoundedFormula.Realize, Propositional.eval]
  | neg B ih =>
    change ¬(fromSkeleton B).Realize M ↔ (!Propositional.eval (truthValuation M) B) = true
    rw [ih]
    cases Propositional.eval (truthValuation M) B <;> decide
  | conj B C ihB ihC =>
    rw [fromSkeleton.eq_4, Sentence.realize_inf, ihB, ihC]
    change (_ ∧ _) ↔ (Propositional.eval (truthValuation M) B && Propositional.eval (truthValuation M) C) = true
    cases Propositional.eval (truthValuation M) B <;> cases Propositional.eval (truthValuation M) C <;> decide
  | disj B C ihB ihC =>
    rw [fromSkeleton.eq_5, Sentence.realize_sup, ihB, ihC]
    change (_ ∨ _) ↔ (Propositional.eval (truthValuation M) B || Propositional.eval (truthValuation M) C) = true
    cases Propositional.eval (truthValuation M) B <;> cases Propositional.eval (truthValuation M) C <;> decide
  | impl B C ihB ihC =>
    change ((fromSkeleton B).Realize M → (fromSkeleton C).Realize M) ↔ _
    rw [ihB, ihC]
    change (_ → _) ↔ (!Propositional.eval (truthValuation M) B || Propositional.eval (truthValuation M) C) = true
    cases Propositional.eval (truthValuation M) B <;> cases Propositional.eval (truthValuation M) C <;> decide

theorem skeleton_truth (A : L.Sentence) (hA : A.IsQF) (M : Type w) [L.Structure M] :
    A.Realize M ↔ Propositional.eval (truthValuation M) (skeleton A) = true := by
  have h := fromSkeleton_truth (skeleton A) M
  rw [skeleton_roundtrip A hA] at h
  exact h

variable [∀ n, DecidableEq (L.Functions n)] [∀ n, DecidableEq (L.Relations n)]

/-- Every atom contributes one signed demand, including its negative sign when false. -/
def rowProblem (S : Finset (Atom L)) (b : Atom L → Bool) : Problem L :=
  S.image (fun a => (b a, a))

theorem rowProblem_truth (S : Finset (Atom L)) (b : Atom L → Bool)
    (M : Type w) [L.Structure M] :
    Satisfies (rowProblem S b) M ↔ ∀ a ∈ S, (a.Realize M ↔ b a = true) := by
  classical
  have hs : Satisfies (rowProblem S b) M ↔ ∀ a ∈ S, (literalFormula (b a, a)).Realize M := by
    simp [Satisfies, rowProblem]
  rw [hs]
  apply forall_congr' fun a => forall_congr' fun _ha => ?_
  rw [literal_truth]
  cases b a <;> simp

theorem actual_row_satisfies (S : Finset (Atom L)) (M : Type w) [L.Structure M] :
    Satisfies (rowProblem S (truthValuation M)) M := by
  classical
  apply (rowProblem_truth S _ M).mpr
  intro a _ha
  simp [truthValuation]

theorem skeleton_truth_of_row (A : L.Sentence) (hA : A.IsQF) (b : Atom L → Bool)
    (M : Type w) [L.Structure M] (hM : Satisfies (rowProblem (Propositional.atoms (skeleton A)) b) M) :
    A.Realize M ↔ Propositional.eval b (skeleton A) = true := by
  classical
  have hv := (rowProblem_truth _ b M).mp hM
  have he : Propositional.eval (truthValuation M) (skeleton A) =
      Propositional.eval b (skeleton A) := by
    apply Propositional.eval_congr
    intro a ha
    apply Bool.eq_iff_iff.mpr
    simpa [truthValuation] using hv a ha
  rw [skeleton_truth A hA M, he]

/-- All distinct ground subterms occurring in the input formula. -/
def formulaSupport (A : L.Sentence) : Finset (GroundEquality.GroundTerm L) :=
  (Propositional.atoms (skeleton A)).biUnion Atom.subterms

theorem rowProblem_support (S : Finset (Atom L)) (b : Atom L → Bool) :
    support (rowProblem S b) = S.biUnion Atom.subterms := by
  ext t
  simp only [support, rowProblem, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨l, ⟨a, ha, rfl⟩, ht⟩
    exact ⟨a, ha, ht⟩
  · rintro ⟨a, ha, ht⟩
    exact ⟨(b a, a), ⟨a, ha, rfl⟩, ht⟩

/-- This finite search uses only syntactic equality, Boolean evaluation and literalTest. -/
def groundTest (A : L.Sentence) : Bool :=
  decide (∃ r ∈ truthTableRows (Propositional.atoms (skeleton A)),
    Propositional.eval (extendRow (Propositional.atoms (skeleton A)) r) (skeleton A) = true ∧
      literalTest (rowProblem (Propositional.atoms (skeleton A))
        (extendRow (Propositional.atoms (skeleton A)) r)) = true)

def GroundHasModel (A : L.Sentence) : Prop :=
  ∃ (M : Type u) (inst : L.Structure M), Nonempty M ∧ @Sentence.Realize L M inst A

/-- Every passing row is realized by exactly its supplied relation-extension model. -/
theorem passing_row_model (A : L.Sentence) (hA : A.IsQF)
    (r : Propositional.atoms (skeleton A) → Bool)
    (hb : Propositional.eval (extendRow _ r) (skeleton A) = true)
    (hc : literalTest (rowProblem (Propositional.atoms (skeleton A)) (extendRow _ r)) = true) :
    let Γ := rowProblem (Propositional.atoms (skeleton A)) (extendRow _ r)
    letI := modelStructure Γ
    A.Realize (Carrier Γ) ∧ Finite (Carrier Γ) ∧
      Nat.card (Carrier Γ) ≤ (formulaSupport A).card + 1 := by
  dsimp
  let Γ := rowProblem (Propositional.atoms (skeleton A)) (extendRow _ r)
  let : L.Structure (Carrier Γ) := modelStructure Γ
  have hΓ : ConflictFree Γ := of_decide_eq_true hc
  refine ⟨(skeleton_truth_of_row A hA _ _ (model_satisfies Γ hΓ)).mpr hb,
    carrier_finite Γ, ?_⟩
  simpa [Γ, rowProblem_support, formulaSupport] using carrier_card_bound Γ

theorem groundTest_complete (A : L.Sentence) (hA : A.IsQF) (M : Type w)
    [L.Structure M] (hM : A.Realize M) : groundTest A = true := by
  classical
  let S := Propositional.atoms (skeleton A)
  let r : S → Bool := fun a => truthValuation (L := L) M a.val
  have he : Propositional.eval (extendRow S r) (skeleton A) =
      Propositional.eval (truthValuation M) (skeleton A) := by
    apply Propositional.eval_congr
    intro a ha
    simp [extendRow, S, r, ha]
  apply decide_eq_true_iff.mpr
  refine ⟨r, Finset.mem_univ _, ?_, ?_⟩
  · rw [he]
    exact (skeleton_truth A hA M).mp hM
  · apply decide_eq_true_iff.mpr
    apply conflict_sound _ M
    apply (rowProblem_truth S _ M).mpr
    intro a ha
    change a ∈ Propositional.atoms (skeleton A) at ha
    simp [extendRow, ha, r, truthValuation]

theorem groundTest_correct (A : L.Sentence) (hA : A.IsQF) :
    groundTest A = true ↔ GroundHasModel A := by
  constructor
  · intro h
    obtain ⟨r, _hr, hb, hc⟩ := of_decide_eq_true h
    let Γ := rowProblem (Propositional.atoms (skeleton A)) (extendRow _ r)
    exact ⟨Carrier Γ, modelStructure Γ, inferInstance, (passing_row_model A hA r hb hc).1⟩
  · rintro ⟨M, inst, _hne, hM⟩
    let : L.Structure M := inst
    exact groundTest_complete A hA M hM

end Lemmatheca.MathematicalLogic.QuantifierFreeValidity
