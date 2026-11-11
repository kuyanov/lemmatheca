import Lemmatheca.FunctionalCompletenessCriterion.Construction

namespace Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion

open Propositional
universe u

private def termNot {S : Set Operation} {α : Type u}
    (negTerm : Term S (Fin 1)) (t : Term S α) : Term S α :=
  termSubst (fun _ => t) negTerm

private def termAnd {S : Set Operation} {α : Type u}
    (andTerm : Term S (Fin 2)) (s t : Term S α) : Term S α :=
  termSubst (fun i => if i = 0 then s else t) andTerm

def fromFormula {S : Set Operation} {α : Type u}
    (negTerm : Term S (Fin 1)) (andTerm : Term S (Fin 2)) (falseTerm : Term S α) :
    PropFormula α → Term S α
  | .atom a => .atom a
  | .falsum => falseTerm
  | .neg A => termNot negTerm (fromFormula negTerm andTerm falseTerm A)
  | .conj A B => termAnd andTerm (fromFormula negTerm andTerm falseTerm A)
      (fromFormula negTerm andTerm falseTerm B)
  | .disj A B => termNot negTerm (termAnd andTerm
      (termNot negTerm (fromFormula negTerm andTerm falseTerm A))
      (termNot negTerm (fromFormula negTerm andTerm falseTerm B)))
  | .impl A B => termNot negTerm (termAnd andTerm
      (fromFormula negTerm andTerm falseTerm A)
      (termNot negTerm (fromFormula negTerm andTerm falseTerm B)))

noncomputable def dnfTerm {S : Set Operation} {n : ℕ} (hn : 0 < n)
    (negTerm : Term S (Fin 1)) (andTerm : Term S (Fin 2))
    (falseUnaryTerm : Term S (Fin 1)) (f : TruthFunction n) : Term S (Fin n) :=
  fromFormula negTerm andTerm
    (termSubst (fun _ => .atom ⟨0, hn⟩) falseUnaryTerm)
    (dnfFormula (canonicalDnf id f))

theorem fromFormula_eval {S : Set Operation} {α : Type u}
    (negTerm : Term S (Fin 1)) (andTerm : Term S (Fin 2)) (falseTerm : Term S α)
    (hn : ∀ row, termEval row negTerm = unaryNeg row)
    (ha : ∀ row, termEval row andTerm = binaryAnd row)
    (hf : ∀ row, termEval row falseTerm = false)
    (A : PropFormula α) (row : α → Bool) :
    termEval row (fromFormula negTerm andTerm falseTerm A) = Propositional.eval row A := by
  have hnot (t : Term S α) : termEval row (termNot negTerm t) = !(termEval row t) := by
    rw [termNot, termSubst_eval, hn]
    rfl
  have hand (s t : Term S α) : termEval row (termAnd andTerm s t) =
      (termEval row s && termEval row t) := by
    rw [termAnd, termSubst_eval, ha]
    rfl
  induction A with
  | atom a => rfl
  | falsum => exact hf row
  | neg A ih => simp only [fromFormula, hnot, ih, Propositional.eval]
  | conj A B ia ib => simp only [fromFormula, hand, ia, ib, Propositional.eval]
  | disj A B ia ib =>
    simp only [fromFormula, hnot, hand, ia, ib, Propositional.eval]
    cases Propositional.eval row A <;> cases Propositional.eval row B <;> rfl
  | impl A B ia ib =>
    simp only [fromFormula, hnot, hand, ia, ib, Propositional.eval]
    cases Propositional.eval row A <;> cases Propositional.eval row B <;> rfl

theorem dnfTerm_eval {S : Set Operation} {n : ℕ} (hn : 0 < n)
    (negTerm : Term S (Fin 1)) (andTerm : Term S (Fin 2))
    (falseUnaryTerm : Term S (Fin 1))
    (hneg : ∀ row, termEval row negTerm = unaryNeg row)
    (hand : ∀ row, termEval row andTerm = binaryAnd row)
    (hfalse : ∀ row, termEval row falseUnaryTerm = false)
    (f : TruthFunction n) (row : Fin n → Bool) :
    termEval row (dnfTerm hn negTerm andTerm falseUnaryTerm f) = f row := by
  unfold dnfTerm
  rw [fromFormula_eval _ _ _ hneg hand]
  · exact (canonicalDnf_represents id f).2 row
  · intro v
    rw [termSubst_eval]
    exact hfalse _

theorem positive_complete_of_basis {S : Set Operation}
    (hn : Generates S unaryNeg) (ha : Generates S binaryAnd)
    (hf : Generates S (unaryConstant false)) : PositiveComplete S := by
  obtain ⟨nt, hnt⟩ := hn
  obtain ⟨andT, hat⟩ := ha
  obtain ⟨ft, hft⟩ := hf
  intro n hn f
  exact ⟨dnfTerm hn nt andT ft f, dnfTerm_eval hn nt andT ft hnt hat hft f⟩

theorem post_criterion (S : Set Operation) : PositiveComplete S ↔ EscapesAll S := by
  constructor
  · exact necessary_witnesses
  · rintro ⟨h0, h1, hm, hd, ha⟩
    have hn := generates_negation h0 h1 hm
    have hc := generates_constants hn hd
    have ho := generates_oddBinary hn hc ha
    exact positive_complete_of_basis hn (generates_conjunction hn ho) (hc false)

theorem full_iff_positive_closed (S : Set Operation) :
    FullComplete S ↔ PositiveComplete S ∧ HasClosedTerm S := by
  constructor
  · intro hf
    refine ⟨fun n _ f => hf n f, ?_⟩
    obtain ⟨t, ht⟩ := hf 0 (fun _ => false)
    exact ⟨t⟩
  · rintro ⟨hp, ⟨t⟩⟩ n f
    cases n with
    | zero =>
      obtain ⟨ct, hct⟩ := hp 1 (by decide) (unaryConstant (f (fun i => Fin.elim0 i)))
      refine ⟨termSubst (fun _ => t) ct, fun row => ?_⟩
      rw [termSubst_eval, hct]
      change f (fun i => Fin.elim0 i) = f row
      apply congrArg f
      funext i
      exact Fin.elim0 i
    | succ n => exact hp _ (Nat.succ_pos _) f

theorem full_criterion (S : Set Operation) :
    FullComplete S ↔ EscapesAll S ∧ HasClosedTerm S := by
  rw [full_iff_positive_closed, post_criterion]

theorem full_criterion_nullary (S : Set Operation) :
    FullComplete S ↔ EscapesAll S ∧ ∃ g ∈ S, g.arity = 0 := by
  rw [full_criterion, closed_iff_nullary]

end Lemmatheca.MathematicalLogic.FunctionalCompletenessCriterion
