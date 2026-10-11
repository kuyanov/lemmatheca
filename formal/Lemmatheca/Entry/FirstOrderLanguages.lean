import Lemmatheca.MathematicalLogic.FirstOrderSyntax

/-! Particular illustrative first-order syntax trees. -/

namespace Lemmatheca.Entry.FirstOrderLanguages

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax

variable {L : Language}

theorem doubleUnary_support (s : L.Functions 1) :
    (s.apply₁ (s.apply₁ (.var 0 : L.Term ℕ))).varFinset = {0} := by
  simp [Functions.apply₁]

theorem doubleUnary_subst (s : L.Functions 1) :
    (s.apply₁ (s.apply₁ (.var 0 : L.Term ℕ))).subst
        (fun i => if i = 0 then s.apply₁ (.var 1) else .var i) =
      s.apply₁ (s.apply₁ (s.apply₁ (.var 1))) := by
  simp [Functions.apply₁, Term.subst, funext_iff]

/-- The formula saying that the free parameter is related to some element. -/
def parameterHasSuccessor (r : L.Relations 2) : L.Formula ℕ :=
  (r.boundedFormula₂ (.var (.inl 0)) (.var (.inr 0)) : L.BoundedFormula ℕ 1).ex

/-- The sentence saying every element is related to some element. -/
def everyHasSuccessor (r : L.Relations 2) : L.Sentence :=
  ((r.boundedFormula₂ (.var (.inr 0)) (.var (.inr 1)) : L.BoundedFormula Empty 2).ex).all

/-- The captured tree, which relates a quantified element to itself. -/
def capturedSelfRelation (r : L.Relations 2) : L.Formula ℕ :=
  (r.boundedFormula₂ (.var (.inr 0)) (.var (.inr 0)) : L.BoundedFormula ℕ 1).ex

theorem parameterHasSuccessor_support (r : L.Relations 2) :
    (parameterHasSuccessor r).freeVarFinset = {0} := by
  simp [parameterHasSuccessor, BoundedFormula.ex, BoundedFormula.not,
    Relations.boundedFormula₂, Relations.boundedFormula, Finset.univ_fin2]

theorem everyHasSuccessor_support (r : L.Relations 2) :
    (everyHasSuccessor r).freeVarFinset = ∅ := by
  simp [everyHasSuccessor, BoundedFormula.ex, BoundedFormula.not,
    Relations.boundedFormula₂, Relations.boundedFormula, Finset.univ_fin2]

theorem parameterHasSuccessor_subst (r : L.Relations 2) :
    (parameterHasSuccessor r).subst (fun i => if i = 0 then .var 1 else .var i) =
      (r.boundedFormula₂ (.var (.inl 1)) (.var (.inr 0)) : L.BoundedFormula ℕ 1).ex := by
  simp [parameterHasSuccessor, BoundedFormula.subst, BoundedFormula.ex,
    BoundedFormula.not, BoundedFormula.mapTermRel, Relations.boundedFormula₂,
    Relations.boundedFormula, Bot.bot, funext_iff, Fin.forall_fin_two]

theorem parameterHasSuccessor_subst_support (r : L.Relations 2) :
    ((parameterHasSuccessor r).subst (fun i => if i = 0 then .var 1 else .var i)).freeVarFinset =
      {1} := by
  rw [parameterHasSuccessor_subst]
  simp [Relations.boundedFormula₂, Relations.boundedFormula, Finset.univ_fin2]

theorem capturedSelfRelation_support (r : L.Relations 2) :
    (capturedSelfRelation r).freeVarFinset = ∅ := by
  simp [capturedSelfRelation, BoundedFormula.ex, BoundedFormula.not,
    Relations.boundedFormula₂, Relations.boundedFormula, Finset.univ_fin2]

end Lemmatheca.Entry.FirstOrderLanguages
