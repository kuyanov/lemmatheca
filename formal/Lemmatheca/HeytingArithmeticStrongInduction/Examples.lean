import Lemmatheca.HeytingArithmeticStrongInduction.Schemata

namespace Lemmatheca.Entry.HeytingArithmeticStrongInduction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.HeytingArithmetic
open Lemmatheca.ProofTheory.HeytingArithmetic.Order
open Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open TheoryCertificate
universe u
variable {α : Type u}

/-- The parameter term has no occurrence of the fresh predicate-input name. -/
def orderPredicate (t : LA.Term α) : Formula (α ⊕ Unit) :=
  leFormula (t.relabel Sum.inl) (.var (.inr ()))

theorem orderPredicate_instance (t s : LA.Term α) :
    atTerm (orderPredicate t) s = leFormula t s := by
  simp [atTerm, orderPredicate, leFormula_subst, term_subst_relabel, Term.subst]

noncomputable section
local instance hasiExamplesEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _
variable {Γ : Context α}

def orderPredicateDecision (t : LA.Term α) :
    Certificate false Γ (predicateDecision (orderPredicate t)) := by
  apply allUnitIntro (.disj (orderPredicate t) (.neg (orderPredicate t)))
  have hp : (orderPredicate t).rename (Sum.map id (fun _ => (0 : Fin 1))) =
      leFormula (t.relabel Sum.inl) (.var (.inr (0 : Fin 1))) := by
    simp [orderPredicate, leFormula_rename, Term.relabel_relabel, Term.relabel, Function.comp_def]
  let P := (orderPredicate t).rename (Sum.map id (fun _ => (0 : Fin 1)))
  change Certificate false (Γ.image (fun A => A.rename (Sum.inl : α → α ⊕ Fin 1))) (.disj P (.neg P))
  change P = leFormula (t.relabel Sum.inl) (.var (.inr (0 : Fin 1))) at hp
  rw [hp]
  exact leDecision (t.relabel Sum.inl) (.var (.inr 0))

def orderPredicateMinimum (t : LA.Term α) :
    Certificate false Γ (minimum (orderPredicate t) t) := by
  apply conjIntro
  · rw [orderPredicate_instance]
    exact leRefl t
  · apply allUnitIntro (.impl (ltFormula (.var (.inr ())) (t.relabel Sum.inl)) (.neg (orderPredicate t)))
    have hp : (orderPredicate t).rename (Sum.map id (fun _ => (0 : Fin 1))) =
        leFormula (t.relabel Sum.inl) (.var (.inr (0 : Fin 1))) := by
      simp [orderPredicate, leFormula_rename, Term.relabel_relabel, Term.relabel, Function.comp_def]
    have hg : (ltFormula (.var (.inr ())) (t.relabel Sum.inl)).rename
        (Sum.map id (fun _ => (0 : Fin 1))) =
        ltFormula (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl) := by
      simp [ltFormula_rename, Term.relabel_relabel, Term.relabel, Function.comp_def]
    let P := (orderPredicate t).rename (Sum.map id (fun _ => (0 : Fin 1)))
    let L := (ltFormula (.var (.inr ())) (t.relabel Sum.inl)).rename
      (Sum.map id (fun _ => (0 : Fin 1)))
    change Certificate false (Γ.image (fun A => A.rename (Sum.inl : α → α ⊕ Fin 1))) (.impl L (.neg P))
    change P = leFormula (t.relabel Sum.inl) (.var (.inr (0 : Fin 1))) at hp
    change L = ltFormula (.var (.inr (0 : Fin 1))) (t.relabel Sum.inl) at hg
    rw [hp, hg]
    apply impIntro
    apply negIntro
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    exact negElim (impElim (ltLeTransitivity e (t.relabel Sum.inl) e)
      (conjIntro (assumption (by simp [e])) (assumption (Finset.mem_insert_self _ _))))
      (ltIrrefl e)

end
end Lemmatheca.Entry.HeytingArithmeticStrongInduction
