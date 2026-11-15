import Lemmatheca.HeytingArithmeticBoundedFormulas.Certificates
import Lemmatheca.HeytingArithmeticOrder.Closure

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula

noncomputable section
local instance habfDecisionsEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _
open TheoryCertificate

private def closeDecisionInput {α : Type} (A : Formula (α ⊕ Unit))
    (p : Certificate false (∅ : Context (α ⊕ Unit)) (.disj A (.neg A))) :
    Certificate false (∅ : Context α) (StrongInduction.predicateDecision A) := by
  apply allUnitIntro (.disj A (.neg A))
  simpa only [Finset.image_empty] using
    p.rename (Sum.map id (fun _ => (0 : Fin 1)))

/-- Structural proof construction for the actual expansion, with finite free names. -/
def decision {α : Type} [Fintype α] (B : Expr α) :
    Certificate false (∅ : Context α) (.disj B.expand (.neg B.expand)) := by
  revert ‹Fintype α›
  induction B with
  | falsum => intro _; exact falsumDecision
  | equal s t => intro _; exact equalityTermDecision s t
  | le s t => intro _; exact Order.leDecision s t
  | lt s t => intro _; exact Order.ltDecision s t
  | neg B ih => intro _; exact negDecision B.expand ih
  | conj B C ihB ihC => intro _; exact conjDecision B.expand C.expand ihB ihC
  | disj B C ihB ihC => intro _; exact disjDecision B.expand C.expand ihB ihC
  | impl B C ihB ihC => intro _; exact implDecision B.expand C.expand ihB ihC
  | allLT t B ih => intro _; exact strictAllDecision B.expand t (closeDecisionInput B.expand ih)
  | exLT t B ih => intro _; exact strictExistsDecision B.expand t (closeDecisionInput B.expand ih)
  | allLE t B ih => intro _; exact inclusiveAllDecision B.expand t (closeDecisionInput B.expand ih)
  | exLE t B ih => intro _; exact inclusiveExistsDecision B.expand t (closeDecisionInput B.expand ih)

def closedDecision {k : ℕ} (B : Expr (Fin k)) :
    Certificate false (∅ : Context Empty) (close (.disj B.expand (.neg B.expand))) := by
  exact Order.closeCertificate _ (decision B)

def decisionInstance {k : ℕ} {β : Type} (B : Expr (Fin k))
    (σ : Fin k → LA.Term β) {Γ : Context β} :
    Certificate false Γ (.disj (B.subst σ).expand (.neg (B.subst σ).expand)) := by
  have p := (decision B).substitute σ
  have q : Certificate false (∅ : Context β)
      (.disj (B.subst σ).expand (.neg (B.subst σ).expand)) := by
    simpa only [Finset.image_empty, subst_disj, subst_neg, expand_subst] using p
  exact q.weaken (Finset.empty_subset _)

def stability {α : Type} [Fintype α] (B : Expr α) :
    Certificate false (∅ : Context α) (.impl (.neg (.neg B.expand)) B.expand) := by
  exact stabilityFromDecision B.expand (decision B)

def closedStability {k : ℕ} (B : Expr (Fin k)) :
    Certificate false (∅ : Context Empty) (close (.impl (.neg (.neg B.expand)) B.expand)) := by
  exact Order.closeCertificate _ (stability B)

def stabilityInstance {k : ℕ} {β : Type} (B : Expr (Fin k))
    (σ : Fin k → LA.Term β) {Γ : Context β} :
    Certificate false Γ (.impl (.neg (.neg (B.subst σ).expand)) (B.subst σ).expand) := by
  have p := (stability B).substitute σ
  have q : Certificate false (∅ : Context β)
      (.impl (.neg (.neg (B.subst σ).expand)) (B.subst σ).expand) := by
    simpa only [Finset.image_empty, subst_impl, subst_neg, expand_subst] using p
  exact q.weaken (Finset.empty_subset _)

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
