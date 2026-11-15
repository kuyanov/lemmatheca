import Lemmatheca.BoundedArithmeticNegativeTranslation.Universal

namespace Lemmatheca.Entry.BoundedArithmeticNegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.HeytingArithmetic
open Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
open Lemmatheca.ProofTheory.HeytingArithmetic.BoundedNegativeTranslation
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative)
noncomputable section
local instance bantExampleFormulaEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _

/-- The input x is an older name when the witness y is introduced. -/
def nested {α : Type} (a : LA.Term α) : Expr α :=
  .allLT a (.exLE (.var (.inr ()))
    (.disj (.equal (.var (.inr ())) (.var (.inl (.inr ()))))
      (.equal (.var (.inr ())) (succTerm (.var (.inl (.inr ())))))))

def nestedPresentation : Presentation Empty :=
  .all (.bounded (nested (.var (.inr ()))))

def nestedSentence : Sentence := nestedPresentation.expand

theorem nested_universal_bounded : UniversalBounded nestedSentence := by
  exact ⟨nestedPresentation, rfl⟩

private def witnessAt {α : Type} {Γ : Context α} (x : LA.Term α) :
    Certificate false Γ (inclusiveExists
      (.disj (termEqual (.var (.inr ())) (x.relabel Sum.inl))
        (termEqual (.var (.inr ())) (succTerm (x.relabel Sum.inl)))) x) := by
  apply TheoryCertificate.exUnitIntro _ x
  change Certificate false Γ (StrongInduction.atTerm
    (.conj (Order.leFormula (.var (.inr ())) (x.relabel Sum.inl))
      (.disj (termEqual (.var (.inr ())) (x.relabel Sum.inl))
        (termEqual (.var (.inr ())) (succTerm (x.relabel Sum.inl))))) x)
  rw [inclusiveExists_body_instance]
  apply TheoryCertificate.conjIntro (Order.leRefl x)
  have p : Certificate false Γ (.disj (termEqual x x) (termEqual x (succTerm x))) :=
    TheoryCertificate.disjLeft (TheoryCertificate.equalIntro x)
  simpa [StrongInduction.atTerm, subst_disj, termEqual_subst_poly, Term.subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel] using p

private def nestedProof {α : Type} {Γ : Context α} (a : LA.Term α) :
    Certificate false Γ (nested a).expand := by
  apply TheoryCertificate.allUnitIntro
  change Certificate false _ ((.impl _ _ : Formula (α ⊕ Unit)).rename _)
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_impl]
  apply TheoryCertificate.impIntro
  have p := witnessAt (Γ := insert
    ((Order.ltFormula (.var (.inr ())) (a.relabel Sum.inl)).rename
      (Sum.map id (fun _ => (0 : Fin 1))))
    (Γ.image (fun F => F.rename Sum.inl))) (.var (.inr (0 : Fin 1)) : LA.Term (α ⊕ Fin 1))
  simpa [nested, Expr.expand, inclusiveExists_subst, subst_disj,
    termEqual_subst_poly, unitSubst, Term.subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_relabel_subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel] using p

def nestedCertificate : Certificate false (∅ : Context Empty) nestedSentence := by
  apply TheoryCertificate.allUnitIntro
  have p := nestedProof (Γ := (∅ : Context (Empty ⊕ Fin 1)))
    (.var (.inr (0 : Fin 1)))
  simpa [nested, Expr.expand, nestedSentence, nestedPresentation, Presentation.expand,
    StrongInduction.history_subst, inclusiveExists_subst, subst_disj,
    termEqual_subst_poly, unitSubst, Term.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_relabel_subst,
    Lemmatheca.MathematicalLogic.FirstOrderProofs.term_subst_relabel] using p

def nestedNegativeCertificate :
    Certificate false (∅ : Context Empty) (negative nestedSentence) := by
  exact (universalBoundedConversions nestedSentence nested_universal_bounded).forward
    nestedCertificate

theorem nested_not_universal_matrix :
    ¬ NegativeTranslation.UniversalMatrix nestedSentence := by
  simp [nestedSentence, nestedPresentation, Presentation.expand, nested, Expr.expand,
    StrongInduction.history, inclusiveExists, allUnit, exUnit, bindUnit, map,
    NegativeTranslation.UniversalMatrix, QuantifierFree]

end
end Lemmatheca.Entry.BoundedArithmeticNegativeTranslation
