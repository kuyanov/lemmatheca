import Lemmatheca.HeytingArithmeticOrder.Certificates

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Order
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder (liftScope scopeInclusion)
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u
noncomputable section
local instance haoClosureEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _

private def slotsIntro : {n : ℕ} → (A : BF Empty n) →
    Certificate false (∅ : Context (Empty ⊕ Fin n)) A.toFormula →
    Certificate false (∅ : Context Empty) (allSlots A)
  | 0, A, p => by
    have q := p.rename (Sum.elim id Fin.elim0 : Empty ⊕ Fin 0 → Empty)
    convert q using 1
    · simp only [Finset.image_empty]
    · unfold toFormula rename subst
      rw [map_comp]
      symm
      calc
        A.map _ = A.map Term.var := by
          congr 1
          funext z
          cases z with
          | inl e => exact e.elim
          | inr i => exact i.elim0
        _ = A := map_id A
  | n+1, A, p => by
    let f : Empty ⊕ Fin (n+1) → (Empty ⊕ Fin n) ⊕ Fin 1 :=
      Sum.elim Empty.elim (Fin.lastCases (.inr 0) (fun i => .inl (.inr i)))
    have q : Certificate false (∅ : Context (Empty ⊕ Fin n)) ((.all A : BF Empty n).toFormula) := by
      change Certificate false ∅ (.all _)
      apply TheoryCertificate.allIntro
      have pr := p.rename f
      convert pr using 1
      · simp only [Finset.image_empty]
      · unfold toFormula rename subst
        simp only [map_comp]
        congr 1
        funext z
        cases z with
        | inl e => exact e.elim
        | inr i =>
          induction i using Fin.lastCases with
          | last => simp [f, liftScope, scopeInclusion, freeScope, Term.subst]
          | cast i => simp [f, liftScope, scopeInclusion, freeScope, Term.subst, Term.relabel]
    exact slotsIntro (.all A) q

/-- Universally introduce every member of the ordered finite original parameter list. -/
def closeCertificate {k : ℕ} (A : Formula (Fin k))
    (p : Certificate false (∅ : Context (Fin k)) A) :
    Certificate false (∅ : Context Empty) (close A) := by
  let B : BF Empty k := A.map (Sum.elim (fun i => .var (.inr i)) Fin.elim0)
  apply slotsIntro B
  have q := p.rename (Sum.inr : Fin k → Empty ⊕ Fin k)
  convert q using 1
  · simp only [Finset.image_empty]
  · unfold B toFormula rename subst
    rw [map_comp]
    congr 1
    funext z
    cases z with
    | inl i => rfl
    | inr i => exact i.elim0

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Order
