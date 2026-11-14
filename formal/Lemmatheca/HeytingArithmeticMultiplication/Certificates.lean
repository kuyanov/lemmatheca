import Lemmatheca.HeytingArithmeticMultiplication.Statements
import Lemmatheca.HeytingArithmeticAddition.Instances

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder (liftScope scopeInclusion)
open Lemmatheca.MathematicalLogic.FirstOrderProofs
noncomputable section
local instance haMultiplicationCertificateEq {α : Type*} : DecidableEq (Formula α) := Classical.decEq _
private theorem basicIn : basic ⊆ theory := fun _ h => Or.inl h

attribute [local simp] lastCases_one lastCases_two_zero lastCases_two_one
@[simp] private theorem lastCases_three_zero {δ : Sort*} (a : δ) (f : Fin 2 → δ) :
    Fin.lastCases a f (0 : Fin 3) = f 0 := by
  change Fin.lastCases a f (Fin.castSucc (0 : Fin 2)) = f 0
  exact Fin.lastCases_castSucc _
@[simp] private theorem lastCases_three_one {δ : Sort*} (a : δ) (f : Fin 2 → δ) :
    Fin.lastCases a f (1 : Fin 3) = f 1 := by
  change Fin.lastCases a f (Fin.castSucc (1 : Fin 2)) = f 1
  exact Fin.lastCases_castSucc _
@[simp] private theorem lastCases_three_two {δ : Sort*} (a : δ) (f : Fin 2 → δ) :
    Fin.lastCases a f (2 : Fin 3) = a := by
  change Fin.lastCases a f (Fin.last 2) = a
  exact Fin.lastCases_last

private def closeTwo (D : Formula (Fin 2))
    (p : Certificate false (∅ : Context (Fin 2)) D) :
    Certificate false (∅ : Context Empty) (close D) := by
  change Certificate false ∅ (.all (.all _))
  apply TheoryCertificate.allIntro
  apply TheoryCertificate.allIntro
  let f : Fin 2 → (Empty ⊕ Fin 1) ⊕ Fin 1 := ![.inl (.inr 0), .inr 0]
  have q := p.rename f
  convert q using 1
  · simp only [Finset.image_empty]
  · unfold toFormula rename subst
    simp only [map_comp]
    congr 1
    funext z
    cases z with
    | inl i => fin_cases i <;> simp [f, freeScope, liftScope, scopeInclusion,
        Term.subst, Term.relabel]
    | inr i => exact i.elim0

private def closeThree (D : Formula (Fin 3))
    (p : Certificate false (∅ : Context (Fin 3)) D) :
    Certificate false (∅ : Context Empty) (close D) := by
  change Certificate false ∅ (.all (.all (.all _)))
  apply TheoryCertificate.allIntro
  apply TheoryCertificate.allIntro
  apply TheoryCertificate.allIntro
  let f : Fin 3 → ((Empty ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1 :=
    ![.inl (.inl (.inr 0)), .inl (.inr 0), .inr 0]
  have q := p.rename f
  convert q using 1
  · simp only [Finset.image_empty]
  · unfold toFormula rename subst
    simp only [map_comp]
    congr 1
    funext z
    cases z with
    | inl i => fin_cases i <;> simp [f, freeScope, liftScope, scopeInclusion,
        Term.subst, Term.relabel]
    | inr i => exact i.elim0

private def inductAt {k} (A : Formula (Fin k ⊕ Unit)) (t : LA.Term (Fin k))
    (p0 : Certificate false (∅ : Context (Fin k)) (base A))
    (ps : Certificate false
      (insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅)
      ((next A).rename (Sum.map id (fun _ => (0 : Fin 1))))) :
    Certificate false (∅ : Context (Fin k))
      (A.subst (Sum.elim Term.var (fun _ => t))) :=
  TheoryCertificate.allUnitElim A t
    (inductionRule A ∅ p0 (by simpa only [Finset.image_empty] using ps))



def zeroLeftProof : Certificate false (∅ : Context Empty) zeroLeftSentence := by
  let A : Formula (Fin 1 ⊕ Unit) := termEqual (mulTerm zeroTerm (.var (.inr ()))) zeroTerm
  have p0 : Certificate false (∅ : Context (Fin 1)) (base A) := by
    simpa [A, base, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using
      TheoryCertificate.mulZero (Γ := (∅ : Context (Fin 1))) basicIn zeroTerm
  let Δ : Context (Fin 1 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let u : LA.Term (Fin 1 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (mulTerm zeroTerm u) zeroTerm) := by
    simpa [A, u, rename, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity (TheoryCertificate.mulSucc basicIn zeroTerm u)
    (TheoryCertificate.equalTransitivity
      (TheoryCertificate.addEquality ih (TheoryCertificate.equalIntro zeroTerm))
      (TheoryCertificate.addZero basicIn zeroTerm))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, u, rename, termEqual_subst_poly, mul_subst, zero_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 1)) zeroLeftBody := by
    simpa [A, zeroLeftBody, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using
      inductAt A (.var 0) p0 ps
  exact TheoryCertificate.closeOneIntro zeroLeftBody p

private def addOne {α : Type*} {Γ : Context α} (t : LA.Term α) :
    Certificate false Γ (termEqual (addTerm t (succTerm zeroTerm)) (succTerm t)) :=
  TheoryCertificate.equalTransitivity (TheoryCertificate.addSucc basicIn t zeroTerm)
    (TheoryCertificate.succEquality (TheoryCertificate.addZero basicIn t))

def oneLeftProof : Certificate false (∅ : Context Empty) oneLeftSentence := by
  let A : Formula (Fin 1 ⊕ Unit) := termEqual
    (mulTerm (succTerm zeroTerm) (.var (.inr ()))) (.var (.inr ()))
  have p0 : Certificate false (∅ : Context (Fin 1)) (base A) := by
    simpa [A, base, termEqual_subst_poly, mul_subst, zero_subst, succ_subst, Term.subst] using
      TheoryCertificate.mulZero (Γ := (∅ : Context (Fin 1))) basicIn (succTerm zeroTerm)
  let Δ : Context (Fin 1 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let u : LA.Term (Fin 1 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (mulTerm (succTerm zeroTerm) u) u) := by
    simpa [A, u, rename, termEqual_subst_poly, mul_subst, zero_subst, succ_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity (TheoryCertificate.mulSucc basicIn (succTerm zeroTerm) u)
    (TheoryCertificate.equalTransitivity
      (TheoryCertificate.addEquality ih (TheoryCertificate.equalIntro (succTerm zeroTerm))) (addOne u))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, u, rename, termEqual_subst_poly, mul_subst, zero_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 1)) oneLeftBody := by
    simpa [A, oneLeftBody, termEqual_subst_poly, mul_subst, zero_subst, succ_subst, Term.subst] using
      inductAt A (.var 0) p0 ps
  exact TheoryCertificate.closeOneIntro oneLeftBody p

def successorLeftProof : Certificate false (∅ : Context Empty) successorLeftSentence := by
  let A : Formula (Fin 2 ⊕ Unit) := termEqual
    (mulTerm (succTerm (.var (.inl 0))) (.var (.inr ())))
    (addTerm (mulTerm (.var (.inl 0)) (.var (.inr ()))) (.var (.inr ())))
  have p0 : Certificate false (∅ : Context (Fin 2)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.mulZero (Γ := (∅ : Context (Fin 2))) basicIn (succTerm (.var 0)))
      (TheoryCertificate.equalTransitivity (TheoryCertificate.equalSymmetry (TheoryCertificate.mulZero basicIn (.var 0)))
        (TheoryCertificate.equalSymmetry (TheoryCertificate.addZero basicIn (mulTerm (.var 0) zeroTerm))))
    simpa [A, base, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using h
  let Δ : Context (Fin 2 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inl 0)
  let u : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (mulTerm (succTerm x) u) (addTerm (mulTerm x u) u)) := by
    simpa [A, x, u, rename, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity (TheoryCertificate.mulSucc basicIn (succTerm x) u)
    (TheoryCertificate.equalTransitivity
      (TheoryCertificate.addEquality ih (TheoryCertificate.equalIntro (succTerm x)))
      (TheoryCertificate.equalTransitivity (TheoryCertificate.addSucc basicIn (addTerm (mulTerm x u) u) x)
        (TheoryCertificate.equalTransitivity (TheoryCertificate.succEquality (Addition.exchange (mulTerm x u) u x))
          (TheoryCertificate.equalTransitivity
            (TheoryCertificate.equalSymmetry (TheoryCertificate.addSucc basicIn (addTerm (mulTerm x u) x) u))
            (TheoryCertificate.addEquality (TheoryCertificate.equalSymmetry (TheoryCertificate.mulSucc basicIn x u))
              (TheoryCertificate.equalIntro (succTerm u)))))))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, u, rename, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 2)) successorLeftBody := by
    simpa [A, successorLeftBody, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using
      inductAt A (.var 1) p0 ps
  exact closeTwo successorLeftBody p

private def zeroAt {α : Type*} {Γ : Context α} (s : LA.Term α) :
    Certificate false Γ (termEqual (mulTerm zeroTerm s) zeroTerm) := by
  simpa [zeroLeftBody, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using
    Addition.instantiateClosed zeroLeftBody zeroLeftProof ![s] Γ

private def successorAt {α : Type*} {Γ : Context α} (s t : LA.Term α) :
    Certificate false Γ (termEqual (mulTerm (succTerm s) t) (addTerm (mulTerm s t) t)) := by
  simpa [successorLeftBody, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using
    Addition.instantiateClosed successorLeftBody successorLeftProof ![s,t] Γ

def commutativityProof : Certificate false (∅ : Context Empty) commutativitySentence := by
  let A : Formula (Fin 2 ⊕ Unit) := termEqual
    (mulTerm (.var (.inl 0)) (.var (.inr ()))) (mulTerm (.var (.inr ())) (.var (.inl 0)))
  have p0 : Certificate false (∅ : Context (Fin 2)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.mulZero (Γ := (∅ : Context (Fin 2))) basicIn (.var 0))
      (TheoryCertificate.equalSymmetry (zeroAt (.var 0)))
    simpa [A, base, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using h
  let Δ : Context (Fin 2 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inl 0)
  let u : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (mulTerm x u) (mulTerm u x)) := by
    simpa [A, x, u, rename, termEqual_subst_poly, mul_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity (TheoryCertificate.mulSucc basicIn x u)
    (TheoryCertificate.equalTransitivity (TheoryCertificate.addEquality ih (TheoryCertificate.equalIntro x))
      (TheoryCertificate.equalSymmetry (successorAt u x)))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, u, rename, termEqual_subst_poly, mul_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 2)) commutativityBody := by
    simpa [A, commutativityBody, termEqual_subst_poly, mul_subst, Term.subst] using
      inductAt A (.var 1) p0 ps
  exact closeTwo commutativityBody p

def leftDistributivityProof : Certificate false (∅ : Context Empty) leftDistributivitySentence := by
  let A : Formula (Fin 3 ⊕ Unit) := termEqual
    (mulTerm (.var (.inl 0)) (addTerm (.var (.inl 1)) (.var (.inr ()))))
    (addTerm (mulTerm (.var (.inl 0)) (.var (.inl 1))) (mulTerm (.var (.inl 0)) (.var (.inr ()))))
  have p0 : Certificate false (∅ : Context (Fin 3)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.mulEquality (TheoryCertificate.equalIntro (.var 0))
        (TheoryCertificate.addZero (Γ := (∅ : Context (Fin 3))) basicIn (.var 1)))
      (TheoryCertificate.equalTransitivity
        (TheoryCertificate.equalSymmetry (TheoryCertificate.addZero basicIn (mulTerm (.var 0) (.var 1))))
        (TheoryCertificate.addEquality (TheoryCertificate.equalIntro (mulTerm (.var 0) (.var 1)))
          (TheoryCertificate.equalSymmetry (TheoryCertificate.mulZero basicIn (.var 0)))))
    simpa [A, base, termEqual_subst_poly, mul_subst, add_subst, Term.subst] using h
  let Δ : Context (Fin 3 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 0)
  let y : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 1)
  let u : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (mulTerm x (addTerm y u))
      (addTerm (mulTerm x y) (mulTerm x u))) := by
    simpa [A, x, y, u, rename, termEqual_subst_poly, mul_subst, add_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity
    (TheoryCertificate.mulEquality (TheoryCertificate.equalIntro x) (TheoryCertificate.addSucc basicIn y u))
    (TheoryCertificate.equalTransitivity (TheoryCertificate.mulSucc basicIn x (addTerm y u))
      (TheoryCertificate.equalTransitivity (TheoryCertificate.addEquality ih (TheoryCertificate.equalIntro x))
        (TheoryCertificate.equalTransitivity (Addition.associative (mulTerm x y) (mulTerm x u) x)
          (TheoryCertificate.addEquality (TheoryCertificate.equalIntro (mulTerm x y))
            (TheoryCertificate.equalSymmetry (TheoryCertificate.mulSucc basicIn x u))))))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, y, u, rename, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 3)) leftDistributivityBody := by
    simpa [A, leftDistributivityBody, termEqual_subst_poly, mul_subst, add_subst, Term.subst] using
      inductAt A (.var 2) p0 ps
  exact closeThree leftDistributivityBody p

private def commutativeAt {α : Type*} {Γ : Context α} (s t : LA.Term α) :
    Certificate false Γ (termEqual (mulTerm s t) (mulTerm t s)) := by
  simpa [commutativityBody, termEqual_subst_poly, mul_subst, Term.subst] using
    Addition.instantiateClosed commutativityBody commutativityProof ![s,t] Γ

private def distributeLeftAt {α : Type*} {Γ : Context α} (s t u : LA.Term α) :
    Certificate false Γ (termEqual (mulTerm s (addTerm t u)) (addTerm (mulTerm s t) (mulTerm s u))) := by
  simpa [leftDistributivityBody, termEqual_subst_poly, mul_subst, add_subst, Term.subst] using
    Addition.instantiateClosed leftDistributivityBody leftDistributivityProof ![s,t,u] Γ

def rightDistributivityProof : Certificate false (∅ : Context Empty) rightDistributivitySentence := by
  have p : Certificate false (∅ : Context (Fin 3)) rightDistributivityBody :=
    TheoryCertificate.equalTransitivity (commutativeAt (addTerm (.var 0) (.var 1)) (.var 2))
      (TheoryCertificate.equalTransitivity (distributeLeftAt (.var 2) (.var 0) (.var 1))
        (TheoryCertificate.addEquality (commutativeAt (.var 2) (.var 0)) (commutativeAt (.var 2) (.var 1))))
  exact closeThree rightDistributivityBody p

def associativityProof : Certificate false (∅ : Context Empty) associativitySentence := by
  let A : Formula (Fin 3 ⊕ Unit) := termEqual
    (mulTerm (mulTerm (.var (.inl 0)) (.var (.inl 1))) (.var (.inr ())))
    (mulTerm (.var (.inl 0)) (mulTerm (.var (.inl 1)) (.var (.inr ()))))
  have p0 : Certificate false (∅ : Context (Fin 3)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.mulZero (Γ := (∅ : Context (Fin 3))) basicIn (mulTerm (.var 0) (.var 1)))
      (TheoryCertificate.equalTransitivity (TheoryCertificate.equalSymmetry (TheoryCertificate.mulZero basicIn (.var 0)))
        (TheoryCertificate.mulEquality (TheoryCertificate.equalIntro (.var 0))
          (TheoryCertificate.equalSymmetry (TheoryCertificate.mulZero basicIn (.var 1)))))
    simpa [A, base, termEqual_subst_poly, mul_subst, Term.subst] using h
  let Δ : Context (Fin 3 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 0)
  let y : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 1)
  let u : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (mulTerm (mulTerm x y) u) (mulTerm x (mulTerm y u))) := by
    simpa [A, x, y, u, rename, termEqual_subst_poly, mul_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity (TheoryCertificate.mulSucc basicIn (mulTerm x y) u)
    (TheoryCertificate.equalTransitivity (TheoryCertificate.addEquality ih (TheoryCertificate.equalIntro (mulTerm x y)))
      (TheoryCertificate.equalTransitivity (TheoryCertificate.equalSymmetry (distributeLeftAt x (mulTerm y u) y))
        (TheoryCertificate.mulEquality (TheoryCertificate.equalIntro x)
          (TheoryCertificate.equalSymmetry (TheoryCertificate.mulSucc basicIn y u)))))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, y, u, rename, termEqual_subst_poly, mul_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 3)) associativityBody := by
    simpa [A, associativityBody, termEqual_subst_poly, mul_subst, Term.subst] using
      inductAt A (.var 2) p0 ps
  exact closeThree associativityBody p

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Multiplication
