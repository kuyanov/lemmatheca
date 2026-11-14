import Lemmatheca.HeytingArithmeticAddition.Statements

namespace Lemmatheca.ProofTheory.HeytingArithmetic.Addition
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder (liftScope scopeInclusion)
open Lemmatheca.MathematicalLogic.FirstOrderProofs
noncomputable section
local instance haAdditionCertificateEq {α : Type*} : DecidableEq (Formula α) := Classical.decEq _
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

/-- Construct the finite native HA induction for the exact closed sentence. -/
def zeroLeftProof : Certificate false (∅ : Context Empty) zeroLeftSentence := by
  let A : Formula (Fin 1 ⊕ Unit) := termEqual (addTerm zeroTerm (.var (.inr ()))) (.var (.inr ()))
  have p0 : Certificate false (∅ : Context (Fin 1)) (base A) := by
    simpa [A, base, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using
      TheoryCertificate.addZero (Γ := (∅ : Context (Fin 1))) basicIn zeroTerm
  let Δ : Context (Fin 1 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let u : LA.Term (Fin 1 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (addTerm zeroTerm u) u) := by
    simpa [A, Δ, u, rename, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, u, rename, termEqual_subst_poly, add_subst, succ_subst,
      zero_subst, Term.subst] using TheoryCertificate.equalTransitivity
        (TheoryCertificate.addSucc basicIn zeroTerm u)
        (TheoryCertificate.succEquality ih)
  have p : Certificate false (∅ : Context (Fin 1)) zeroLeftBody := by
    simpa [A, zeroLeftBody, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using
      inductAt A (.var 0) p0 ps
  exact TheoryCertificate.closeOneIntro zeroLeftBody p

def successorLeftProof : Certificate false (∅ : Context Empty) successorLeftSentence := by
  let A : Formula (Fin 2 ⊕ Unit) := termEqual
    (addTerm (succTerm (.var (.inl 0))) (.var (.inr ())))
    (succTerm (addTerm (.var (.inl 0)) (.var (.inr ()))))
  have p0 : Certificate false (∅ : Context (Fin 2)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.addZero (Γ := (∅ : Context (Fin 2))) basicIn (succTerm (.var 0)))
      (TheoryCertificate.equalSymmetry (TheoryCertificate.succEquality
        (TheoryCertificate.addZero basicIn (.var 0))))
    simpa [A, base, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using h
  let Δ : Context (Fin 2 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inl 0)
  let u : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (addTerm (succTerm x) u) (succTerm (addTerm x u))) := by
    simpa [A, x, u, rename, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity
    (TheoryCertificate.addSucc basicIn (succTerm x) u)
    (TheoryCertificate.equalTransitivity (TheoryCertificate.succEquality ih)
      (TheoryCertificate.equalSymmetry (TheoryCertificate.succEquality
        (TheoryCertificate.addSucc basicIn x u))))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, u, rename, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 2)) successorLeftBody := by
    simpa [A, successorLeftBody, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using
      inductAt A (.var 1) p0 ps
  exact closeTwo successorLeftBody p

def associativityProof : Certificate false (∅ : Context Empty) associativitySentence := by
  let A : Formula (Fin 3 ⊕ Unit) := termEqual
    (addTerm (addTerm (.var (.inl 0)) (.var (.inl 1))) (.var (.inr ())))
    (addTerm (.var (.inl 0)) (addTerm (.var (.inl 1)) (.var (.inr ()))))
  have p0 : Certificate false (∅ : Context (Fin 3)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.addZero (Γ := (∅ : Context (Fin 3))) basicIn (addTerm (.var 0) (.var 1)))
      (TheoryCertificate.equalSymmetry (TheoryCertificate.addEquality
        (TheoryCertificate.equalIntro (.var 0)) (TheoryCertificate.addZero basicIn (.var 1))))
    simpa [A, base, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using h
  let Δ : Context (Fin 3 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 0)
  let y : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 1)
  let u : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (addTerm (addTerm x y) u) (addTerm x (addTerm y u))) := by
    simpa [A, x, y, u, rename, termEqual_subst_poly, add_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity
    (TheoryCertificate.addSucc basicIn (addTerm x y) u)
    (TheoryCertificate.equalTransitivity (TheoryCertificate.succEquality ih)
      (TheoryCertificate.equalTransitivity (TheoryCertificate.equalSymmetry
        (TheoryCertificate.addSucc basicIn x (addTerm y u)))
        (TheoryCertificate.addEquality (TheoryCertificate.equalIntro x)
          (TheoryCertificate.equalSymmetry (TheoryCertificate.addSucc basicIn y u)))))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, y, u, rename, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 3)) associativityBody := by
    simpa [A, associativityBody, termEqual_subst_poly, add_subst, Term.subst] using
      inductAt A (.var 2) p0 ps
  exact closeThree associativityBody p

private def zeroAt {α : Type*} {Γ : Context α} (s : LA.Term α) :
    Certificate false Γ (termEqual (addTerm zeroTerm s) s) := by
  simpa [zeroLeftBody, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using
    instantiateClosed zeroLeftBody zeroLeftProof ![s] Γ

private def successorAt {α : Type*} {Γ : Context α} (s t : LA.Term α) :
    Certificate false Γ (termEqual (addTerm (succTerm s) t) (succTerm (addTerm s t))) := by
  simpa [successorLeftBody, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using
    instantiateClosed successorLeftBody successorLeftProof ![s,t] Γ

def commutativityProof : Certificate false (∅ : Context Empty) commutativitySentence := by
  let A : Formula (Fin 2 ⊕ Unit) := termEqual
    (addTerm (.var (.inl 0)) (.var (.inr ())))
    (addTerm (.var (.inr ())) (.var (.inl 0)))
  have p0 : Certificate false (∅ : Context (Fin 2)) (base A) := by
    have h := TheoryCertificate.equalTransitivity
      (TheoryCertificate.addZero (Γ := (∅ : Context (Fin 2))) basicIn (.var 0))
      (TheoryCertificate.equalSymmetry (zeroAt (.var 0)))
    simpa [A, base, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using h
  let Δ : Context (Fin 2 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let x : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inl 0)
  let u : LA.Term (Fin 2 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (termEqual (addTerm x u) (addTerm u x)) := by
    simpa [A, x, u, rename, termEqual_subst_poly, add_subst, Term.subst] using
      (TheoryCertificate.assumption (c := false) (T := theory) (Γ := Δ)
        (A := A.rename (Sum.map id (fun _ => (0 : Fin 1)))) (Finset.mem_insert_self _ _))
  have h := TheoryCertificate.equalTransitivity (TheoryCertificate.addSucc basicIn x u)
    (TheoryCertificate.equalTransitivity (TheoryCertificate.succEquality ih)
      (TheoryCertificate.equalSymmetry (successorAt u x)))
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, x, u, rename, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using h
  have p : Certificate false (∅ : Context (Fin 2)) commutativityBody := by
    simpa [A, commutativityBody, termEqual_subst_poly, add_subst, Term.subst] using
      inductAt A (.var 1) p0 ps
  exact closeTwo commutativityBody p

private def associativeAt {α : Type*} {Γ : Context α} (s t u : LA.Term α) :
    Certificate false Γ (termEqual (addTerm (addTerm s t) u) (addTerm s (addTerm t u))) := by
  simpa [associativityBody, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed associativityBody associativityProof ![s,t,u] Γ

private def commutativeAt {α : Type*} {Γ : Context α} (s t : LA.Term α) :
    Certificate false Γ (termEqual (addTerm s t) (addTerm t s)) := by
  simpa [commutativityBody, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed commutativityBody commutativityProof ![s,t] Γ

def exchangeProof : Certificate false (∅ : Context Empty) exchangeSentence := by
  have p : Certificate false (∅ : Context (Fin 3)) exchangeBody :=
    TheoryCertificate.equalTransitivity (associativeAt (.var 0) (.var 1) (.var 2))
      (TheoryCertificate.equalTransitivity
        (TheoryCertificate.addEquality (TheoryCertificate.equalIntro (.var 0))
          (commutativeAt (.var 1) (.var 2)))
        (TheoryCertificate.equalSymmetry (associativeAt (.var 0) (.var 2) (.var 1))))
  exact closeThree exchangeBody p

def cancelLeftProof : Certificate false (∅ : Context Empty) cancelLeftSentence := by
  let A : Formula (Fin 3 ⊕ Unit) := .impl
    (termEqual (addTerm (.var (.inr ())) (.var (.inl 1)))
      (addTerm (.var (.inr ())) (.var (.inl 2))))
    (termEqual (.var (.inl 1)) (.var (.inl 2)))
  have p0 : Certificate false (∅ : Context (Fin 3)) (base A) := by
    have p : Certificate false (∅ : Context (Fin 3))
        (.impl (termEqual (addTerm zeroTerm (.var 1)) (addTerm zeroTerm (.var 2)))
          (termEqual (.var 1) (.var 2))) := by
      apply TheoryCertificate.impIntro
      exact TheoryCertificate.equalTransitivity (TheoryCertificate.equalSymmetry (zeroAt (.var 1)))
        (TheoryCertificate.equalTransitivity
          (TheoryCertificate.assumption (Finset.mem_insert_self _ _)) (zeroAt (.var 2)))
    simpa [A, base, subst_impl, termEqual_subst_poly, add_subst, Term.subst] using p
  let Δ : Context (Fin 3 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let b : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 1)
  let c : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inl 2)
  let u : LA.Term (Fin 3 ⊕ Fin 1) := .var (.inr 0)
  let E : Formula (Fin 3 ⊕ Fin 1) := termEqual (addTerm (succTerm u) b) (addTerm (succTerm u) c)
  have bodyStep : Certificate false Δ (.impl E (termEqual b c)) := by
    apply TheoryCertificate.impIntro
    have e : Certificate false (insert E Δ) E :=
      TheoryCertificate.assumption (Finset.mem_insert_self _ _)
    have ih : Certificate false (insert E Δ)
        (.impl (termEqual (addTerm u b) (addTerm u c)) (termEqual b c)) := by
      have h : Certificate false (insert E Δ) (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) :=
        TheoryCertificate.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      simpa [A, u, b, c, rename, subst_impl, termEqual_subst_poly, add_subst, Term.subst] using h
    have se := TheoryCertificate.equalTransitivity (TheoryCertificate.equalSymmetry (successorAt u b))
      (TheoryCertificate.equalTransitivity e (successorAt u c))
    have reduced := TheoryCertificate.impElim (TheoryCertificate.succInjective basicIn (addTerm u b) (addTerm u c)) se
    exact TheoryCertificate.impElim ih reduced
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, E, u, b, c, rename, subst_impl, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using bodyStep
  have p : Certificate false (∅ : Context (Fin 3)) cancelLeftBody := by
    simpa [A, cancelLeftBody, subst_impl, termEqual_subst_poly, add_subst, Term.subst] using
      inductAt A (.var 0) p0 ps
  exact closeThree cancelLeftBody p

private def cancelLeftAt {α : Type*} {Γ : Context α} (s t u : LA.Term α) :
    Certificate false Γ (.impl (termEqual (addTerm s t) (addTerm s u)) (termEqual t u)) := by
  simpa [cancelLeftBody, subst_impl, termEqual_subst_poly, add_subst, Term.subst] using
    instantiateClosed cancelLeftBody cancelLeftProof ![s,t,u] Γ

def cancelRightProof : Certificate false (∅ : Context Empty) cancelRightSentence := by
  have p : Certificate false (∅ : Context (Fin 3)) cancelRightBody := by
    apply TheoryCertificate.impIntro
    have e : Certificate false (insert (termEqual (addTerm (.var 1) (.var 0))
        (addTerm (.var 2) (.var 0))) (∅ : Context (Fin 3)))
        (termEqual (addTerm (.var 1) (.var 0)) (addTerm (.var 2) (.var 0))) :=
      TheoryCertificate.assumption (Finset.mem_insert_self _ _)
    have e' := TheoryCertificate.equalTransitivity (commutativeAt (.var 0) (.var 1))
      (TheoryCertificate.equalTransitivity e (commutativeAt (.var 2) (.var 0)))
    exact TheoryCertificate.impElim (cancelLeftAt (.var 0) (.var 1) (.var 2)) e'
  exact closeThree cancelRightBody p

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Addition
