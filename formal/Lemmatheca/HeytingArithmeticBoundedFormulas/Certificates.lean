import Lemmatheca.HeytingArithmeticBoundedFormulas.Reindex

/-! Actual intuitionistic original-HA certificate operations on supplied proofs. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.HeytingArithmetic.Order
open Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction

variable {α : Type}
noncomputable section
local instance habfCertificatesEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _
variable {Γ : Context α}
open TheoryCertificate
open Lemmatheca.MathematicalLogic.FirstOrderProofs

@[simp] private theorem conjRename (A B : Formula α) {β : Type} (f : α → β) :
    (.conj A B : Formula α).rename f = .conj (A.rename f) (B.rename f) := rfl
@[simp] private theorem disjRename (A B : Formula α) {β : Type} (f : α → β) :
    (.disj A B : Formula α).rename f = .disj (A.rename f) (B.rename f) := rfl
@[simp] private theorem implRename (A B : Formula α) {β : Type} (f : α → β) :
    (.impl A B : Formula α).rename f = .impl (A.rename f) (B.rename f) := rfl
@[simp] private theorem negRename (A : Formula α) {β : Type} (f : α → β) :
    (.neg A : Formula α).rename f = .neg (A.rename f) := rfl

private def liftInto {A : Formula α} (p : Certificate false Γ A)
    (B : Formula (α ⊕ Fin 1)) : Certificate false
    (insert B (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
    (A.rename Sum.inl) := (p.rename Sum.inl).weaken (Finset.subset_insert _ _)

private def historyIntro (A : Formula (α ⊕ Unit)) (n : LA.Term α)
    (p : Certificate false
      (insert (ltFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (atTerm (parameterRename A Sum.inl) (.var (.inr 0)))) :
    Certificate false Γ (history A n) := by
  apply allUnitIntro (.impl (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A)
  rw [atTerm_parameterRename_open] at p
  simpa [ltFormula_rename, Term.relabel_relabel, Term.relabel, Function.comp_def] using impIntro p

private def inclusiveAllIntro (A : Formula (α ⊕ Unit)) (n : LA.Term α)
    (p : Certificate false
      (insert (leFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (atTerm (parameterRename A Sum.inl) (.var (.inr 0)))) :
    Certificate false Γ (inclusiveAll A n) := by
  apply allUnitIntro (.impl (leFormula (.var (.inr ())) (n.relabel Sum.inl)) A)
  rw [inclusiveAll_body_open]
  rw [atTerm_parameterRename_open] at p
  exact impIntro p

private def inclusiveAllAt (A : Formula (α ⊕ Unit)) (n s : LA.Term α)
    (p : Certificate false Γ (inclusiveAll A n)) (q : Certificate false Γ (leFormula s n)) :
    Certificate false Γ (atTerm A s) := by
  have h := allUnitElim (.impl (leFormula (.var (.inr ())) (n.relabel Sum.inl)) A) s p
  change Certificate false Γ
    (atTerm (.impl (leFormula (.var (.inr ())) (n.relabel Sum.inl)) A) s) at h
  rw [inclusiveAll_body_instance] at h
  exact impElim h q

private def strictExistsIntro (A : Formula (α ⊕ Unit)) (n s : LA.Term α)
    (p : Certificate false Γ (.conj (ltFormula s n) (atTerm A s))) :
    Certificate false Γ (strictExists A n) := by
  apply exUnitIntro (.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A) s
  change Certificate false Γ
    (atTerm (.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A) s)
  simpa only [strictExists_body_instance] using p

private def inclusiveExistsIntro (A : Formula (α ⊕ Unit)) (n s : LA.Term α)
    (p : Certificate false Γ (.conj (leFormula s n) (atTerm A s))) :
    Certificate false Γ (inclusiveExists A n) := by
  apply exUnitIntro (.conj (leFormula (.var (.inr ())) (n.relabel Sum.inl)) A) s
  change Certificate false Γ
    (atTerm (.conj (leFormula (.var (.inr ())) (n.relabel Sum.inl)) A) s)
  simpa only [inclusiveExists_body_instance] using p

private def strictExistsElim (A : Formula (α ⊕ Unit)) (n : LA.Term α) {C : Formula α}
    (p : Certificate false Γ (strictExists A n))
    (q : Certificate false
      (insert (.conj (ltFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (atTerm (parameterRename A Sum.inl) (.var (.inr 0))))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (C.rename Sum.inl)) : Certificate false Γ C := by
  apply exUnitEliminate (.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A) p
  simpa only [strictExists_body_open, atTerm_parameterRename_open] using q

private def inclusiveExistsElim (A : Formula (α ⊕ Unit)) (n : LA.Term α) {C : Formula α}
    (p : Certificate false Γ (inclusiveExists A n))
    (q : Certificate false
      (insert (.conj (leFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (atTerm (parameterRename A Sum.inl) (.var (.inr 0))))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (C.rename Sum.inl)) : Certificate false Γ C := by
  apply exUnitEliminate (.conj (leFormula (.var (.inr ())) (n.relabel Sum.inl)) A) p
  simpa only [inclusiveExists_body_open, atTerm_parameterRename_open] using q

private def belowNext (n : LA.Term α) : Certificate false Γ (ltFormula n (succTerm n)) :=
  impElim (conjRight (ltSuccIffLe n n)) (leRefl n)

private def increaseBound (s n : LA.Term α) (p : Certificate false Γ (ltFormula s n)) :
    Certificate false Γ (ltFormula s (succTerm n)) :=
  impElim (conjRight (ltSuccIffLe s n)) (ltToLe s n p)

private theorem foundBodyOpen (A : Formula (α ⊕ Unit)) (n : LA.Term α) :
    ((.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) (minimumBody A)) : Formula (α ⊕ Unit)).rename
      (Sum.map id (fun _ => (0 : Fin 1))) =
      .conj (ltFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (minimum (parameterRename A Sum.inl) (.var (.inr (0 : Fin 1)))) := by
  simp [minimumBody, minimum_rename, parameterRename_comp, ltFormula_rename,
    Term.relabel_relabel, Term.relabel, Function.comp_def]

private def foundElim (A : Formula (α ⊕ Unit)) (n : LA.Term α) {C : Formula α}
    (p : Certificate false Γ
      (exUnit (.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) (minimumBody A))))
    (q : Certificate false
      (insert (.conj (ltFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (minimum (parameterRename A Sum.inl) (.var (.inr (0 : Fin 1)))))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (C.rename Sum.inl)) : Certificate false Γ C := by
  apply exUnitEliminate (.conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) (minimumBody A)) p
  simpa only [foundBodyOpen] using q

def falsumDecision : Certificate false Γ (.disj .falsum (.neg .falsum)) := by
  exact disjRight (negIntro (assumption (Finset.mem_insert_self _ _)))

def negDecision (A : Formula α) (p : Certificate false Γ (.disj A (.neg A))) :
    Certificate false Γ (.disj (.neg A) (.neg (.neg A))) := by
  apply disjElim p
  · apply disjRight
    apply negIntro
    exact negElim (assumption (A := A) (by simp)) (assumption (A := .neg A) (by simp))
  · exact disjLeft (assumption (by simp))

def conjDecision (A B : Formula α)
    (p : Certificate false Γ (.disj A (.neg A)))
    (q : Certificate false Γ (.disj B (.neg B))) :
    Certificate false Γ (.disj (.conj A B) (.neg (.conj A B))) := by
  apply disjElim p
  · apply disjElim (q.weaken (Finset.subset_insert _ _))
    · exact disjLeft (conjIntro (assumption (by simp)) (assumption (by simp)))
    · apply disjRight
      apply negIntro
      exact negElim (conjRight (assumption (A := .conj A B) (by simp)))
        (assumption (by simp))
  · apply disjRight
    apply negIntro
    exact negElim (conjLeft (assumption (A := .conj A B) (by simp)))
      (assumption (by simp))

def disjDecision (A B : Formula α)
    (p : Certificate false Γ (.disj A (.neg A)))
    (q : Certificate false Γ (.disj B (.neg B))) :
    Certificate false Γ (.disj (.disj A B) (.neg (.disj A B))) := by
  apply disjElim p
  · exact disjLeft (disjLeft (assumption (by simp)))
  · apply disjElim (q.weaken (Finset.subset_insert _ _))
    · exact disjLeft (disjRight (assumption (by simp)))
    · apply disjRight
      apply negIntro
      apply disjElim (assumption (A := .disj A B) (by simp))
      · exact negElim (assumption (A := A) (by simp)) (assumption (A := .neg A) (by simp))
      · exact negElim (assumption (A := B) (by simp)) (assumption (A := .neg B) (by simp))

def implDecision (A B : Formula α)
    (p : Certificate false Γ (.disj A (.neg A)))
    (q : Certificate false Γ (.disj B (.neg B))) :
    Certificate false Γ (.disj (.impl A B) (.neg (.impl A B))) := by
  apply disjElim p
  · apply disjElim (q.weaken (Finset.subset_insert _ _))
    · exact disjLeft (impIntro (assumption (A := B) (by simp)))
    · apply disjRight
      apply negIntro
      exact negElim
        (impElim (assumption (A := .impl A B) (by simp)) (assumption (A := A) (by simp)))
        (assumption (A := .neg B) (by simp))
  · apply disjLeft
    apply impIntro
    exact falsumElim (negElim (assumption (A := A) (by simp))
      (assumption (A := .neg A) (by simp)))

def stabilityFromDecision (A : Formula α)
    (p : Certificate false Γ (.disj A (.neg A))) :
    Certificate false Γ (.impl (.neg (.neg A)) A) := by
  apply impIntro
  apply disjElim (p.weaken (Finset.subset_insert _ _))
  · exact assumption (by simp)
  · exact falsumElim (negElim (assumption (A := .neg A) (by simp))
      (assumption (A := .neg (.neg A)) (by simp)))

def negativePredicateDecision (A : Formula (α ⊕ Unit))
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (predicateDecision (.neg A)) := by
  apply allUnitIntro (.disj (.neg A) (.neg (.neg A)))
  let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
  have pd : Certificate false (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1)))
      (predicateDecision A') := by
    simpa only [predicateDecision_rename] using p.rename (Sum.inl : α → α ⊕ Fin 1)
  have q := negDecision (atTerm A' e) (decisionAt A' e pd)
  simpa only [A', e, atTerm_parameterRename_open, disjRename, negRename] using q

def strictExistsZero (A : Formula (α ⊕ Unit)) :
    Certificate false Γ (.neg (strictExists A zeroTerm)) := by
  apply negIntro
  apply strictExistsElim A zeroTerm (assumption (by simp))
  simp only [zero_relabel]
  let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
  let Δ : Context (α ⊕ Fin 1) := insert
    (.conj (ltFormula e zeroTerm) (atTerm A' e))
    ((insert (strictExists A zeroTerm) Γ).image (fun E => E.rename Sum.inl))
  have q : Certificate false Δ (.conj (ltFormula e zeroTerm) (atTerm A' e)) :=
    assumption (by simp [Δ])
  exact negElim (conjLeft q) (ltZero e)

def inclusiveAllZero (A : Formula (α ⊕ Unit)) :
    Certificate false Γ (iffFormula (inclusiveAll A zeroTerm) (atTerm A zeroTerm)) := by
  apply conjIntro
  · apply impIntro
    exact inclusiveAllAt A zeroTerm zeroTerm (assumption (by simp)) (leRefl zeroTerm)
  · apply impIntro
    have p : Certificate false (insert (atTerm A zeroTerm) Γ) (atTerm A zeroTerm) :=
      assumption (by simp)
    apply inclusiveAllIntro A zeroTerm
    simp only [zero_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) := insert (leFormula e zeroTerm)
      ((insert (atTerm A zeroTerm) Γ).image (fun E => E.rename Sum.inl))
    have eq : Certificate false Δ (termEqual e zeroTerm) :=
      impElim (conjLeft (leZero e)) (assumption (by simp [Δ]))
    have pa : Certificate false Δ (atTerm A' zeroTerm) := by
      simpa only [atTerm_rename, zero_relabel] using liftInto p (leFormula e zeroTerm)
    exact replaceUnit A' zeroTerm e (equalSymmetry eq) pa

def inclusiveExistsZero (A : Formula (α ⊕ Unit)) :
    Certificate false Γ (iffFormula (inclusiveExists A zeroTerm) (atTerm A zeroTerm)) := by
  apply conjIntro
  · apply impIntro
    apply inclusiveExistsElim A zeroTerm (assumption (by simp))
    rw [atTerm_rename]
    simp only [zero_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    have p : Certificate false
        (insert (.conj (leFormula e zeroTerm) (atTerm A' e))
          ((insert (inclusiveExists A zeroTerm) Γ).image (fun E => E.rename Sum.inl)))
        (.conj (leFormula e zeroTerm) (atTerm A' e)) := assumption (by simp)
    exact replaceUnit A' e zeroTerm
      (impElim (conjLeft (leZero e)) (conjLeft p)) (conjRight p)
  · apply impIntro
    exact inclusiveExistsIntro A zeroTerm zeroTerm
      (conjIntro (leRefl zeroTerm) (assumption (by simp)))

def strictExistsSuccessor (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    Certificate false Γ (iffFormula (strictExists A (succTerm t))
      (.disj (strictExists A t) (atTerm A t))) := by
  apply conjIntro
  · apply impIntro
    apply strictExistsElim A (succTerm t) (assumption (by simp))
    rw [disjRename, strictExists_rename, atTerm_rename]
    simp only [succ_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) :=
      insert (.conj (ltFormula e (succTerm t')) (atTerm A' e))
        ((insert (strictExists A (succTerm t)) Γ).image (fun E => E.rename Sum.inl))
    have p : Certificate false Δ (.conj (ltFormula e (succTerm t')) (atTerm A' e)) :=
      assumption (by simp [Δ])
    apply disjElim (impElim (conjLeft (ltSuccSplit e t')) (conjLeft p))
    · apply disjLeft
      exact strictExistsIntro A' t' e
        (conjIntro (assumption (by simp)) ((conjRight p).weaken (Finset.subset_insert _ _)))
    · apply disjRight
      exact replaceUnit A' e t' (assumption (by simp))
        ((conjRight p).weaken (Finset.subset_insert _ _))
  · apply impIntro
    apply disjElim (assumption (A := .disj (strictExists A t) (atTerm A t)) (by simp))
    · apply strictExistsElim A t (assumption (by simp))
      rw [strictExists_rename]
      simp only [succ_relabel]
      let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
      let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
      let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
      let Θ : Context α := insert (strictExists A t)
        (insert (.disj (strictExists A t) (atTerm A t)) Γ)
      have p : Certificate false
          (insert (.conj (ltFormula e t') (atTerm A' e))
            (Θ.image (fun E => E.rename Sum.inl)))
          (.conj (ltFormula e t') (atTerm A' e)) := assumption (by simp)
      exact strictExistsIntro A' (succTerm t') e
        (conjIntro (increaseBound e t' (conjLeft p)) (conjRight p))
    · exact strictExistsIntro A (succTerm t) t
        (conjIntro (belowNext t) (assumption (by simp)))

def inclusiveAllStrict (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    Certificate false Γ (iffFormula (inclusiveAll A t) (history A (succTerm t))) := by
  apply conjIntro
  · apply impIntro
    have p : Certificate false (insert (inclusiveAll A t) Γ) (inclusiveAll A t) :=
      assumption (by simp)
    apply historyIntro A (succTerm t)
    simp only [succ_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) := insert (ltFormula e (succTerm t'))
      ((insert (inclusiveAll A t) Γ).image (fun E => E.rename Sum.inl))
    have pp : Certificate false Δ (inclusiveAll A' t') := by
      simpa only [inclusiveAll_rename] using liftInto p (ltFormula e (succTerm t'))
    exact inclusiveAllAt A' t' e pp
      (impElim (conjLeft (ltSuccIffLe e t')) (assumption (by simp [e, t'])))
  · apply impIntro
    have p : Certificate false (insert (history A (succTerm t)) Γ)
        (history A (succTerm t)) := assumption (by simp)
    apply inclusiveAllIntro A t
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) := insert (leFormula e t')
      ((insert (history A (succTerm t)) Γ).image (fun E => E.rename Sum.inl))
    have pp : Certificate false Δ (history A' (succTerm t')) := by
      simpa only [history_rename, succ_relabel] using liftInto p (leFormula e t')
    exact historyAt A' (succTerm t') e pp
      (impElim (conjRight (ltSuccIffLe e t')) (assumption (by simp [e, t'])))

def inclusiveExistsStrict (A : Formula (α ⊕ Unit)) (t : LA.Term α) :
    Certificate false Γ (iffFormula (inclusiveExists A t) (strictExists A (succTerm t))) := by
  apply conjIntro
  · apply impIntro
    apply inclusiveExistsElim A t (assumption (by simp))
    rw [strictExists_rename]
    simp only [succ_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) := insert (.conj (leFormula e t') (atTerm A' e))
      ((insert (inclusiveExists A t) Γ).image (fun E => E.rename Sum.inl))
    have q : Certificate false Δ (.conj (leFormula e t') (atTerm A' e)) :=
      assumption (by simp [Δ])
    exact strictExistsIntro A' (succTerm t') e
      (conjIntro (impElim (conjRight (ltSuccIffLe e t')) (conjLeft q)) (conjRight q))
  · apply impIntro
    apply strictExistsElim A (succTerm t) (assumption (by simp))
    rw [inclusiveExists_rename]
    simp only [succ_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) := insert (.conj (ltFormula e (succTerm t')) (atTerm A' e))
      ((insert (strictExists A (succTerm t)) Γ).image (fun E => E.rename Sum.inl))
    have q : Certificate false Δ (.conj (ltFormula e (succTerm t')) (atTerm A' e)) :=
      assumption (by simp [Δ])
    exact inclusiveExistsIntro A' t' e
      (conjIntro (impElim (conjLeft (ltSuccIffLe e t')) (conjLeft q)) (conjRight q))

private def negativeAt (A : Formula (α ⊕ Unit)) (n t : LA.Term α)
    (p : Certificate false Γ (negativeHistory A n)) (q : Certificate false Γ (ltFormula t n)) :
    Certificate false Γ (.neg (atTerm A t)) := by
  simpa only [atTerm, subst_neg] using historyAt (.neg A) n t p q

private def decisionAlongIff (A B : Formula α)
    (p : Certificate false Γ (.disj B (.neg B)))
    (h : Certificate false Γ (iffFormula A B)) :
    Certificate false Γ (.disj A (.neg A)) := by
  apply disjElim p
  · exact disjLeft (impElim ((conjRight h).weaken (Finset.subset_insert _ _))
      (assumption (by simp)))
  · apply disjRight
    apply negIntro
    have q : Certificate false (insert A (insert (.neg B) Γ)) (.impl A B) :=
      (conjLeft h).weaken (by intro C hC; simp [hC])
    exact negElim (impElim q (assumption (by simp))) (assumption (by simp))

def strictExistsDecision [Fintype α] (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (.disj (strictExists A t) (.neg (strictExists A t))) := by
  apply disjElim (searchByEquiv (Fintype.equivFin α) A t p)
  · apply disjRight
    apply negIntro
    let Θ : Context α := insert (strictExists A t) (insert (negativeHistory A t) Γ)
    have pn : Certificate false Θ (negativeHistory A t) := assumption (by simp [Θ])
    apply strictExistsElim A t (assumption (by simp))
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let W : Formula (α ⊕ Fin 1) := .conj (ltFormula e t') (atTerm A' e)
    let Δ : Context (α ⊕ Fin 1) := insert W (Θ.image (fun E => E.rename Sum.inl))
    have w : Certificate false Δ W := assumption (by simp [Δ])
    have pn' : Certificate false Δ (negativeHistory A' t') := by
      simpa only [negativeHistory_rename] using liftInto pn W
    exact negElim (conjRight w) (negativeAt A' t' e pn' (conjLeft w))
  · apply foundElim A t (assumption (by simp))
    simp only [disjRename, negRename, strictExists_rename]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let F : Formula α :=
      exUnit (.conj (ltFormula (.var (.inr ())) (t.relabel Sum.inl)) (minimumBody A))
    let W : Formula (α ⊕ Fin 1) := .conj (ltFormula e t') (minimum A' e)
    let Δ : Context (α ⊕ Fin 1) := insert W
      ((insert F Γ).image (fun E => E.rename Sum.inl))
    have w : Certificate false Δ W := assumption (by simp [Δ])
    exact disjLeft (strictExistsIntro A' t' e
      (conjIntro (conjLeft w) (conjLeft (conjRight w))))

def strictAllDecision [Fintype α] (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (.disj (history A t) (.neg (history A t))) := by
  have pd := negativePredicateDecision A p
  apply disjElim (searchByEquiv (Fintype.equivFin α) (.neg A) t pd)
  · apply disjLeft
    apply historyIntro A t
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Θ : Context α := insert (negativeHistory (.neg A) t) Γ
    let Δ : Context (α ⊕ Fin 1) := insert (ltFormula e t')
      (Θ.image (fun E => E.rename Sum.inl))
    have pn : Certificate false Θ (negativeHistory (.neg A) t) := assumption (by simp [Θ])
    have pn' : Certificate false Δ (negativeHistory (.neg A') t') := by
      simpa only [negativeHistory_rename, A', parameterRename, negRename] using
        liftInto pn (ltFormula e t')
    have pd' : Certificate false Δ (predicateDecision A') := by
      simpa only [predicateDecision_rename] using
        liftInto (p.weaken (Finset.subset_insert _ _)) (ltFormula e t')
    have nn : Certificate false Δ (.neg (.neg (atTerm A' e))) := by
      simpa only [atTerm, subst_neg] using
        negativeAt (.neg A') t' e pn' (assumption (by simp [Δ]))
    exact impElim (stabilityFromDecision (atTerm A' e) (decisionAt A' e pd')) nn
  · apply foundElim (.neg A) t (assumption (by simp))
    simp only [disjRename, negRename, history_rename]
    apply disjRight
    apply negIntro
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let t' := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let F : Formula α :=
      exUnit (.conj (ltFormula (.var (.inr ())) (t.relabel Sum.inl)) (minimumBody (.neg A)))
    let W : Formula (α ⊕ Fin 1) := .conj (ltFormula e t')
      (minimum (parameterRename (.neg A) (Sum.inl : α → α ⊕ Fin 1)) e)
    let Δ : Context (α ⊕ Fin 1) := insert (history A' t')
      (insert W ((insert F Γ).image (fun E => E.rename Sum.inl)))
    have w : Certificate false Δ W := assumption (by simp [Δ])
    have hu : Certificate false Δ (history A' t') := assumption (by simp [Δ])
    have hn : Certificate false Δ (.neg (atTerm A' e)) := by
      simpa only [A', atTerm, parameterRename, negRename, subst_neg] using conjLeft (conjRight w)
    exact negElim (historyAt A' t' e hu (conjLeft w)) hn

def inclusiveAllDecision [Fintype α] (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (.disj (inclusiveAll A t) (.neg (inclusiveAll A t))) := by
  exact decisionAlongIff _ _ (strictAllDecision A (succTerm t) p) (inclusiveAllStrict A t)

def inclusiveExistsDecision [Fintype α] (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (.disj (inclusiveExists A t) (.neg (inclusiveExists A t))) := by
  exact decisionAlongIff _ _ (strictExistsDecision A (succTerm t) p) (inclusiveExistsStrict A t)

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
