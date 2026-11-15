import Lemmatheca.HeytingArithmeticStrongInduction.Syntax
import Lemmatheca.HeytingArithmeticOrder.Certificates

/-! All results are actual original HA certificates, with finite additional context. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.Lemmatheca.ProofTheory.HeytingArithmetic.Order
universe u
variable {α : Type u}
noncomputable section
local instance hasiCertificatesEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _
variable {Γ : Context α}

open TheoryCertificate
open Lemmatheca.MathematicalLogic.FirstOrderProofs
attribute [local simp] atTerm_subst atTerm_rename history_subst history_rename
  negativeHistory_subst negativeHistory_rename minimum_subst minimum_rename
  completePremise_subst completePremise_rename predicateDecision_subst predicateDecision_rename
  minimumExists_subst minimumExists_rename finiteSearch_subst finiteSearch_rename
  historyInductionBody_instance searchInductionBody_instance minimumBody_instance

@[simp] private theorem conjRename (A B : Formula α) {β : Type u} (f : α → β) :
    (.conj A B : Formula α).rename f = .conj (A.rename f) (B.rename f) := rfl
@[simp] private theorem disjRename (A B : Formula α) {β : Type u} (f : α → β) :
    (.disj A B : Formula α).rename f = .disj (A.rename f) (B.rename f) := rfl
@[simp] private theorem implRename (A B : Formula α) {β : Type u} (f : α → β) :
    (.impl A B : Formula α).rename f = .impl (A.rename f) (B.rename f) := rfl
@[simp] private theorem negRename (A : Formula α) {β : Type u} (f : α → β) :
    (.neg A : Formula α).rename f = .neg (A.rename f) := rfl
@[simp] private theorem eqRename (s t : LA.Term α) {β : Type u} (f : α → β) :
    (termEqual s t).rename f = termEqual (s.relabel f) (t.relabel f) := by
  simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, termEqual_subst_poly, term_subst_vars]

private def liftInto {A : Formula α} (p : Certificate false Γ A)
    (B : Formula (α ⊕ Fin 1)) : Certificate false
    (insert B (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
    (A.rename Sum.inl) := (p.universeRename Sum.inl).weaken (Finset.subset_insert _ _)

/-- Instantiate a supplied cumulative history at the supplied internally bounded input. -/
def historyAt (A : Formula (α ⊕ Unit)) (n t : LA.Term α)
    (p : Certificate false Γ (history A n)) (q : Certificate false Γ (ltFormula t n)) :
    Certificate false Γ (atTerm A t) := by
  have h := allUnitElim (.impl (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A) t p
  have h' : Certificate false Γ (.impl (ltFormula t n) (atTerm A t)) := by
    simpa [atTerm, subst_impl, term_subst_relabel, Term.subst] using h
  exact impElim h' q

private def historyIntro (A : Formula (α ⊕ Unit)) (n : LA.Term α)
    (p : Certificate false
      (insert (ltFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (atTerm (parameterRename A Sum.inl) (.var (.inr 0)))) :
    Certificate false Γ (history A n) := by
  apply allUnitIntro (.impl (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) A)
  rw [atTerm_parameterRename_open] at p
  simpa [implRename, ltFormula_rename, Term.relabel_relabel, Term.relabel, Function.comp_def] using impIntro p

private def universalOpen (A : Formula (α ⊕ Unit)) (p : Certificate false Γ (allUnit A)) :
    Certificate false (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1)))
      (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
  have q : Certificate false (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1)))
      (allUnit (parameterRename A Sum.inl)) := by
    simpa only [parameterRename, allUnit_rename] using p.universeRename (Sum.inl : α → α ⊕ Fin 1)
  have r := allUnitElim (parameterRename A Sum.inl) (.var (.inr 0)) q
  change Certificate false _ (atTerm (parameterRename A Sum.inl) (.var (.inr 0))) at r
  simpa only [atTerm_parameterRename_open] using r

private def premiseAt (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (completePremise A)) :
    Certificate false Γ (.impl (history A t) (atTerm A t)) := by
  have q := allUnitElim (.impl (historyInductionBody A) A) t p
  change Certificate false Γ (.impl (atTerm (historyInductionBody A) t) (atTerm A t)) at q
  simpa only [historyInductionBody_instance] using q

/-- Instantiate a supplied internal predicate decision at this actual term. -/
def decisionAt (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (.disj (atTerm A t) (.neg (atTerm A t))) := by
  have q := allUnitElim (.disj A (.neg A)) t p
  simpa only [subst_disj, subst_neg, atTerm] using q



private def negativeAt (A : Formula (α ⊕ Unit)) (n t : LA.Term α)
    (p : Certificate false Γ (negativeHistory A n)) (q : Certificate false Γ (ltFormula t n)) :
    Certificate false Γ (.neg (atTerm A t)) := by
  simpa only [atTerm, subst_neg] using historyAt (.neg A) n t p q

def historyZero (A : Formula (α ⊕ Unit)) : Certificate false Γ (history A zeroTerm) := by
  apply historyIntro A zeroTerm
  simp only [zero_relabel]
  exact falsumElim (negElim (assumption (by simp)) (ltZero (.var (.inr 0))))

def historySuccessor (A : Formula (α ⊕ Unit)) (n : LA.Term α) : Certificate false Γ
    (iffFormula (history A (succTerm n)) (.conj (history A n) (atTerm A n))) := by
  apply conjIntro
  · apply impIntro
    have p : Certificate false (insert (history A (succTerm n)) Γ) (history A (succTerm n)) := assumption (by simp)
    apply conjIntro
    · apply historyIntro A n
      let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
      let n' := n.relabel (Sum.inl : α → α ⊕ Fin 1)
      let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
      let Δ : Context (α ⊕ Fin 1) := insert (ltFormula e n')
        ((insert (history A (succTerm n)) Γ).image (fun E => E.rename Sum.inl))
      have pp : Certificate false Δ (history A' (succTerm n')) := by
        simpa only [history_rename, succ_relabel] using liftInto p (ltFormula e n')
      exact historyAt A' (succTerm n') e pp
        (impElim (conjRight (ltSuccIffLe e n')) (ltToLe e n' (assumption (by simp [e,n']))))
    · exact historyAt A (succTerm n) n p (impElim (conjRight (ltSuccIffLe n n)) (leRefl n))
  · apply impIntro
    have p : Certificate false (insert (.conj (history A n) (atTerm A n)) Γ)
        (.conj (history A n) (atTerm A n)) := assumption (by simp)
    apply historyIntro A (succTerm n)
    simp only [succ_relabel]
    let e : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let n' := n.relabel (Sum.inl : α → α ⊕ Fin 1)
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let Δ : Context (α ⊕ Fin 1) := insert (ltFormula e (succTerm n'))
      ((insert (.conj (history A n) (atTerm A n)) Γ).image (fun E => E.rename Sum.inl))
    have ph : Certificate false Δ (history A' n') := by
      simpa only [history_rename] using liftInto (conjLeft p) (ltFormula e (succTerm n'))
    have pa : Certificate false Δ (atTerm A' n') := by
      simpa only [atTerm_rename] using liftInto (conjRight p) (ltFormula e (succTerm n'))
    apply disjElim (impElim (conjLeft (ltSuccSplit e n')) (assumption (by simp [e,n'])))
    · exact historyAt A' n' e (ph.weaken (Finset.subset_insert _ _)) (assumption (by simp))
    · exact replaceUnit A' n' e (equalSymmetry (assumption (by simp))) (pa.weaken (Finset.subset_insert _ _))

/-- Apply ordinary native induction to the exact cumulative body with fixed parameters. -/
def cumulativeHistories {k} (A : Formula (Fin k ⊕ Unit)) {Γ : Context (Fin k)}
    (p : Certificate false Γ (completePremise A)) :
    Certificate false Γ (allUnit (historyInductionBody A)) := by
  apply inductionRule (historyInductionBody A) Γ
  · rw [historyInductionBody_base]
    exact historyZero A
  · let e : LA.Term (Fin k ⊕ Fin 1) := .var (.inr 0)
    let A' := parameterRename A (Sum.inl : Fin k → Fin k ⊕ Fin 1)
    let I := (historyInductionBody A).rename (Sum.map id (fun _ => (0 : Fin 1)))
    let Δ : Context (Fin k ⊕ Fin 1) := insert I (Γ.image (fun E => E.rename Sum.inl))
    have ih : Certificate false Δ (history A' e) := by
      have q : Certificate false Δ I := assumption (by simp [Δ])
      simpa only [I, historyInductionBody_open] using q
    have pt : Certificate false Δ (completePremise A') := by
      simpa only [completePremise_rename] using liftInto p I
    have pa := impElim (premiseAt A' e pt) ih
    have ps := impElim (conjRight (historySuccessor A' e)) (conjIntro ih pa)
    simpa [historyInductionBody_next, history_rename, parameterRename_comp,
      parameterRename, rename_comp, Term.relabel, Function.comp_def, I, Δ, e, A'] using ps

/-- Transform the supplied complete-induction premise; no predicate decision is needed. -/
def strongInduction {k} (A : Formula (Fin k ⊕ Unit)) {Γ : Context (Fin k)}
    (p : Certificate false Γ (completePremise A)) : Certificate false Γ (allUnit A) := by
  apply allUnitIntro A
  have ph := universalOpen (historyInductionBody A) (cumulativeHistories A p)
  have pt := universalOpen (.impl (historyInductionBody A) A) p
  exact impElim (by simpa only [implRename] using pt) ph

/-- The explicit zero obligation already follows from the supplied complete premise. -/
def strongZero (A : Formula (α ⊕ Unit)) (p : Certificate false Γ (completePremise A)) :
    Certificate false Γ (atTerm A zeroTerm) := by
  exact impElim (premiseAt A zeroTerm p) (historyZero A)

def searchZero (A : Formula (α ⊕ Unit)) : Certificate false Γ (finiteSearch A zeroTerm) := by
  exact disjLeft (historyZero (.neg A))

/-- Preserve this same supplied minimum and increase only its strict search bound. -/
def carrySearchWitness (A : Formula (α ⊕ Unit)) (m n : LA.Term α)
    (p : Certificate false Γ (.conj (ltFormula m n) (minimum A m))) :
    Certificate false Γ (.conj (ltFormula m (succTerm n)) (minimum A m)) := by
  exact conjIntro (impElim (conjRight (ltSuccIffLe m n)) (ltToLe m n (conjLeft p))) (conjRight p)

/-- In the positive test branch the exact new endpoint is the witnessed minimum. -/
def endpointSearchWitness (A : Formula (α ⊕ Unit)) (n : LA.Term α)
    (p : Certificate false Γ (negativeHistory A n)) (q : Certificate false Γ (atTerm A n)) :
    Certificate false Γ (.conj (ltFormula n (succTerm n)) (minimum A n)) := by
  exact conjIntro (impElim (conjRight (ltSuccIffLe n n)) (leRefl n)) (conjIntro q p)

private theorem minimumBodyOpen (A : Formula (α ⊕ Unit)) :
    (minimumBody A).rename (Sum.map id (fun _ => (0 : Fin 1))) =
      minimum (parameterRename A Sum.inl) (.var (.inr (0 : Fin 1))) := by
  unfold minimumBody
  rw [minimum_rename, parameterRename_comp]
  rfl

private def foundBody (A : Formula (α ⊕ Unit)) (n : LA.Term α) : Formula (α ⊕ Unit) :=
  .conj (ltFormula (.var (.inr ())) (n.relabel Sum.inl)) (minimumBody A)

private theorem foundBodyInstance (A : Formula (α ⊕ Unit)) (n m : LA.Term α) :
    atTerm (foundBody A n) m = .conj (ltFormula m n) (minimum A m) := by
  change (.conj ((ltFormula (.var (.inr ())) (n.relabel Sum.inl)).subst
    (Sum.elim Term.var (fun _ => m))) (atTerm (minimumBody A) m) : Formula α) = _
  rw [minimumBody_instance]
  congr 1
  simp [ltFormula_subst, term_subst_relabel, Term.subst]

private theorem foundBodyOpen (A : Formula (α ⊕ Unit)) (n : LA.Term α) :
    (foundBody A n).rename (Sum.map id (fun _ => (0 : Fin 1))) =
      .conj (ltFormula (.var (.inr (0 : Fin 1))) (n.relabel Sum.inl))
        (minimum (parameterRename A Sum.inl) (.var (.inr (0 : Fin 1)))) := by
  simp [foundBody, minimumBodyOpen, ltFormula_rename,
    Term.relabel_relabel, Term.relabel, Function.comp_def]

private def searchFound (A : Formula (α ⊕ Unit)) (n m : LA.Term α)
    (p : Certificate false Γ (.conj (ltFormula m n) (minimum A m))) :
    Certificate false Γ (finiteSearch A n) := by
  apply disjRight
  apply exUnitIntro (foundBody A n) m
  change Certificate false Γ (atTerm (foundBody A n) m)
  simpa only [foundBodyInstance] using p

private def minimumFound (A : Formula (α ⊕ Unit)) (m : LA.Term α)
    (p : Certificate false Γ (minimum A m)) : Certificate false Γ (minimumExists A) := by
  apply exUnitIntro (minimumBody A) m
  change Certificate false Γ (atTerm (minimumBody A) m)
  simpa only [minimumBody_instance] using p

private theorem searchBodyParameterRename {β : Type u} (A : Formula (α ⊕ Unit)) (f : α → β) :
    parameterRename (searchInductionBody A) f = searchInductionBody (parameterRename A f) := by
  change (finiteSearch (parameterRename A Sum.inl) (.var (.inr ()))).rename (Sum.map f id) =
    finiteSearch (parameterRename (parameterRename A f) Sum.inl) (.var (.inr ()))
  rw [finiteSearch_rename, parameterRename_comp, parameterRename_comp]
  rfl

private theorem searchUniversalRename {β : Type u} (A : Formula (α ⊕ Unit)) (f : α → β) :
    (allUnit (searchInductionBody A)).rename f =
      allUnit (searchInductionBody (parameterRename A f)) := by
  rw [← allUnit_rename]
  change allUnit (parameterRename (searchInductionBody A) f) = _
  rw [searchBodyParameterRename]

private def searchAt (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : Certificate false Γ (allUnit (searchInductionBody A))) : Certificate false Γ (finiteSearch A t) := by
  have q := allUnitElim (searchInductionBody A) t p
  change Certificate false Γ (atTerm (searchInductionBody A) t) at q
  simpa only [searchInductionBody_instance] using q


def searchSuccessor (A : Formula (α ⊕ Unit)) (n : LA.Term α)
    (p : Certificate false Γ (predicateDecision A)) (q : Certificate false Γ (finiteSearch A n)) :
    Certificate false Γ (finiteSearch A (succTerm n)) := by
  apply disjElim q
  · have pn : Certificate false (insert (negativeHistory A n) Γ) (negativeHistory A n) := assumption (Finset.mem_insert_self _ _)
    apply disjElim (decisionAt A n (p.weaken (Finset.subset_insert _ _)))
    · exact searchFound A (succTerm n) n
        (endpointSearchWitness A n (pn.weaken (Finset.subset_insert _ _)) (assumption (Finset.mem_insert_self _ _)))
    · apply disjLeft
      exact impElim (conjRight (historySuccessor (.neg A) n))
        (conjIntro (pn.weaken (Finset.subset_insert _ _))
          (by simpa only [atTerm, subst_neg] using
            (assumption (c := false) (T := theory)
              (Γ := insert (.neg (atTerm A n)) (insert (negativeHistory A n) Γ))
              (A := .neg (atTerm A n)) (Finset.mem_insert_self _ _))))
  · let E := exUnit (foundBody A n)
    let Θ : Context α := insert E Γ
    have pe : Certificate false Θ E := assumption (Finset.mem_insert_self _ _)
    apply exUnitEliminate (foundBody A n) (A := finiteSearch A (succTerm n)) pe
    rw [foundBodyOpen, finiteSearch_rename]
    simp only [succ_relabel]
    let A' := parameterRename A (Sum.inl : α → α ⊕ Fin 1)
    let n' := n.relabel (Sum.inl : α → α ⊕ Fin 1)
    let m : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let Δ : Context (α ⊕ Fin 1) := insert (.conj (ltFormula m n') (minimum A' m))
      (Θ.image (fun F => F.rename Sum.inl))
    have pm : Certificate false Δ (.conj (ltFormula m n') (minimum A' m)) := assumption (Finset.mem_insert_self _ _)
    exact searchFound A' (succTerm n') m (carrySearchWitness A' m n' pm)

/-- One ordinary induction on the exact search body, with the supplied decisions fixed. -/
def boundedSearch {k} (A : Formula (Fin k ⊕ Unit)) {Γ : Context (Fin k)}
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (allUnit (searchInductionBody A)) := by
  apply inductionRule (searchInductionBody A) Γ
  · rw [searchInductionBody_base]
    exact searchZero A
  · let e : LA.Term (Fin k ⊕ Fin 1) := .var (.inr 0)
    let A' := parameterRename A (Sum.inl : Fin k → Fin k ⊕ Fin 1)
    let I := (searchInductionBody A).rename (Sum.map id (fun _ => (0 : Fin 1)))
    let Δ : Context (Fin k ⊕ Fin 1) := insert I (Γ.image (fun E => E.rename Sum.inl))
    have ih : Certificate false Δ (finiteSearch A' e) := by
      have q : Certificate false Δ I := assumption (by simp [Δ])
      simpa only [I, searchInductionBody_open] using q
    have pd : Certificate false Δ (predicateDecision A') := by
      simpa only [predicateDecision_rename] using liftInto p I
    have ps := searchSuccessor A' e pd ih
    simpa [searchInductionBody_next, finiteSearch_rename, parameterRename_comp,
      parameterRename, rename_comp, Term.relabel, Function.comp_def, I, Δ, e, A'] using ps

def boundedSearchAt {k} (A : Formula (Fin k ⊕ Unit)) {Γ : Context (Fin k)}
    (p : Certificate false Γ (predicateDecision A)) (t : LA.Term (Fin k)) :
    Certificate false Γ (finiteSearch A t) := by
  have q := allUnitElim (searchInductionBody A) t (boundedSearch A p)
  change Certificate false Γ (atTerm (searchInductionBody A) t) at q
  simpa only [searchInductionBody_instance] using q

/-- Consume both supplied proofs and conclude native existence of a least witness. -/
def leastWitness {k} (A : Formula (Fin k ⊕ Unit)) {Γ : Context (Fin k)}
    (d : Certificate false Γ (predicateDecision A)) (p : Certificate false Γ (exUnit A)) :
    Certificate false Γ (minimumExists A) := by
  have ps := boundedSearch A d
  apply exUnitEliminate A p
  rw [minimumExists_rename]
  let A' := parameterRename A (Sum.inl : Fin k → Fin k ⊕ Fin 1)
  let w : LA.Term (Fin k ⊕ Fin 1) := .var (.inr 0)
  let Aw := A.rename (Sum.map id (fun _ => (0 : Fin 1)))
  let Δ : Context (Fin k ⊕ Fin 1) := insert Aw (Γ.image (fun E => E.rename Sum.inl))
  have pw : Certificate false Δ (atTerm A' w) := by
    rw [atTerm_parameterRename_open]
    exact assumption (Finset.mem_insert_self _ _)
  have pf : Certificate false Δ (allUnit (searchInductionBody A')) := by
    simpa only [searchUniversalRename] using liftInto ps Aw
  apply disjElim (searchAt A' (succTerm w) pf)
  · exact falsumElim (negElim (pw.weaken (Finset.subset_insert _ _))
      (negativeAt A' (succTerm w) w (assumption (Finset.mem_insert_self _ _))
        (impElim (conjRight (ltSuccIffLe w w)) (leRefl w))))
  · apply exUnitEliminate (foundBody A' (succTerm w)) (assumption (Finset.mem_insert_self _ _))
    rw [foundBodyOpen, minimumExists_rename]
    exact minimumFound _ (.var (.inr 0)) (conjRight (assumption (Finset.mem_insert_self _ _)))

def minimumUnique (A : Formula (α ⊕ Unit)) (m n : LA.Term α) : Certificate false Γ
    (.impl (.conj (minimum A m) (minimum A n)) (termEqual m n)) := by
  apply impIntro
  have p : Certificate false (insert (.conj (minimum A m) (minimum A n)) Γ)
      (.conj (minimum A m) (minimum A n)) := assumption (by simp)
  apply disjElim (trichotomy m n)
  · exact falsumElim (negElim ((conjLeft (conjLeft p)).weaken (Finset.subset_insert _ _))
      (negativeAt A n m ((conjRight (conjRight p)).weaken (Finset.subset_insert _ _)) (assumption (by simp))))
  · apply disjElim (assumption (A := .disj (termEqual m n) (ltFormula n m)) (by simp))
    · exact assumption (by simp)
    · exact falsumElim (negElim
        ((conjLeft (conjRight p)).weaken ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))
        (negativeAt A m n
          ((conjRight (conjLeft p)).weaken ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))
          (assumption (by simp))))

def zeroMinimum (A : Formula (α ⊕ Unit)) : Certificate false Γ
    (iffFormula (minimum A zeroTerm) (atTerm A zeroTerm)) := by
  apply conjIntro
  · apply impIntro
    exact conjLeft (assumption (A := minimum A zeroTerm) (by simp))
  · apply impIntro
    exact conjIntro (assumption (by simp)) (historyZero (.neg A))

/-- The distinguished numerical witness is exactly S0, independently of B. -/
def excludedMiddleWitness (B : Formula α) : Certificate false Γ
    (atTerm (excludedMiddlePredicate B) (succTerm zeroTerm)) := by
  unfold atTerm excludedMiddlePredicate
  rw [subst_disj]
  apply disjRight
  simpa only [termEqual_subst_poly, zero_subst, succ_subst, Term.subst, Sum.elim_inr] using
    equalIntro (succTerm zeroTerm)

def excludedMiddleZero (B : Formula α) : Certificate false Γ
    (iffFormula (atTerm (excludedMiddlePredicate B) zeroTerm) B) := by
  have shape : atTerm (excludedMiddlePredicate B) zeroTerm =
      .disj (.conj (termEqual zeroTerm zeroTerm) B) (termEqual zeroTerm (succTerm zeroTerm)) := by
    simp [atTerm, excludedMiddlePredicate, subst_disj, subst_conj,
      termEqual_subst_poly, formula_rename_subst, Term.subst]
  rw [shape]
  apply conjIntro
  · apply impIntro
    apply disjElim (assumption (Finset.mem_insert_self _ _))
    · exact conjRight (assumption (Finset.mem_insert_self _ _))
    · exact falsumElim (negElim (equalSymmetry (assumption (Finset.mem_insert_self _ _)))
        (succNonzero (fun _ h => Or.inl h) zeroTerm))
  · apply impIntro
    exact disjLeft (conjIntro (equalIntro zeroTerm) (assumption (Finset.mem_insert_self _ _)))

/-- A supplied unrestricted least-number instance yields actual native excluded middle. -/

private theorem emParameterRename {β : Type u} (B : Formula α) (f : α → β) :
    parameterRename (excludedMiddlePredicate B) f = excludedMiddlePredicate (B.rename f) := by
  simp [parameterRename, excludedMiddlePredicate,
    rename_comp, Term.relabel, Function.comp_def]

def leastNumberToExcludedMiddle (B : Formula α)
    (p : Certificate false Γ
      (.impl (exUnit (excludedMiddlePredicate B)) (minimumExists (excludedMiddlePredicate B)))) :
    Certificate false Γ (.disj B (.neg B)) := by
  have pe : Certificate false Γ (exUnit (excludedMiddlePredicate B)) := by
    apply exUnitIntro (excludedMiddlePredicate B) (succTerm zeroTerm)
    exact excludedMiddleWitness B
  have pm := impElim p pe
  apply exUnitEliminate (minimumBody (excludedMiddlePredicate B)) pm
  rw [minimumBodyOpen, disjRename, negRename]
  let B' := B.rename (Sum.inl : α → α ⊕ Fin 1)
  let m : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  let M := minimum (parameterRename (excludedMiddlePredicate B) Sum.inl) m
  let Δ : Context (α ⊕ Fin 1) := insert M (Γ.image (fun F => F.rename Sum.inl))
  have hm : Certificate false Δ (minimum (excludedMiddlePredicate B') m) := by
    have q : Certificate false Δ M := assumption (Finset.mem_insert_self _ _)
    simpa only [M, emParameterRename] using q
  apply zeroSuccElim m
  · apply disjLeft
    have eqm : Certificate false (insert (termEqual m zeroTerm) Δ) (termEqual m zeroTerm) :=
      assumption (Finset.mem_insert_self _ _)
    exact impElim (conjLeft (excludedMiddleZero B'))
      (replaceUnit (excludedMiddlePredicate B') m zeroTerm eqm
        ((conjLeft hm).weaken (Finset.subset_insert _ _)))
  · simp only [disjRename, negRename]
    let B'' := B'.rename (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
    let m' := m.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
    let u : LA.Term ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
    let E := termEqual m' (succTerm u)
    let Θ : Context ((α ⊕ Fin 1) ⊕ Fin 1) := insert E (Δ.image (fun F => F.rename Sum.inl))
    have eqm : Certificate false Θ E := assumption (Finset.mem_insert_self _ _)
    have hm' : Certificate false Θ (minimum (excludedMiddlePredicate B'') m') := by
      simpa only [minimum_rename, emParameterRename] using liftInto hm E
    have zlt : Certificate false Θ (ltFormula zeroTerm m') :=
      leCongr (equalIntro (succTerm zeroTerm)) (equalSymmetry eqm)
        (impElim (conjRight (ltSuccIffLe zeroTerm u)) (zeroLe u))
    have nz := negativeAt (excludedMiddlePredicate B'') m' zeroTerm (conjRight hm') zlt
    apply disjRight
    apply negIntro
    exact negElim (impElim (conjRight (excludedMiddleZero B'')) (assumption (Finset.mem_insert_self _ _)))
      (nz.weaken (Finset.subset_insert _ _))

end
end Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction
