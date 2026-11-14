import Lemmatheca.HeytingArithmetic.Induction

namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder (liftScope scopeInclusion)
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe w w'
variable {α : Type w} {β : Type w'} {c : Bool}
noncomputable section
local instance haEqualityEq {δ : Type w} : DecidableEq (Formula δ) := Classical.decEq _

/-- Logical equality alone transports the successor argument. -/
def succCongr {Γ : Context α} {s t : LA.Term α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual s t)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ
      (termEqual (succTerm s) (succTerm t)) := by
  let D : BF α 1 := .equal ((succTerm s).relabel Sum.inl) (succTerm (.var (.inr 0)))
  have inst (r : LA.Term α) : D.instantiate r = termEqual (succTerm s) (succTerm r) := by
    simp [D, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots, map, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
      term_subst_relabel, term_subst_vars, Term.subst, succ_subst, succ_relabel]
  have q := Proof.equalElim D s t p
    (by simpa only [inst] using Proof.equalIntro (c := c) (Γ := Γ) (succTerm s))
  simpa only [inst] using q

private def binaryTerm (f : LA.Functions 2) (s t : LA.Term α) : LA.Term α := .func f ![s,t]
private theorem binary_subst (f : LA.Functions 2) (s t : LA.Term α) (σ : α → LA.Term β) :
    (binaryTerm f s t).subst σ = binaryTerm f (s.subst σ) (t.subst σ) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl
private theorem binary_relabel (f : LA.Functions 2) (s t : LA.Term α) (g : α → β) :
    (binaryTerm f s t).relabel g = binaryTerm f (s.relabel g) (t.relabel g) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl

private def binaryCongr (f : LA.Functions 2) {Γ : Context α} {s t u v : LA.Term α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual s t))
    (q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual u v)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ
      (termEqual (binaryTerm f s u) (binaryTerm f t v)) := by
  let D : BF α 1 := .equal ((binaryTerm f s u).relabel Sum.inl)
    (binaryTerm f (.var (.inr 0)) (u.relabel Sum.inl))
  have instD (r : LA.Term α) : D.instantiate r = termEqual (binaryTerm f s u) (binaryTerm f r u) := by
    simp [D, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots, map, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
      term_subst_relabel, term_subst_vars, binary_subst, binary_relabel, Term.subst]
  have h1 := Proof.equalElim D s t p
    (by simpa only [instD] using Proof.equalIntro (c := c) (Γ := Γ) (binaryTerm f s u))
  let E : BF α 1 := .equal ((binaryTerm f t u).relabel Sum.inl)
    (binaryTerm f (t.relabel Sum.inl) (.var (.inr 0)))
  have instE (r : LA.Term α) : E.instantiate r = termEqual (binaryTerm f t u) (binaryTerm f t r) := by
    simp [E, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots, map, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
      term_subst_relabel, term_subst_vars, binary_subst, binary_relabel, Term.subst]
  have h2 := Proof.equalElim E u v q
    (by simpa only [instE] using Proof.equalIntro (c := c) (Γ := Γ) (binaryTerm f t u))
  exact Proof.equalTransitivity (by simpa only [instD] using h1) (by simpa only [instE] using h2)

/-- Two supplied equality proofs are composed in the same ambient context. -/
def addCongr {Γ : Context α} {s t u v : LA.Term α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual s t))
    (q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual u v)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ
      (termEqual (addTerm s u) (addTerm t v)) := by
  exact binaryCongr .add p q

def mulCongr {Γ : Context α} {s t u v : LA.Term α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual s t))
    (q : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ (termEqual u v)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof c true LA Γ
      (termEqual (mulTerm s u) (mulTerm t v)) := by
  exact binaryCongr .mul p q

namespace TheoryCertificate
variable {T : Set Sentence} {Γ : Context α}
def equalSymmetry {s t : LA.Term α} (p : TheoryCertificate c T Γ (termEqual s t)) :
    TheoryCertificate c T Γ (termEqual t s) :=
  ⟨p.assumptions, p.allowed, Proof.equalSymmetry p.derivation⟩
def equalTransitivity {s t u : LA.Term α}
    (p : TheoryCertificate c T Γ (termEqual s t)) (q : TheoryCertificate c T Γ (termEqual t u)) :
    TheoryCertificate c T Γ (termEqual s u) := combine p q (fun _ => Proof.equalTransitivity)
def succEquality {s t : LA.Term α} (p : TheoryCertificate c T Γ (termEqual s t)) :
    TheoryCertificate c T Γ (termEqual (succTerm s) (succTerm t)) :=
  ⟨p.assumptions, p.allowed, succCongr p.derivation⟩
def addEquality {s t u v : LA.Term α}
    (p : TheoryCertificate c T Γ (termEqual s t)) (q : TheoryCertificate c T Γ (termEqual u v)) :
    TheoryCertificate c T Γ (termEqual (addTerm s u) (addTerm t v)) :=
  combine p q (fun _ => addCongr)
def mulEquality {s t u v : LA.Term α}
    (p : TheoryCertificate c T Γ (termEqual s t)) (q : TheoryCertificate c T Γ (termEqual u v)) :
    TheoryCertificate c T Γ (termEqual (mulTerm s u) (mulTerm t v)) :=
  combine p q (fun _ => mulCongr)
end TheoryCertificate

namespace TheoryCertificate
variable {T : Set Sentence} {Γ : Context α}
def basicInstance (hT : basic ⊆ T) {k} (D : Formula (Fin k)) (hD : close D ∈ basic)
    (ts : Fin k → LA.Term α) : TheoryCertificate false T Γ (D.subst ts) :=
  closeElim D ts (fromAxiom (close D) (hT hD))

def succNonzero (hT : basic ⊆ T) (t : LA.Term α) :
    TheoryCertificate false T Γ (.neg (termEqual (succTerm t) zeroTerm)) := by
  let D : Formula (Fin 1) := .neg (termEqual (succTerm (.var 0)) zeroTerm)
  have p := basicInstance (Γ := Γ) hT D (by change qSuccNeZero ∈ basic; simp [basic]) ![t]
  simpa [D, subst_neg, termEqual_subst_poly, succ_subst, zero_subst, Term.subst] using p

def succInjective (hT : basic ⊆ T) (s t : LA.Term α) :
    TheoryCertificate false T Γ (.impl (termEqual (succTerm s) (succTerm t)) (termEqual s t)) := by
  let D : Formula (Fin 2) := .impl
    (termEqual (succTerm (.var 0)) (succTerm (.var 1))) (termEqual (.var 0) (.var 1))
  have p := basicInstance (Γ := Γ) hT D (by change qSuccInjective ∈ basic; simp [basic]) ![s,t]
  simpa [D, subst_impl, termEqual_subst_poly, succ_subst, Term.subst] using p

def addZero (hT : basic ⊆ T) (t : LA.Term α) :
    TheoryCertificate false T Γ (termEqual (addTerm t zeroTerm) t) := by
  let D : Formula (Fin 1) := termEqual (addTerm (.var 0) zeroTerm) (.var 0)
  have p := basicInstance (Γ := Γ) hT D (by change qAddZero ∈ basic; simp [basic]) ![t]
  simpa [D, termEqual_subst_poly, add_subst, zero_subst, Term.subst] using p

def addSucc (hT : basic ⊆ T) (s t : LA.Term α) :
    TheoryCertificate false T Γ (termEqual (addTerm s (succTerm t)) (succTerm (addTerm s t))) := by
  let D : Formula (Fin 2) := termEqual
    (addTerm (.var 0) (succTerm (.var 1))) (succTerm (addTerm (.var 0) (.var 1)))
  have p := basicInstance (Γ := Γ) hT D (by change qAddSucc ∈ basic; simp [basic]) ![s,t]
  simpa [D, termEqual_subst_poly, add_subst, succ_subst, Term.subst] using p

def mulZero (hT : basic ⊆ T) (t : LA.Term α) :
    TheoryCertificate false T Γ (termEqual (mulTerm t zeroTerm) zeroTerm) := by
  let D : Formula (Fin 1) := termEqual (mulTerm (.var 0) zeroTerm) zeroTerm
  have p := basicInstance (Γ := Γ) hT D (by change qMulZero ∈ basic; simp [basic]) ![t]
  simpa [D, termEqual_subst_poly, mul_subst, zero_subst, Term.subst] using p

def mulSucc (hT : basic ⊆ T) (s t : LA.Term α) :
    TheoryCertificate false T Γ (termEqual (mulTerm s (succTerm t)) (addTerm (mulTerm s t) s)) := by
  let D : Formula (Fin 2) := termEqual
    (mulTerm (.var 0) (succTerm (.var 1))) (addTerm (mulTerm (.var 0) (.var 1)) (.var 0))
  have p := basicInstance (Γ := Γ) hT D (by change qMulSucc ∈ basic; simp [basic]) ![s,t]
  simpa [D, termEqual_subst_poly, mul_subst, add_subst, succ_subst, Term.subst] using p
end TheoryCertificate

/-- The zero case is itself an internal constructive induction proof. -/
def zeroEqualityDecisionProof : Certificate false (∅ : Context Empty) zeroEqualityDecision := by
  let A : Formula (Fin 0 ⊕ Unit) := .disj (termEqual zeroTerm (.var (.inr ())))
    (.neg (termEqual zeroTerm (.var (.inr ()))))
  have p0 : Certificate false (∅ : Context (Fin 0)) (base A) := by
    unfold base
    dsimp only [A]
    rw [subst_disj, termEqual_subst_poly]
    simp only [Term.subst, Sum.elim_inr, zero_subst]
    exact TheoryCertificate.disjLeft (TheoryCertificate.equalIntro zeroTerm)
  let Γ : Context (Fin 0 ⊕ Fin 1) :=
    insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let u : LA.Term (Fin 0 ⊕ Fin 1) := .var (.inr 0)
  have pn : Certificate false Γ (.neg (termEqual zeroTerm (succTerm u))) := by
    apply TheoryCertificate.negIntro
    exact TheoryCertificate.negElim
      (TheoryCertificate.equalSymmetry (TheoryCertificate.assumption (Finset.mem_insert_self _ _)))
      (TheoryCertificate.succNonzero (fun _ h => Or.inl h) u)
  have ps : Certificate false Γ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, u, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      subst_disj, subst_neg, termEqual_subst_poly, succ_subst, zero_subst, Term.subst] using
      (TheoryCertificate.disjRight (A := termEqual zeroTerm (succTerm u)) pn)
  have p := inductionRule A ∅ p0 (by simpa only [Γ, Finset.image_empty] using ps)
  have q := p.rename (Fin.elim0 : Fin 0 → Empty)
  let D : Formula (Fin 1) := .disj (termEqual zeroTerm (.var 0)) (.neg (termEqual zeroTerm (.var 0)))
  change Certificate false (∅ : Context Empty) (close D)
  simpa [A, D, close, allSlots, allUnit, bindUnit, liftScope, scopeInclusion,
    lastCases_one, lastCases_two_zero, lastCases_two_one,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
    term_subst_relabel, term_subst_vars, Term.relabel_relabel,
    zero_relabel, succ_relabel, Term.subst, Term.relabel, Finset.image_empty] using q

def equalityAlternative (s t : LA.Term α) : Formula α := .disj (termEqual s t) (.neg (termEqual s t))
@[simp] theorem equalityAlternative_subst (s t : LA.Term α) (σ : α → LA.Term β) :
    (equalityAlternative s t).subst σ = equalityAlternative (s.subst σ) (t.subst σ) := by
  simp only [equalityAlternative, subst_disj, subst_neg, termEqual_subst_poly]

def equalEverywhere (s : LA.Term α) : Formula α :=
  allUnit (equalityAlternative (s.relabel Sum.inl) (.var (.inr ())))
@[simp] theorem equalEverywhere_subst (s : LA.Term α) (σ : α → LA.Term β) :
    (equalEverywhere s).subst σ = equalEverywhere (s.subst σ) := by
  simp [equalEverywhere, allUnit_subst, equalityAlternative_subst,
    unitSubst, term_subst_relabel, term_relabel_subst, Term.subst]
@[simp] theorem equalEverywhere_rename (s : LA.Term α) (f : α → β) :
    (equalEverywhere s).rename f = equalEverywhere (s.relabel f) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    equalEverywhere_subst, term_subst_vars]

theorem close_one_allUnit (D : Formula (Fin 1)) :
    (close D).rename (Empty.elim : Empty → α) =
      allUnit (D.rename (fun _ : Fin 1 => (Sum.inr () : α ⊕ Unit))) := by
  rw [close_rename]
  unfold allSlots allUnit bindUnit Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp]
  congr 2
  apply congrArg (D.map)
  funext z
  cases z with
  | inl i => have hi : i = 0 := Fin.eq_zero i; subst i; rfl
  | inr i => exact i.elim0

namespace TheoryCertificate
variable {Γ : Context α}
def everywhereAt (s t : LA.Term α) (p : Certificate false Γ (equalEverywhere s)) :
    Certificate false Γ (equalityAlternative s t) := by
  have q := allUnitElim (equalityAlternative (s.relabel Sum.inl) (.var (.inr ()))) t p
  simpa [equalityAlternative_subst, term_subst_relabel, Term.subst] using q
end TheoryCertificate

def zeroEverywhere : Certificate false (∅ : Context α) (equalEverywhere (zeroTerm : LA.Term α)) := by
  let D : Formula (Fin 1) := equalityAlternative zeroTerm (.var 0)
  have hd : zeroEqualityDecision = close D := rfl
  have q := zeroEqualityDecisionProof.universeRename (Empty.elim : Empty → α)
  rw [hd, close_one_allUnit] at q
  simpa [D, equalEverywhere, equalityAlternative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    subst_disj, subst_neg, termEqual_subst_poly, zero_subst, zero_relabel,
    Term.subst, Finset.image_empty] using q

def successorEverywhere : Certificate false (∅ : Context (Fin 1))
    (.impl (equalEverywhere (.var 0)) (equalEverywhere (succTerm (.var 0)))) := by
  let IH : Formula (Fin 1) := equalEverywhere (.var 0)
  let Γ : Context (Fin 1) := {IH}
  let B : Formula (Fin 1 ⊕ Unit) := equalityAlternative (succTerm (.var (.inl 0))) (.var (.inr ()))
  have p0 : Certificate false Γ (base B) := by
    unfold base
    dsimp only [B]
    rw [equalityAlternative_subst]
    simp only [succ_subst, Term.subst, Sum.elim_inl, Sum.elim_inr]
    exact TheoryCertificate.disjRight (TheoryCertificate.succNonzero (fun _ h => Or.inl h) (.var 0))
  let Δ : Context (Fin 1 ⊕ Fin 1) :=
    insert (B.rename (Sum.map id (fun _ => (0 : Fin 1))))
      (Γ.image (fun A => A.rename Sum.inl))
  let u : LA.Term (Fin 1 ⊕ Fin 1) := .var (.inl 0)
  let v : LA.Term (Fin 1 ⊕ Fin 1) := .var (.inr 0)
  have pIH : Certificate false Δ (equalEverywhere u) := by
    have p : Certificate false Δ (IH.rename (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)) :=
      TheoryCertificate.assumption (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨IH, Finset.mem_singleton_self _, rfl⟩))
    simpa [IH, u, equalEverywhere_rename, Term.relabel] using p
  have duv := TheoryCertificate.everywhereAt u v pIH
  have ds : Certificate false Δ (equalityAlternative (succTerm u) (succTerm v)) := by
    apply TheoryCertificate.disjElim duv
    · exact TheoryCertificate.disjLeft (TheoryCertificate.succEquality
        (TheoryCertificate.assumption (Finset.mem_insert_self _ _)))
    · apply TheoryCertificate.disjRight
      apply TheoryCertificate.negIntro
      exact TheoryCertificate.negElim
        (TheoryCertificate.impElim
          (TheoryCertificate.succInjective (fun _ h => Or.inl h) u v)
          (TheoryCertificate.assumption (Finset.mem_insert_self _ _)))
        (TheoryCertificate.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have ps : Certificate false Δ ((next B).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [B, next, u, v, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      equalityAlternative_subst, succ_subst, Term.subst] using ds
  have p := inductionRule B Γ p0 (by simpa only [Δ] using ps)
  have p' : Certificate false (insert (equalEverywhere (.var (0 : Fin 1))) (∅ : Context (Fin 1)))
      (equalEverywhere (succTerm (.var 0))) := by
    simpa only [equalEverywhere, succ_relabel, Γ, IH, B, Term.relabel, Finset.insert_empty] using p
  exact TheoryCertificate.impIntro p'

/-- Two native induction instances produce the universal equality disjunction. -/
def equalityDecisionProof : Certificate false (∅ : Context Empty) equalityDecision := by
  let A : Formula (Fin 0 ⊕ Unit) := equalEverywhere (.var (.inr ()))
  have p0 : Certificate false (∅ : Context (Fin 0)) (base A) := by
    unfold base
    dsimp only [A]
    rw [equalEverywhere_subst]
    exact zeroEverywhere
  let Γ : Context (Fin 0 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let u : LA.Term (Fin 0 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Γ (equalEverywhere u) := by
    have q : Certificate false Γ (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) :=
      TheoryCertificate.assumption (Finset.mem_insert_self _ _)
    simpa [A, u, equalEverywhere_rename, Term.relabel] using q
  have sp := successorEverywhere.substitute (fun _ : Fin 1 => u)
  have sp' : Certificate false Γ (.impl (equalEverywhere u) (equalEverywhere (succTerm u))) := by
    have q : Certificate false (∅ : Context (Fin 0 ⊕ Fin 1))
        (.impl (equalEverywhere u) (equalEverywhere (succTerm u))) := by
      simpa [subst_impl, equalEverywhere_subst, succ_subst, Term.subst, Finset.image_empty] using sp
    exact q.weaken (Finset.empty_subset _)
  have ps : Certificate false Γ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, u, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      equalEverywhere_subst, succ_subst, Term.subst] using TheoryCertificate.impElim sp' ih
  have p := inductionRule A ∅ p0 (by simpa only [Γ, Finset.image_empty] using ps)
  have q := p.rename (Fin.elim0 : Fin 0 → Empty)
  let D : Formula (Fin 2) := equalityAlternative (.var 0) (.var 1)
  change Certificate false (∅ : Context Empty) (close D)
  simpa [A, D, equalEverywhere, equalityAlternative, close, allSlots, allUnit, bindUnit,
    liftScope, scopeInclusion, lastCases_one, lastCases_two_zero, lastCases_two_one,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
    term_subst_relabel, term_subst_vars, Term.relabel_relabel,
    zero_relabel, succ_relabel, Term.subst, Term.relabel, Finset.image_empty] using q

/-- Instantiate that supplied universal theorem at these actual terms. -/
def equalityTermDecision (s t : LA.Term α) :
    Certificate false (∅ : Context α) (.disj (termEqual s t) (.neg (termEqual s t))) := by
  let D : Formula (Fin 2) := .disj (termEqual (.var 0) (.var 1)) (.neg (termEqual (.var 0) (.var 1)))
  have hd : close D = equalityDecision := rfl
  have q := equalityDecisionProof.universeRename (Empty.elim : Empty → α)
  have q' : Certificate false (∅ : Context α) ((close D).rename Empty.elim) := by
    rw [hd]
    simpa only [Finset.image_empty] using q
  have p := TheoryCertificate.closeElim D ![s,t] q'
  simpa [D, subst_disj, subst_neg, termEqual_subst_poly, Term.subst] using p

def atomicDoubleNegation (s t : LA.Term α) :
    Certificate false (∅ : Context α) (.impl (.neg (.neg (termEqual s t))) (termEqual s t)) := by
  apply TheoryCertificate.impIntro
  apply TheoryCertificate.disjElim ((equalityTermDecision s t).weaken (Finset.empty_subset _))
  · exact TheoryCertificate.assumption (Finset.mem_insert_self _ _)
  · exact TheoryCertificate.falsumElim (TheoryCertificate.negElim
      (TheoryCertificate.assumption (Finset.mem_insert_self _ _))
      (TheoryCertificate.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))

private theorem term_remove_empty (s : LA.Term (α ⊕ Fin 0)) :
    (s.relabel (Sum.elim id Fin.elim0)).relabel (Sum.inl : α → α ⊕ Fin 0) = s := by
  rw [Term.relabel_relabel]
  have hf : ((Sum.inl : α → α ⊕ Fin 0) ∘ Sum.elim id Fin.elim0) = id := by
    funext x
    cases x with
    | inl a => rfl
    | inr i => exact i.elim0
  rw [hf, Term.relabel_id]

/-- Native formula recursion constructs an internal decision, not a truth test. -/
def quantifierFreeDecision (A : Formula α) (hA : A.QuantifierFree) :
    Certificate false (∅ : Context α) (.disj A (.neg A)) := by
  cases h : A with
  | falsum =>
    exact TheoryCertificate.disjRight (TheoryCertificate.negIntro
      (TheoryCertificate.assumption (Finset.mem_insert_self _ _)))
  | equal s t =>
    simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual, term_remove_empty] using
      equalityTermDecision (s.relabel (Sum.elim id Fin.elim0)) (t.relabel (Sum.elim id Fin.elim0))
  | rel R ts => exact R.elim
  | neg B =>
    rw [h] at hA
    apply TheoryCertificate.disjElim (quantifierFreeDecision B hA)
    · apply TheoryCertificate.disjRight
      apply TheoryCertificate.negIntro
      exact TheoryCertificate.negElim
        (TheoryCertificate.assumption (A := B) (by simp))
        (TheoryCertificate.assumption (A := .neg B) (by simp))
    · exact TheoryCertificate.disjLeft (TheoryCertificate.assumption (by simp))
  | conj B C =>
    rw [h] at hA
    have pB := quantifierFreeDecision B hA.1
    have pC := quantifierFreeDecision C hA.2
    apply TheoryCertificate.disjElim pB
    · apply TheoryCertificate.disjElim (pC.weaken (Finset.empty_subset _))
      · exact TheoryCertificate.disjLeft (TheoryCertificate.conjIntro
          (TheoryCertificate.assumption (by simp)) (TheoryCertificate.assumption (by simp)))
      · apply TheoryCertificate.disjRight
        apply TheoryCertificate.negIntro
        exact TheoryCertificate.negElim
          (TheoryCertificate.conjRight (TheoryCertificate.assumption (A := .conj B C) (by simp)))
          (TheoryCertificate.assumption (by simp))
    · apply TheoryCertificate.disjRight
      apply TheoryCertificate.negIntro
      exact TheoryCertificate.negElim
        (TheoryCertificate.conjLeft (TheoryCertificate.assumption (A := .conj B C) (by simp)))
        (TheoryCertificate.assumption (by simp))
  | disj B C =>
    rw [h] at hA
    have pB := quantifierFreeDecision B hA.1
    have pC := quantifierFreeDecision C hA.2
    apply TheoryCertificate.disjElim pB
    · exact TheoryCertificate.disjLeft (TheoryCertificate.disjLeft (TheoryCertificate.assumption (by simp)))
    · apply TheoryCertificate.disjElim (pC.weaken (Finset.empty_subset _))
      · exact TheoryCertificate.disjLeft (TheoryCertificate.disjRight (TheoryCertificate.assumption (by simp)))
      · apply TheoryCertificate.disjRight
        apply TheoryCertificate.negIntro
        apply TheoryCertificate.disjElim (TheoryCertificate.assumption (A := .disj B C) (by simp))
        · exact TheoryCertificate.negElim
            (TheoryCertificate.assumption (A := B) (by simp))
            (TheoryCertificate.assumption (A := .neg B) (by simp))
        · exact TheoryCertificate.negElim
            (TheoryCertificate.assumption (A := C) (by simp))
            (TheoryCertificate.assumption (A := .neg C) (by simp))
  | impl B C =>
    rw [h] at hA
    have pB := quantifierFreeDecision B hA.1
    have pC := quantifierFreeDecision C hA.2
    apply TheoryCertificate.disjElim pB
    · apply TheoryCertificate.disjElim (pC.weaken (Finset.empty_subset _))
      · exact TheoryCertificate.disjLeft (TheoryCertificate.impIntro (TheoryCertificate.assumption (A := C) (by simp)))
      · apply TheoryCertificate.disjRight
        apply TheoryCertificate.negIntro
        exact TheoryCertificate.negElim
          (TheoryCertificate.impElim
            (TheoryCertificate.assumption (A := .impl B C) (by simp))
            (TheoryCertificate.assumption (A := B) (by simp)))
          (TheoryCertificate.assumption (A := .neg C) (by simp))
    · apply TheoryCertificate.disjLeft
      apply TheoryCertificate.impIntro
      exact TheoryCertificate.falsumElim (TheoryCertificate.negElim
        (TheoryCertificate.assumption (A := B) (by simp))
        (TheoryCertificate.assumption (A := .neg B) (by simp)))
  | all B => rw [h] at hA; exact hA.elim
  | ex B => rw [h] at hA; exact hA.elim
termination_by A.depth
decreasing_by
  all_goals simp_all only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth]
  all_goals first
    | exact Nat.lt_succ_self _
    | exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    | exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

end
end Lemmatheca.ProofTheory.HeytingArithmetic
