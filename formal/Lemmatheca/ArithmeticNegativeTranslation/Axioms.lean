import Lemmatheca.ArithmeticNegativeTranslation.Scope
import Lemmatheca.HeytingArithmetic.Equality

namespace Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative context)
universe u v
variable {α : Type u}
noncomputable section
local instance arithmeticNegativeAxiomsFormulaEq {β : Type*} : DecidableEq (Formula β) := Classical.decEq _

open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder (liftScope scopeInclusion)

private def splitLast {δ : Type u} {n} : δ ⊕ Fin (n+1) → (δ ⊕ Fin n) ⊕ Fin 1 :=
  Sum.elim (fun a => .inl (.inl a))
    (Fin.lastCases (.inr 0) (fun i => .inl (.inr i)))

private theorem openedLast {δ : Type u} {n} (A : BF δ (n+1)) :
    A.toFormula.rename splitLast =
      (A.map (liftScope (fun x : δ ⊕ Fin n => .var (.inl x)))).toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp, map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [splitLast, liftScope, scopeInclusion, freeScope, Term.subst, Term.relabel]

/-- Close actual independently tagged arbitrary parameters, newest slot first. -/
private def allSlotsIntro {δ : Type u} {n} (A : BF δ n)
    (p : Certificate false (∅ : Context (δ ⊕ Fin n)) A.toFormula) :
    Certificate false (∅ : Context δ) (allSlots A) := by
  induction n with
  | zero =>
    have q := p.rename (Sum.elim id Fin.elim0 : δ ⊕ Fin 0 → δ)
    have he : A.toFormula.rename (Sum.elim id Fin.elim0) = A := by
      unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
      rw [map_comp]
      have hf : (fun x : δ ⊕ Fin 0 =>
          (Term.var (.inl x) : LA.Term ((δ ⊕ Fin 0) ⊕ Fin 0)).subst
            (freeScope (fun a => .var (Sum.elim id Fin.elim0 a)) 0)) = Term.var := by
        funext x
        cases x with
        | inl a => rfl
        | inr i => exact i.elim0
      rw [hf, map_id]
    simpa only [allSlots, Finset.image_empty, he] using q
  | succ n ih =>
    let B : BF (δ ⊕ Fin n) 1 :=
      A.map (liftScope (fun x : δ ⊕ Fin n => .var (.inl x)))
    have q : Certificate false (∅ : Context ((δ ⊕ Fin n) ⊕ Fin 1)) B.toFormula := by
      simpa only [Finset.image_empty, openedLast, B] using p.rename splitLast
    have r : Certificate false (∅ : Context (δ ⊕ Fin n)) (.all B) :=
      TheoryCertificate.allIntro (by simpa only [Finset.image_empty] using q)
    exact ih (.all A) r

/-- Close the exact ordered finite list of original parameters. -/
private def closeIntro {k} (A : Formula (Fin k))
    (p : Certificate false (∅ : Context (Fin k)) A) :
    Certificate false (∅ : Context Empty) (close A) := by
  let B : BF Empty k := A.map (Sum.elim (fun i => .var (.inr i)) Fin.elim0)
  have he : A.rename (Sum.inr : Fin k → Empty ⊕ Fin k) = B.toFormula := by
    unfold B Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    rw [map_comp]
    congr 1
    funext x
    cases x with
    | inl i => rfl
    | inr i => exact i.elim0
  have q : Certificate false (∅ : Context (Empty ⊕ Fin k)) B.toFormula := by
    simpa only [Finset.image_empty, he] using
      p.rename (Sum.inr : Fin k → Empty ⊕ Fin k)
  exact allSlotsIntro B q

private def basicBody {k} (D : Formula (Fin k)) (hD : close D ∈ basic) :
    Certificate false (∅ : Context (Fin k)) D := by
  simpa only [subst_id] using
    TheoryCertificate.basicInstance (T := theory) (Γ := (∅ : Context (Fin k)))
      (fun _ h => Or.inl h) D hD Term.var

private def doubleNegate {δ : Type*} {Γ : Context δ} {D : Formula δ}
    (p : Certificate false Γ D) : Certificate false Γ (.neg (.neg D)) :=
  TheoryCertificate.negIntro (TheoryCertificate.negElim
    (p.weaken (Finset.subset_insert _ _)) (TheoryCertificate.assumption (by simp)))

private def doubleNegatedBasic {k} (D : Formula (Fin k)) (hD : close D ∈ basic)
    (hN : negative D = .neg (.neg D)) :
    Certificate false (∅ : Context Empty) (negative (close D)) := by
  rw [negative_close, hN]
  exact closeIntro (.neg (.neg D)) (doubleNegate (basicBody D hD))

private def implicationDoubleNegate {δ : Type*} {Γ : Context δ} {A B : Formula δ}
    (p : Certificate false Γ (.impl A B)) :
    Certificate false Γ (.impl (.neg (.neg A)) (.neg (.neg B))) := by
  apply TheoryCertificate.impIntro
  apply TheoryCertificate.negIntro
  have na : Certificate false (insert (.neg B) (insert (.neg (.neg A)) Γ)) (.neg A) := by
    apply TheoryCertificate.negIntro
    exact TheoryCertificate.negElim
      (TheoryCertificate.impElim (p.weaken (by intro D hD; simp [hD]))
        (TheoryCertificate.assumption (by simp)))
      (TheoryCertificate.assumption (by simp))
  exact TheoryCertificate.negElim na (TheoryCertificate.assumption (by simp))

open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction (Derivation)
universe w

private def arngPredDN {δ : Type w} {Ξ : Context δ} {E : Formula δ}
    (p : Derivation false true LA Ξ E) : Derivation false true LA Ξ (.neg (.neg E)) :=
  .negIntro (.negElim (p.weaken (Finset.subset_insert _ _))
    (.assumption (Finset.mem_insert_self _ _)))

private theorem arngPred_openInstance {δ : Type w} (B : BF δ 1) :
    (B.rename (Sum.inl : δ → δ ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl

/-- Introduce existence using exactly the protected fresh variable. -/
private def arngPredCloseEx {δ : Type w} {Ξ : Context (δ ⊕ Fin 1)} (B : BF δ 1)
    (p : Derivation false true LA Ξ B.toFormula) :
    Derivation false true LA Ξ ((.ex B : Formula δ).rename Sum.inl) := by
  have q : Derivation false true LA Ξ
      ((B.rename (Sum.inl : δ → δ ⊕ Fin 1)).instantiate (.var (.inr 0))) :=
    (arngPred_openInstance B).symm ▸ p
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_ex] using
    (Derivation.exIntro (B := B.rename (Sum.inl : δ → δ ⊕ Fin 1)) (.var (.inr 0)) q)

/-- Construct the triple-negated-antecedent and doubly-negated-body consequence. -/
private def arngRawPredecessor {δ : Type w} {Ξ : Context δ} {E : Formula δ} {B : BF δ 1}
    (p : Derivation false true LA Ξ (.impl (.neg E) (.ex B))) :
    Derivation false true LA Ξ
      (.impl (.neg (.neg (.neg E))) (.neg (.neg (.ex (.neg (.neg B)))))) := by
  apply Derivation.impIntro
  let Γ : Context δ := insert (.neg (.neg (.neg E))) Ξ
  change Derivation false true LA Γ (.neg (.neg (.ex (.neg (.neg B)))))
  have ne : Derivation false true LA Γ (.neg E) := by
    apply Derivation.negIntro
    have he : Derivation false true LA (insert E Γ) E :=
      .assumption (Finset.mem_insert_self _ _)
    have hn : Derivation false true LA (insert E Γ) (.neg (.neg (.neg E))) :=
      .assumption (by simp [Γ])
    exact .negElim (arngPredDN he) hn
  have hex : Derivation false true LA Γ (.ex B) :=
    .impElim (p.weaken (Finset.subset_insert _ _)) ne
  apply Derivation.exElim hex
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_neg,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula] using
    arngPredDN (arngPredCloseEx (.neg (.neg B))
      (arngPredDN (.assumption (Finset.mem_insert_self _ _))))


def translatedSuccNonzero :
    Certificate false (∅ : Context Empty) (negative qSuccNeZero) := by
  let D : Formula (Fin 1) := .neg (termEqual (succTerm (.var 0)) zeroTerm)
  exact doubleNegatedBasic D (by change qSuccNeZero ∈ basic; simp [basic]) rfl

def translatedSuccInjective :
    Certificate false (∅ : Context Empty) (negative qSuccInjective) := by
  let D : Formula (Fin 2) := .impl
    (termEqual (succTerm (.var 0)) (succTerm (.var 1))) (termEqual (.var 0) (.var 1))
  change Certificate false (∅ : Context Empty) (negative (close D))
  rw [negative_close]
  exact closeIntro (negative D)
    (implicationDoubleNegate (basicBody D (by change qSuccInjective ∈ basic; simp [basic])))

def translatedPredecessor :
    Certificate false (∅ : Context Empty) (negative qPredecessor) := by
  let D : Formula (Fin 1) := .impl (.neg (termEqual (.var 0) zeroTerm))
    (exUnit (termEqual (.var (.inl (0 : Fin 1))) (succTerm (.var (.inr ())))))
  change Certificate false (∅ : Context Empty) (negative (close D))
  rw [negative_close]
  let p := TheoryCertificate.toRaw
    (basicBody D (by change qPredecessor ∈ basic; simp [basic]))
  exact closeIntro (negative D) (TheoryCertificate.ofRaw
    ⟨p.support, p.allowed, arngRawPredecessor p.derivation⟩)

def translatedAddZero :
    Certificate false (∅ : Context Empty) (negative qAddZero) := by
  let D : Formula (Fin 1) := termEqual (addTerm (.var 0) zeroTerm) (.var 0)
  exact doubleNegatedBasic D (by change qAddZero ∈ basic; simp [basic]) rfl

def translatedAddSucc :
    Certificate false (∅ : Context Empty) (negative qAddSucc) := by
  let D : Formula (Fin 2) := termEqual (addTerm (.var 0) (succTerm (.var 1)))
    (succTerm (addTerm (.var 0) (.var 1)))
  exact doubleNegatedBasic D (by change qAddSucc ∈ basic; simp [basic]) rfl

def translatedMulZero :
    Certificate false (∅ : Context Empty) (negative qMulZero) := by
  let D : Formula (Fin 1) := termEqual (mulTerm (.var 0) zeroTerm) zeroTerm
  exact doubleNegatedBasic D (by change qMulZero ∈ basic; simp [basic]) rfl

def translatedMulSucc :
    Certificate false (∅ : Context Empty) (negative qMulSucc) := by
  let D : Formula (Fin 2) := termEqual (mulTerm (.var 0) (succTerm (.var 1)))
    (addTerm (mulTerm (.var 0) (.var 1)) (.var 0))
  exact doubleNegatedBasic D (by change qMulSucc ∈ basic; simp [basic]) rfl

/-- A particular actual arithmetic axiom yields an actual translated certificate. -/
def translatedAxiom (θ : Sentence) (hθ : θ ∈ theory) :
    Certificate false (∅ : Context Empty) (negative θ) := by
  by_cases h : θ = qSuccNeZero
  · exact h.symm ▸ translatedSuccNonzero
  by_cases h : θ = qSuccInjective
  · exact h.symm ▸ translatedSuccInjective
  by_cases h : θ = qPredecessor
  · exact h.symm ▸ translatedPredecessor
  by_cases h : θ = qAddZero
  · exact h.symm ▸ translatedAddZero
  by_cases h : θ = qAddSucc
  · exact h.symm ▸ translatedAddSucc
  by_cases h : θ = qMulZero
  · exact h.symm ▸ translatedMulZero
  by_cases h : θ = qMulSucc
  · exact h.symm ▸ translatedMulSucc
  have hi : θ ∈ inductionTheory := by
    rcases hθ with hb | hi
    · simp_all [basic]
    · exact hi
  let k := Classical.choose hi
  let A := Classical.choose (Classical.choose_spec hi)
  have he : θ = inductionAxiom A := Classical.choose_spec (Classical.choose_spec hi)
  rw [he, negative_inductionAxiom]
  have p := TheoryCertificate.fromAxiom (c := false) (Γ := (∅ : Context Empty))
    (inductionAxiom (negative A)) (show inductionAxiom (negative A) ∈ theory from
      Or.inr ⟨k, negative A, rfl⟩)
  have hid : (Empty.elim : Empty → Empty) = id := by funext x; exact x.elim
  simpa only [hid, rename_id] using p

/-- Closed copies have the exact original free-name type in the target certificate. -/
def translatedAxiomOverNames (θ : Sentence) (hθ : θ ∈ theory) (X : Type u) :
    Certificate false (∅ : Context X)
      (negative (θ.rename (Empty.elim : Empty → X))) := by
  simpa only [Finset.image_empty,
    Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.negative_rename] using
      (translatedAxiom θ hθ).universeRename (Empty.elim : Empty → X)

end
end Lemmatheca.ProofTheory.HeytingArithmetic.NegativeTranslation
