import Lemmatheca.HeytingArithmeticOrder.Syntax

/-! Every target returns an actual original-HA finite certificate. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.Order
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
universe u
variable {α : Type u}
noncomputable section
local instance haoCertificateEq {δ : Type*} : DecidableEq (Formula δ) := Classical.decEq _
variable {Γ : Context α}

private theorem basicIn : basic ⊆ theory := fun _ h => Or.inl h
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open TheoryCertificate
attribute [local simp] leFormula_subst ltFormula_subst leFormula_rename ltFormula_rename

private def exEliminate {D : BF α 1} {A : Formula α}
    (p : Certificate false Γ (.ex D))
    (q : Certificate false (insert D.toFormula
      (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ Fin 1))))
      (A.rename Sum.inl)) : Certificate false Γ A := by
  let σ : α ⊕ Fin 1 → LA.Term α := Sum.elim Term.var (fun _ => zeroTerm)
  have fix (E : Formula α) : (E.rename (Sum.inl : α → α ⊕ Fin 1)).subst σ = E := by
    rw [formula_rename_subst]
    exact E.subst_id
  have pull {E : Formula (α ⊕ Fin 1)} (hE : E ∈ q.assumptions.erase D.toFormula) :
      E.subst σ ∈ assumptions theory Γ ∧ (E.subst σ).rename Sum.inl = E := by
    obtain ⟨hne, hE⟩ := Finset.mem_erase.mp hE
    rcases q.allowed E hE with hT | hΓ
    · obtain ⟨θ, hθ, rfl⟩ := hT
      rw [closed_subst θ σ]
      exact ⟨Or.inl ⟨θ, hθ, rfl⟩, closed_rename θ Sum.inl⟩
    · have hΓ := (Finset.mem_insert.mp hΓ).resolve_left hne
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hΓ
      rw [fix]
      exact ⟨Or.inr hF, rfl⟩
  let Ξ := p.assumptions ∪ (q.assumptions.erase D.toFormula).image (fun E => E.subst σ)
  refine ⟨Ξ, ?_, Proof.exElim (p.derivation.weaken Finset.subset_union_left)
    (q.derivation.weaken ?_)⟩
  · intro E hE
    rcases Finset.mem_union.mp hE with hp | hq
    · exact p.allowed E hp
    · obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hq
      exact (pull hF).1
  · intro E hE
    by_cases he : E = D.toFormula
    · exact Finset.mem_insert.mpr (Or.inl he)
    · have hmem : E ∈ q.assumptions.erase D.toFormula := Finset.mem_erase.mpr ⟨he, hE⟩
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
        ⟨E.subst σ, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨E, hmem, rfl⟩), (pull hmem).2⟩))

/-- Transport a supplied certificate along a proved equality through the specified native Unit-body. -/
def replaceUnit (B : Formula (α ⊕ Unit)) (s t : LA.Term α)
    (e : Certificate false Γ (termEqual s t))
    (p : Certificate false Γ (B.subst (Sum.elim Term.var (fun _ => s)))) :
    Certificate false Γ (B.subst (Sum.elim Term.var (fun _ => t))) := by
  have q : Certificate false Γ ((bindUnit B).instantiate s) := by
    simpa only [bindUnit_instance] using p
  simpa only [bindUnit_instance] using
    TheoryCertificate.combine e q (fun _ => Proof.equalElim (bindUnit B) s t)

private theorem leBody_instance (s t d : LA.Term α) :
    (leBody s t).subst (Sum.elim Term.var (fun _ => d)) = termEqual (addTerm d s) t := by
  simp [leBody, termEqual_subst_poly, term_subst_relabel, Term.subst]

private theorem leBody_open (s t : LA.Term α) :
    (leBody s t).rename (Sum.map id (fun _ => (0 : Fin 1))) =
      termEqual (addTerm (.var (.inr 0)) (s.relabel Sum.inl)) (t.relabel Sum.inl) := by
  simp [leBody, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, termEqual_subst_poly,
    term_subst_vars, Term.relabel_relabel, Function.comp_def]

private def zeroOrSucc (t : LA.Term α) : Certificate false Γ
    (.disj (termEqual t zeroTerm) (exUnit (termEqual (t.relabel Sum.inl) (succTerm (.var (.inr ())))))) := by
  let D : Formula (Fin 1) := .disj (termEqual (.var 0) zeroTerm)
    (exUnit (termEqual (.var (.inl 0)) (succTerm (.var (.inr ())))))
  have p : Certificate false (∅ : Context Empty) (close D) :=
    zeroOrSuccessorProof.mono (fun _ h => Or.inr h)
  simpa [D, subst_disj, termEqual_subst_poly, exUnit_subst, unitSubst,
    term_subst_relabel, Term.subst] using Addition.instantiateClosed D p ![t] Γ


/-- Introduce precisely the supplied additive witness and its instance proof. -/
def leIntro (s t d : LA.Term α) (p : Certificate false Γ (termEqual (addTerm d s) t)) :
    Certificate false Γ (leFormula s t) := by
  exact exUnitIntro (leBody s t) d (by simpa only [leBody_instance] using p)

/-- Eliminate the supplied order premise in a genuinely protected witness branch. -/
def leElim (s t : LA.Term α) {A : Formula α}
    (p : Certificate false Γ (leFormula s t))
    (q : Certificate false
      (insert ((leBody s t).rename (Sum.map id (fun _ => (0 : Fin 1))))
        (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ Fin 1))))
      (A.rename Sum.inl)) : Certificate false Γ A := by
  exact exEliminate p (by simpa only [bindUnit_open] using q)

/-- Eliminate a supplied native existential certificate with a protected witness branch and pull back its finite support. -/
def exUnitEliminate (B : Formula (α ⊕ Unit)) {A : Formula α}
    (p : Certificate false Γ (exUnit B))
    (q : Certificate false
      (insert (B.rename (Sum.map id (fun _ => (0 : Fin 1))))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (A.rename Sum.inl)) : Certificate false Γ A :=
  exEliminate p (by simpa only [bindUnit_open] using q)

/-- Eliminate the internal zero-or-successor alternatives with a protected predecessor branch. -/
def zeroSuccElim (t : LA.Term α) {A : Formula α}
    (q0 : Certificate false (insert (termEqual t zeroTerm) Γ) A)
    (qs : Certificate false
      (insert (termEqual (t.relabel Sum.inl) (succTerm (.var (.inr (0 : Fin 1)))))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (A.rename Sum.inl)) : Certificate false Γ A := by
  apply TheoryCertificate.disjElim (zeroOrSucc t) q0
  apply exUnitEliminate _ (TheoryCertificate.assumption (Finset.mem_insert_self _ _))
  have h : (termEqual (t.relabel Sum.inl) (succTerm (.var (.inr ()) : LA.Term (α ⊕ Unit)))).rename
      (Sum.map id (fun _ => (0 : Fin 1))) =
      termEqual (t.relabel Sum.inl) (succTerm (.var (.inr 0))) := by
    simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, termEqual_subst_poly,
      term_subst_vars, Term.relabel_relabel, Function.comp_def]
  rw [h]
  exact qs.weaken (by intro E hE; simp only [Finset.mem_insert, Finset.image_insert] at *; aesop)

/-- Open the exact additive witness equation of a supplied non-strict order certificate. -/
def leElimEq (s t : LA.Term α) {A : Formula α}
    (p : Certificate false Γ (leFormula s t))
    (q : Certificate false
      (insert (termEqual (addTerm (.var (.inr (0 : Fin 1))) (s.relabel Sum.inl)) (t.relabel Sum.inl))
        (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ Fin 1))))
      (A.rename Sum.inl)) : Certificate false Γ A :=
  leElim s t p (by simpa only [leBody_open] using q)

/-- Transport an order certificate along supplied endpoint equality certificates. -/
def leCongr {s s' t t' : LA.Term α}
    (es : Certificate false Γ (termEqual s s')) (et : Certificate false Γ (termEqual t t'))
    (p : Certificate false Γ (leFormula s t)) : Certificate false Γ (leFormula s' t') := by
  have p1 := replaceUnit (leFormula (.var (.inr ())) (t.relabel Sum.inl)) s s' es
    (by simpa [term_subst_relabel, Term.subst] using p)
  have p1' : Certificate false Γ (leFormula s' t) := by
    simpa [term_subst_relabel, Term.subst] using p1
  have p2 := replaceUnit (leFormula (s'.relabel Sum.inl) (.var (.inr ()))) t t' et
    (by simpa [term_subst_relabel, Term.subst] using p1')
  simpa [term_subst_relabel, Term.subst] using p2



@[simp] private theorem eqRename (s t : LA.Term α) {β : Type u} (f : α → β) :
    (termEqual s t).rename f = termEqual (s.relabel f) (t.relabel f) := by
  simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, termEqual_subst_poly, term_subst_vars]
@[simp] private theorem conjRename (A B : Formula α) {β : Type u} (f : α → β) :
    (.conj A B : Formula α).rename f = .conj (A.rename f) (B.rename f) := rfl
@[simp] private theorem disjRename (A B : Formula α) {β : Type u} (f : α → β) :
    (.disj A B : Formula α).rename f = .disj (A.rename f) (B.rename f) := rfl
@[simp] private theorem negRename (A : Formula α) {β : Type u} (f : α → β) :
    (.neg A : Formula α).rename f = .neg (A.rename f) := rfl
@[simp] private theorem falseRename {β : Type u} (f : α → β) :
    (.falsum : Formula α).rename f = .falsum := rfl

private def liftInto {A : Formula α} (p : Certificate false Γ A)
    (B : Formula (α ⊕ Fin 1)) : Certificate false
    (insert B (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
    (A.rename Sum.inl) := (p.universeRename Sum.inl).weaken (Finset.subset_insert _ _)

private def sumZeroRight (s t : LA.Term α) (p : Certificate false Γ (termEqual (addTerm s t) zeroTerm)) :
    Certificate false Γ (termEqual t zeroTerm) := by
  apply zeroSuccElim s
  · have es : Certificate false (insert (termEqual s zeroTerm) Γ) (termEqual s zeroTerm) := assumption (by simp)
    exact equalTransitivity (equalSymmetry (Addition.zeroLeft t))
      (equalTransitivity (equalSymmetry (addEquality es (equalIntro t)))
        (p.weaken (Finset.subset_insert _ _)))
  · simp only [eqRename, zero_relabel]
    let x := s.relabel (Sum.inl : α → α ⊕ Fin 1)
    let y := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let d : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let Δ : Context (α ⊕ Fin 1) := insert (termEqual x (succTerm d)) (Γ.image (fun E => E.rename Sum.inl))
    have es : Certificate false Δ (termEqual x (succTerm d)) := assumption (by simp [Δ,x,d])
    have ep : Certificate false Δ (termEqual (addTerm x y) zeroTerm) := by
      simpa only [eqRename, add_relabel, zero_relabel] using liftInto p (termEqual x (succTerm d))
    exact falsumElim (negElim
      (equalTransitivity (equalSymmetry (Addition.successorLeft d y))
        (equalTransitivity (equalSymmetry (addEquality es (equalIntro y))) ep))
      (succNonzero basicIn (addTerm d y)))

def zeroSum (s t : LA.Term α) : Certificate false Γ
    (iffFormula (termEqual (addTerm s t) zeroTerm)
      (.conj (termEqual s zeroTerm) (termEqual t zeroTerm))) := by
  apply conjIntro
  · apply impIntro
    have p : Certificate false (insert (termEqual (addTerm s t) zeroTerm) Γ)
        (termEqual (addTerm s t) zeroTerm) := assumption (by simp)
    exact conjIntro (sumZeroRight t s (equalTransitivity (Addition.commutative t s) p))
      (sumZeroRight s t p)
  · apply impIntro
    have p : Certificate false (insert (.conj (termEqual s zeroTerm) (termEqual t zeroTerm)) Γ)
        (.conj (termEqual s zeroTerm) (termEqual t zeroTerm)) := assumption (by simp)
    exact equalTransitivity (addEquality (conjLeft p) (conjRight p)) (addZero basicIn zeroTerm)

def zeroLe (t : LA.Term α) : Certificate false Γ (leFormula zeroTerm t) := by
  exact leIntro zeroTerm t t (addZero basicIn t)

def leZero (t : LA.Term α) :
    Certificate false Γ (iffFormula (leFormula t zeroTerm) (termEqual t zeroTerm)) := by
  apply conjIntro
  · apply impIntro
    apply leElimEq t zeroTerm (assumption (by simp))
    simp only [eqRename, zero_relabel]
    exact sumZeroRight (.var (.inr 0)) (t.relabel Sum.inl) (assumption (by simp))
  · apply impIntro
    have e : Certificate false (insert (termEqual t zeroTerm) Γ) (termEqual t zeroTerm) := assumption (by simp)
    exact leIntro t zeroTerm zeroTerm (equalTransitivity (Addition.zeroLeft t) e)

def ltZero (t : LA.Term α) : Certificate false Γ (.neg (ltFormula t zeroTerm)) := by
  apply negIntro
  have p : Certificate false (insert (ltFormula t zeroTerm) Γ) (leFormula (succTerm t) zeroTerm) := assumption (by simp [ltFormula])
  exact negElim (impElim (conjLeft (leZero (succTerm t))) p) (succNonzero basicIn t)

/-- Successor cancellation transports exactly the same additive witness. -/

private def mapLeWitness (s t u v : LA.Term α) (p : Certificate false Γ (leFormula s t))
    (f : Certificate false
      (insert (termEqual (addTerm (.var (.inr (0 : Fin 1))) (s.relabel Sum.inl)) (t.relabel Sum.inl))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (termEqual (addTerm (.var (.inr 0)) (s.relabel Sum.inl)) (t.relabel Sum.inl)) →
      Certificate false
      (insert (termEqual (addTerm (.var (.inr (0 : Fin 1))) (s.relabel Sum.inl)) (t.relabel Sum.inl))
        (Γ.image (fun E => E.rename (Sum.inl : α → α ⊕ Fin 1))))
      (termEqual (addTerm (.var (.inr 0)) (u.relabel Sum.inl)) (v.relabel Sum.inl))) :
    Certificate false Γ (leFormula u v) := by
  apply leElimEq s t p
  rw [leFormula_rename]
  exact leIntro _ _ (.var (.inr 0)) (f (assumption (by simp)))

def leSuccWitness (s t d : LA.Term α) : Certificate false Γ
    (iffFormula (termEqual (addTerm d (succTerm s)) (succTerm t))
      (termEqual (addTerm d s) t)) := by
  apply conjIntro
  · apply impIntro
    exact impElim (succInjective basicIn (addTerm d s) t)
      (equalTransitivity (equalSymmetry (addSucc basicIn d s)) (assumption (by simp)))
  · apply impIntro
    exact equalTransitivity (addSucc basicIn d s) (succEquality (assumption (by simp)))

def leSucc (s t : LA.Term α) : Certificate false Γ
    (iffFormula (leFormula (succTerm s) (succTerm t)) (leFormula s t)) := by
  apply conjIntro
  · apply impIntro
    exact mapLeWitness (succTerm s) (succTerm t) s t (assumption (by simp))
      (fun p => impElim (conjLeft (leSuccWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (.var (.inr 0)))) p)
  · apply impIntro
    exact mapLeWitness s t (succTerm s) (succTerm t) (assumption (by simp))
      (fun p => impElim (conjRight (leSuccWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (.var (.inr 0)))) p)

def ltSucc (s t : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula (succTerm s) (succTerm t)) (ltFormula s t)) := by
  exact leSucc (succTerm s) t

def ltSuccIffLe (s t : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula s (succTerm t)) (leFormula s t)) := by
  exact leSucc s t


private def splitGivenWitness (s t d : LA.Term α)
    (e : Certificate false Γ (termEqual (addTerm d s) t)) :
    Certificate false Γ (.disj (ltFormula s t) (termEqual s t)) := by
  apply zeroSuccElim d
  · apply disjRight
    have ed : Certificate false (insert (termEqual d zeroTerm) Γ) (termEqual d zeroTerm) := assumption (by simp)
    exact equalTransitivity (equalSymmetry (Addition.zeroLeft s))
      (equalTransitivity (equalSymmetry (addEquality ed (equalIntro s)))
        (e.weaken (Finset.subset_insert _ _)))
  · simp only [disjRename, ltFormula_rename, eqRename]
    let x := s.relabel (Sum.inl : α → α ⊕ Fin 1)
    let y := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let d' := d.relabel (Sum.inl : α → α ⊕ Fin 1)
    let a : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let Δ : Context (α ⊕ Fin 1) := insert (termEqual d' (succTerm a)) (Γ.image (fun E => E.rename Sum.inl))
    have ed : Certificate false Δ (termEqual d' (succTerm a)) := assumption (by simp [Δ])
    have ee : Certificate false Δ (termEqual (addTerm d' x) y) := by
      simpa only [eqRename, add_relabel] using liftInto e (termEqual d' (succTerm a))
    apply disjLeft
    exact leIntro (succTerm x) y a
      (equalTransitivity (addSucc basicIn a x)
        (equalTransitivity (equalSymmetry (Addition.successorLeft a x))
          (equalTransitivity (addEquality (equalSymmetry ed) (equalIntro x)) ee)))

def leSplit (s t : LA.Term α) : Certificate false Γ
    (iffFormula (leFormula s t) (.disj (ltFormula s t) (termEqual s t))) := by
  apply conjIntro
  · apply impIntro
    apply leElimEq s t (assumption (by simp))
    simp only [disjRename, ltFormula_rename, eqRename]
    exact splitGivenWitness _ _ (.var (.inr 0)) (assumption (by simp))
  · apply impIntro
    apply disjElim (assumption (A := .disj (ltFormula s t) (termEqual s t)) (by simp))
    · apply leElimEq (succTerm s) t (assumption (by simp [ltFormula]))
      rw [leFormula_rename]
      exact leIntro _ _ (succTerm (.var (.inr 0)))
        (equalTransitivity (Addition.successorLeft (.var (.inr 0)) (s.relabel Sum.inl))
          (equalTransitivity (equalSymmetry (addSucc basicIn (.var (.inr 0)) (s.relabel Sum.inl)))
            (assumption (by simp))))
    · exact leIntro s t zeroTerm (equalTransitivity (Addition.zeroLeft s) (assumption (by simp)))

def leRefl (t : LA.Term α) : Certificate false Γ (leFormula t t) := by
  exact leIntro t t zeroTerm (Addition.zeroLeft t)

def ltToLe (s t : LA.Term α) (p : Certificate false Γ (ltFormula s t)) :
    Certificate false Γ (leFormula s t) := by
  apply leElimEq (succTerm s) t p
  rw [leFormula_rename]
  exact leIntro _ _ (succTerm (.var (.inr 0)))
    (equalTransitivity (Addition.successorLeft (.var (.inr 0)) (s.relabel Sum.inl))
      (equalTransitivity (equalSymmetry (addSucc basicIn (.var (.inr 0)) (s.relabel Sum.inl)))
        (assumption (by simp))))

/-- The exact strict successor-bound split needed for bounded induction. -/
def ltSuccSplit (s t : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula s (succTerm t)) (.disj (ltFormula s t) (termEqual s t))) := by
  apply conjIntro
  · apply impIntro
    exact impElim (conjLeft (leSplit s t))
      (impElim (conjLeft (ltSuccIffLe s t)) (assumption (by simp)))
  · apply impIntro
    exact impElim (conjRight (ltSuccIffLe s t))
      (impElim (conjRight (leSplit s t)) (assumption (by simp)))

/-- The exact non-strict successor-bound split, retaining the endpoint. -/
def leSuccSplit (s t : LA.Term α) : Certificate false Γ
    (iffFormula (leFormula s (succTerm t)) (.disj (leFormula s t) (termEqual s (succTerm t)))) := by
  apply conjIntro
  · apply impIntro
    apply disjElim (impElim (conjLeft (leSplit s (succTerm t))) (assumption (by simp)))
    · exact disjLeft (impElim (conjLeft (ltSuccIffLe s t)) (assumption (by simp)))
    · exact disjRight (assumption (by simp))
  · apply impIntro
    apply disjElim (assumption (A := .disj (leFormula s t) (termEqual s (succTerm t))) (by simp))
    · exact impElim (conjRight (leSplit s (succTerm t)))
        (disjLeft (impElim (conjRight (ltSuccIffLe s t)) (assumption (by simp))))
    · exact leIntro s (succTerm t) zeroTerm
        (equalTransitivity (Addition.zeroLeft s) (assumption (by simp)))


private def leCompose (s t r : LA.Term α)
    (p : Certificate false Γ (leFormula s t)) (q : Certificate false Γ (leFormula t r)) :
    Certificate false Γ (leFormula s r) := by
  apply leElimEq t r q
  rw [leFormula_rename]
  let x := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let y := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let z := r.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  let Δ : Context (α ⊕ Fin 1) := insert (termEqual (addTerm b y) z) (Γ.image (fun E => E.rename Sum.inl))
  have ps : Certificate false Δ (leFormula x y) := by
    simpa only [leFormula_rename] using liftInto p (termEqual (addTerm b y) z)
  have eb : Certificate false Δ (termEqual (addTerm b y) z) := assumption (by simp [Δ])
  apply leElimEq x y ps
  rw [leFormula_rename]
  let x' := x.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let y' := y.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let z' := z.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let b' := b.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let a : LA.Term ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let Ξ : Context ((α ⊕ Fin 1) ⊕ Fin 1) := insert (termEqual (addTerm a x') y') (Δ.image (fun E => E.rename Sum.inl))
  have ea : Certificate false Ξ (termEqual (addTerm a x') y') := assumption (by simp [Ξ])
  have eb' : Certificate false Ξ (termEqual (addTerm b' y') z') := by
    simpa only [eqRename, add_relabel] using liftInto eb (termEqual (addTerm a x') y')
  exact leIntro x' z' (addTerm b' a)
    (equalTransitivity (Addition.associative b' a x')
      (equalTransitivity (addEquality (equalIntro b') ea) eb'))

def leTransitivity (s t r : LA.Term α) : Certificate false Γ
    (.impl (.conj (leFormula s t) (leFormula t r)) (leFormula s r)) := by
  apply impIntro
  have p : Certificate false (insert (.conj (leFormula s t) (leFormula t r)) Γ)
      (.conj (leFormula s t) (leFormula t r)) := assumption (by simp)
  exact leCompose s t r (conjLeft p) (conjRight p)

def ltLeTransitivity (s t r : LA.Term α) : Certificate false Γ
    (.impl (.conj (ltFormula s t) (leFormula t r)) (ltFormula s r)) := by
  apply impIntro
  have p : Certificate false (insert (.conj (ltFormula s t) (leFormula t r)) Γ)
      (.conj (ltFormula s t) (leFormula t r)) := assumption (by simp)
  exact leCompose (succTerm s) t r (conjLeft p) (conjRight p)

def leLtTransitivity (s t r : LA.Term α) : Certificate false Γ
    (.impl (.conj (leFormula s t) (ltFormula t r)) (ltFormula s r)) := by
  apply impIntro
  have p : Certificate false (insert (.conj (leFormula s t) (ltFormula t r)) Γ)
      (.conj (leFormula s t) (ltFormula t r)) := assumption (by simp)
  exact leCompose (succTerm s) (succTerm t) r
    (impElim (conjRight (leSucc s t)) (conjLeft p)) (conjRight p)

def ltTransitivity (s t r : LA.Term α) : Certificate false Γ
    (.impl (.conj (ltFormula s t) (ltFormula t r)) (ltFormula s r)) := by
  apply impIntro
  have p : Certificate false (insert (.conj (ltFormula s t) (ltFormula t r)) Γ)
      (.conj (ltFormula s t) (ltFormula t r)) := assumption (by simp)
  exact impElim (ltLeTransitivity s t r)
    (conjIntro (conjLeft p) (ltToLe t r (conjRight p)))

def ltIrrefl (t : LA.Term α) : Certificate false Γ (.neg (ltFormula t t)) := by
  apply negIntro
  apply leElimEq (succTerm t) t (assumption (by simp [ltFormula]))
  simp only [falseRename]
  let x := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let d : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  exact negElim
    (Addition.cancelRight x (succTerm d) zeroTerm
      (equalTransitivity (Addition.successorLeft d x)
        (equalTransitivity (equalSymmetry (addSucc basicIn d x))
          (equalTransitivity (assumption (by simp [x,d])) (equalSymmetry (Addition.zeroLeft x))))))
    (succNonzero basicIn d)


private def strictNe (s t : LA.Term α) (p : Certificate false Γ (ltFormula s t)) :
    Certificate false Γ (.neg (termEqual s t)) := by
  apply negIntro
  have e : Certificate false (insert (termEqual s t) Γ) (termEqual s t) := assumption (by simp)
  exact negElim
    (leCongr (equalIntro (succTerm s)) (equalSymmetry e) (p.weaken (Finset.subset_insert _ _)))
    (ltIrrefl s)

private def eqLe (s t : LA.Term α) (e : Certificate false Γ (termEqual s t)) :
    Certificate false Γ (leFormula s t) := leIntro s t zeroTerm (equalTransitivity (Addition.zeroLeft s) e)

private def strictReverseLeFalse (s t : LA.Term α)
    (p : Certificate false Γ (ltFormula s t)) (q : Certificate false Γ (leFormula t s)) :
    Certificate false Γ .falsum :=
  negElim (impElim (ltLeTransitivity s t s) (conjIntro p q)) (ltIrrefl s)

def ltIffLeNe (s t : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula s t) (.conj (leFormula s t) (.neg (termEqual s t)))) := by
  apply conjIntro
  · apply impIntro
    have p : Certificate false (insert (ltFormula s t) Γ) (ltFormula s t) := assumption (by simp)
    exact conjIntro (ltToLe s t p) (strictNe s t p)
  · apply impIntro
    have p : Certificate false (insert (.conj (leFormula s t) (.neg (termEqual s t))) Γ)
        (.conj (leFormula s t) (.neg (termEqual s t))) := assumption (by simp)
    apply disjElim (impElim (conjLeft (leSplit s t)) (conjLeft p))
    · exact assumption (by simp)
    · exact falsumElim (negElim (assumption (by simp))
        ((conjRight p).weaken (Finset.subset_insert _ _)))

private def antisymFromWitness (s t a : LA.Term α)
    (e : Certificate false Γ (termEqual (addTerm a s) t))
    (q : Certificate false Γ (leFormula t s)) : Certificate false Γ (termEqual s t) := by
  apply leElimEq t s q
  simp only [eqRename]
  let x := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let y := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let a' := a.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  let Δ : Context (α ⊕ Fin 1) := insert (termEqual (addTerm b y) x) (Γ.image (fun E => E.rename Sum.inl))
  have ea : Certificate false Δ (termEqual (addTerm a' x) y) := by
    simpa only [eqRename, add_relabel] using liftInto e (termEqual (addTerm b y) x)
  have eb : Certificate false Δ (termEqual (addTerm b y) x) := assumption (by simp [Δ])
  have eba : Certificate false Δ (termEqual (addTerm b a') zeroTerm) :=
    Addition.cancelRight x (addTerm b a') zeroTerm
      (equalTransitivity (Addition.associative b a' x)
        (equalTransitivity (addEquality (equalIntro b) ea)
          (equalTransitivity eb (equalSymmetry (Addition.zeroLeft x)))))
  have azero : Certificate false Δ (termEqual a' zeroTerm) := sumZeroRight b a' eba
  exact equalTransitivity (equalSymmetry (Addition.zeroLeft x))
    (equalTransitivity (equalSymmetry (addEquality azero (equalIntro x))) ea)

def leAntisymmetry (s t : LA.Term α) : Certificate false Γ
    (.impl (.conj (leFormula s t) (leFormula t s)) (termEqual s t)) := by
  apply impIntro
  have p : Certificate false (insert (.conj (leFormula s t) (leFormula t s)) Γ)
      (.conj (leFormula s t) (leFormula t s)) := assumption (by simp)
  apply leElimEq s t (conjLeft p)
  simp only [eqRename]
  let x := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let y := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let a : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
  let Δ : Context (α ⊕ Fin 1) := insert (termEqual (addTerm a x) y)
    ((insert (.conj (leFormula s t) (leFormula t s)) Γ).image (fun E => E.rename Sum.inl))
  have e : Certificate false Δ (termEqual (addTerm a x) y) := assumption (by simp [Δ])
  have q : Certificate false Δ (leFormula y x) := by
    simpa only [leFormula_rename] using liftInto (conjRight p) (termEqual (addTerm a x) y)
  exact antisymFromWitness x y a e q


@[simp] private theorem comparisonSubst (s t : LA.Term α) {β : Type u} (σ : α → LA.Term β) :
    (comparison s t).subst σ = comparison (s.subst σ) (t.subst σ) := by
  simp only [comparison, subst_disj, ltFormula_subst, termEqual_subst_poly]
@[simp] private theorem comparisonRename (s t : LA.Term α) {β : Type u} (f : α → β) :
    (comparison s t).rename f = comparison (s.relabel f) (t.relabel f) := by
  simp only [comparison, disjRename, ltFormula_rename, eqRename]

private def comparisonCongr {s s' t t' : LA.Term α}
    (es : Certificate false Γ (termEqual s s')) (et : Certificate false Γ (termEqual t t'))
    (p : Certificate false Γ (comparison s t)) : Certificate false Γ (comparison s' t') := by
  have p1 := replaceUnit (comparison (.var (.inr ())) (t.relabel Sum.inl)) s s' es
    (by simpa [term_subst_relabel, Term.subst] using p)
  have p1' : Certificate false Γ (comparison s' t) := by
    simpa [term_subst_relabel, Term.subst] using p1
  have p2 := replaceUnit (comparison (s'.relabel Sum.inl) (.var (.inr ()))) t t' et
    (by simpa [term_subst_relabel, Term.subst] using p1')
  simpa [term_subst_relabel, Term.subst] using p2

private def zeroLtSucc (t : LA.Term α) : Certificate false Γ (ltFormula zeroTerm (succTerm t)) :=
  impElim (conjRight (ltSuccIffLe zeroTerm t)) (zeroLe t)

private def compareZero (t : LA.Term α) : Certificate false Γ (comparison t zeroTerm) := by
  apply zeroSuccElim t
  · have e : Certificate false (insert (termEqual t zeroTerm) Γ) (termEqual t zeroTerm) := assumption (by simp)
    exact comparisonCongr (equalSymmetry e) (equalIntro zeroTerm)
      (disjRight (disjLeft (equalIntro zeroTerm)))
  · simp only [comparisonRename, zero_relabel]
    let x := t.relabel (Sum.inl : α → α ⊕ Fin 1)
    let d : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let Δ : Context (α ⊕ Fin 1) := insert (termEqual x (succTerm d)) (Γ.image (fun E => E.rename Sum.inl))
    have e : Certificate false Δ (termEqual x (succTerm d)) := assumption (by simp [Δ])
    exact comparisonCongr (equalSymmetry e) (equalIntro zeroTerm)
      (disjRight (disjRight (zeroLtSucc d)))

private def compareSuccessors (s t : LA.Term α) (p : Certificate false Γ (comparison s t)) :
    Certificate false Γ (comparison (succTerm s) (succTerm t)) := by
  apply disjElim p
  · exact disjLeft (impElim (conjRight (ltSucc s t)) (assumption (by simp)))
  · apply disjElim (assumption (A := .disj (termEqual s t) (ltFormula t s)) (by simp))
    · exact disjRight (disjLeft (succEquality (assumption (by simp))))
    · exact disjRight (disjRight (impElim (conjRight (ltSucc t s)) (assumption (by simp))))

private def everyComparison (t : LA.Term α) : Formula α :=
  allUnit (comparison (.var (.inr ())) (t.relabel Sum.inl))
@[simp] private theorem everyComparisonSubst (t : LA.Term α) {β : Type u} (σ : α → LA.Term β) :
    (everyComparison t).subst σ = everyComparison (t.subst σ) := by
  simp [everyComparison, allUnit_subst, unitSubst, term_subst_relabel, term_relabel_subst, Term.subst]
@[simp] private theorem everyComparisonRename (t : LA.Term α) {β : Type u} (f : α → β) :
    (everyComparison t).rename f = everyComparison (t.relabel f) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    everyComparisonSubst, term_subst_vars]

private def everyComparisonAt (y x : LA.Term α) (p : Certificate false Γ (everyComparison y)) :
    Certificate false Γ (comparison x y) := by
  simpa [comparisonSubst, term_subst_relabel, Term.subst] using
    allUnitElim (comparison (.var (.inr ())) (y.relabel Sum.inl)) x p

private def compareStepAt (y x : LA.Term α) (p : Certificate false Γ (everyComparison y)) :
    Certificate false Γ (comparison x (succTerm y)) := by
  apply zeroSuccElim x
  · have e : Certificate false (insert (termEqual x zeroTerm) Γ) (termEqual x zeroTerm) := assumption (by simp)
    exact comparisonCongr (equalSymmetry e) (equalIntro (succTerm y)) (disjLeft (zeroLtSucc y))
  · simp only [comparisonRename, succ_relabel]
    let x' := x.relabel (Sum.inl : α → α ⊕ Fin 1)
    let y' := y.relabel (Sum.inl : α → α ⊕ Fin 1)
    let d : LA.Term (α ⊕ Fin 1) := .var (.inr 0)
    let Δ : Context (α ⊕ Fin 1) := insert (termEqual x' (succTerm d)) (Γ.image (fun E => E.rename Sum.inl))
    have e : Certificate false Δ (termEqual x' (succTerm d)) := assumption (by simp [Δ])
    have ih : Certificate false Δ (everyComparison y') := by
      simpa only [everyComparisonRename] using liftInto p (termEqual x' (succTerm d))
    exact comparisonCongr (equalSymmetry e) (equalIntro (succTerm y'))
      (compareSuccessors d y' (everyComparisonAt y' d ih))

private def everyComparisonStep (y : LA.Term α) (p : Certificate false Γ (everyComparison y)) :
    Certificate false Γ (everyComparison (succTerm y)) := by
  apply allUnitIntro (comparison (.var (.inr ())) ((succTerm y).relabel Sum.inl))
  simp only [comparisonRename, Term.relabel, Sum.map_inr, Sum.map_inl, succ_relabel,
    Term.relabel_relabel, Function.comp_def, id_eq]
  exact compareStepAt (y.relabel Sum.inl) (.var (.inr 0)) (by
    simpa only [everyComparisonRename] using p.universeRename (Sum.inl : α → α ⊕ Fin 1))

/-- A closed proof built from the displayed quantified induction body. -/
def comparisonProof : Certificate false (∅ : Context Empty) comparisonSentence := by
  let A := comparisonInductionBody
  have ha : A = everyComparison (.var (.inr ()) : LA.Term (Fin 0 ⊕ Unit)) := rfl
  have p0 : Certificate false (∅ : Context (Fin 0)) (base A) := by
    rw [ha]
    change Certificate false ∅ ((everyComparison (.var (.inr ()) : LA.Term (Fin 0 ⊕ Unit))).subst _)
    simp only [everyComparisonSubst, Term.subst, Sum.elim_inr]
    simp only [everyComparison, zero_relabel]
    apply allUnitIntro (comparison (.var (.inr ())) (zeroTerm : LA.Term (Fin 0 ⊕ Unit)))
    simp only [comparisonRename, Term.relabel, Sum.map_inr, zero_relabel, Finset.image_empty]
    exact compareZero (Γ := ∅) (.var (.inr 0) : LA.Term (Fin 0 ⊕ Fin 1))
  let Δ : Context (Fin 0 ⊕ Fin 1) := insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let y : LA.Term (Fin 0 ⊕ Fin 1) := .var (.inr 0)
  have ih : Certificate false Δ (everyComparison y) := by
    have q : Certificate false Δ (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) := assumption (by simp [Δ])
    simpa only [ha, everyComparisonRename, Term.relabel, Sum.map_inr, y] using q
  have ps : Certificate false Δ ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa only [next, ha, everyComparisonSubst, everyComparisonRename, Term.subst,
      Sum.elim_inr, succ_relabel, Term.relabel, Sum.map_inr, y] using everyComparisonStep y ih
  have p := inductionRule A ∅ p0 (by simpa only [Δ, Finset.image_empty] using ps)
  have q := p.universeRename (Fin.elim0 : Fin 0 → Empty)
  simpa only [A, comparison_induction_closure, Finset.image_empty] using q

/-- Instantiate the same closed comparison proof at arbitrary terms and context. -/
def trichotomy (s t : LA.Term α) : Certificate false Γ (comparison s t) := by
  simpa [comparisonSentence, comparison, subst_disj, ltFormula_subst,
    termEqual_subst_poly, Term.subst] using
    Addition.instantiateClosed (comparison (.var (1 : Fin 2)) (.var (0 : Fin 2)))
      comparisonProof ![t,s] Γ

/-- Each of the three pairs of distinct alternatives has an internal contradiction proof. -/
def comparisonExclusive (s t : LA.Term α) : Certificate false Γ
    (.conj (.neg (.conj (ltFormula s t) (termEqual s t)))
      (.conj (.neg (.conj (termEqual s t) (ltFormula t s)))
        (.neg (.conj (ltFormula s t) (ltFormula t s))))) := by
  apply conjIntro
  · apply negIntro
    have p : Certificate false (insert (.conj (ltFormula s t) (termEqual s t)) Γ)
        (.conj (ltFormula s t) (termEqual s t)) := assumption (by simp)
    exact negElim (conjRight p) (strictNe s t (conjLeft p))
  · apply conjIntro
    · apply negIntro
      have p : Certificate false (insert (.conj (termEqual s t) (ltFormula t s)) Γ)
          (.conj (termEqual s t) (ltFormula t s)) := assumption (by simp)
      exact negElim (equalSymmetry (conjLeft p)) (strictNe t s (conjRight p))
    · apply negIntro
      have p : Certificate false (insert (.conj (ltFormula s t) (ltFormula t s)) Γ)
          (.conj (ltFormula s t) (ltFormula t s)) := assumption (by simp)
      exact strictReverseLeFalse s t (conjLeft p) (ltToLe t s (conjRight p))

def leDecision (s t : LA.Term α) : Certificate false Γ
    (.disj (leFormula s t) (.neg (leFormula s t))) := by
  apply disjElim (trichotomy s t)
  · exact disjLeft (ltToLe s t (assumption (by simp)))
  · apply disjElim (assumption (A := .disj (termEqual s t) (ltFormula t s)) (by simp))
    · exact disjLeft (eqLe s t (assumption (by simp)))
    · apply disjRight
      apply negIntro
      exact strictReverseLeFalse t s (assumption (by simp)) (assumption (by simp))

def ltDecision (s t : LA.Term α) : Certificate false Γ
    (.disj (ltFormula s t) (.neg (ltFormula s t))) := by
  apply disjElim (trichotomy s t)
  · exact disjLeft (assumption (by simp))
  · apply disjElim (assumption (A := .disj (termEqual s t) (ltFormula t s)) (by simp))
    · apply disjRight
      apply negIntro
      exact negElim (assumption (A := termEqual s t) (by simp))
        (strictNe s t (assumption (by simp)))
    · apply disjRight
      apply negIntro
      exact strictReverseLeFalse s t (assumption (by simp))
        (ltToLe t s (assumption (by simp)))

def notReverseLt (s t : LA.Term α) : Certificate false Γ
    (iffFormula (.neg (ltFormula t s)) (leFormula s t)) := by
  apply conjIntro
  · apply impIntro
    apply disjElim (trichotomy s t)
    · exact ltToLe s t (assumption (by simp))
    · apply disjElim (assumption (A := .disj (termEqual s t) (ltFormula t s)) (by simp))
      · exact eqLe s t (assumption (by simp))
      · exact falsumElim (negElim (assumption (A := ltFormula t s) (by simp)) (assumption (by simp)))
  · apply impIntro
    apply negIntro
    exact strictReverseLeFalse t s (assumption (by simp)) (assumption (by simp))

def notReverseLe (s t : LA.Term α) : Certificate false Γ
    (iffFormula (.neg (leFormula t s)) (ltFormula s t)) := by
  apply conjIntro
  · apply impIntro
    apply disjElim (trichotomy s t)
    · exact assumption (by simp)
    · apply disjElim (assumption (A := .disj (termEqual s t) (ltFormula t s)) (by simp))
      · exact falsumElim (negElim (eqLe t s (equalSymmetry (assumption (by simp))))
          (assumption (by simp)))
      · exact falsumElim (negElim (ltToLe t s (assumption (by simp))) (assumption (by simp)))
  · apply impIntro
    apply negIntro
    exact strictReverseLeFalse s t (assumption (by simp)) (assumption (by simp))

/-- Right addition preserves and reflects the literal supplied non-strict witness. -/
def addRightWitness (s t a d : LA.Term α) : Certificate false Γ
    (iffFormula (termEqual (addTerm d (addTerm s a)) (addTerm t a))
      (termEqual (addTerm d s) t)) := by
  apply conjIntro
  · apply impIntro
    exact Addition.cancelRight a (addTerm d s) t
      (equalTransitivity (Addition.associative d s a) (assumption (by simp)))
  · apply impIntro
    exact equalTransitivity (equalSymmetry (Addition.associative d s a))
      (addEquality (assumption (by simp)) (equalIntro a))

/-- The strict witness has the same value on both sides of right cancellation. -/
def addRightStrictWitness (s t a d : LA.Term α) : Certificate false Γ
    (iffFormula (termEqual (addTerm d (succTerm (addTerm s a))) (addTerm t a))
      (termEqual (addTerm d (succTerm s)) t)) := by
  apply conjIntro
  · apply impIntro
    exact impElim (conjLeft (addRightWitness (succTerm s) t a d))
      (equalTransitivity (addEquality (equalIntro d) (Addition.successorLeft s a))
        (assumption (by simp)))
  · apply impIntro
    exact equalTransitivity (addEquality (equalIntro d) (equalSymmetry (Addition.successorLeft s a)))
      (impElim (conjRight (addRightWitness (succTerm s) t a d)) (assumption (by simp)))

/-- Left addition also retains the specified witness rather than choosing a new one. -/

private def shuffle (d a s : LA.Term α) :
    Certificate false Γ (termEqual (addTerm d (addTerm a s)) (addTerm a (addTerm d s))) :=
  equalTransitivity (equalSymmetry (Addition.associative d a s))
    (equalTransitivity (addEquality (Addition.commutative d a) (equalIntro s))
      (Addition.associative a d s))

def addLeftWitness (s t a d : LA.Term α) : Certificate false Γ
    (iffFormula (termEqual (addTerm d (addTerm a s)) (addTerm a t))
      (termEqual (addTerm d s) t)) := by
  apply conjIntro
  · apply impIntro
    exact Addition.cancelLeft a (addTerm d s) t
      (equalTransitivity (equalSymmetry (shuffle d a s)) (assumption (by simp)))
  · apply impIntro
    exact equalTransitivity (shuffle d a s)
      (addEquality (equalIntro a) (assumption (by simp)))

def addLeftStrictWitness (s t a d : LA.Term α) : Certificate false Γ
    (iffFormula (termEqual (addTerm d (succTerm (addTerm a s))) (addTerm a t))
      (termEqual (addTerm d (succTerm s)) t)) := by
  apply conjIntro
  · apply impIntro
    exact impElim (conjLeft (addLeftWitness (succTerm s) t a d))
      (equalTransitivity (addEquality (equalIntro d) (addSucc basicIn a s))
        (assumption (by simp)))
  · apply impIntro
    exact equalTransitivity (addEquality (equalIntro d) (equalSymmetry (addSucc basicIn a s)))
      (impElim (conjRight (addLeftWitness (succTerm s) t a d)) (assumption (by simp)))

def addRightLe (s t a : LA.Term α) : Certificate false Γ
    (iffFormula (leFormula (addTerm s a) (addTerm t a)) (leFormula s t)) := by
  apply conjIntro
  · apply impIntro
    apply mapLeWitness (addTerm s a) (addTerm t a) (s) t (assumption (by simp))
    intro p
    exact impElim (conjLeft (addRightWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0))))
      (by simpa only [add_relabel, succ_relabel] using p)
  · apply impIntro
    apply mapLeWitness (s) t (addTerm s a) (addTerm t a) (assumption (by simp))
    intro p
    simpa only [add_relabel, succ_relabel] using
      impElim (conjRight (addRightWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0)))) p

def addRightLt (s t a : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula (addTerm s a) (addTerm t a)) (ltFormula s t)) := by
  apply conjIntro
  · apply impIntro
    apply mapLeWitness (succTerm (addTerm s a)) (addTerm t a) (succTerm s) t (assumption (by simp [ltFormula]))
    intro p
    exact impElim (conjLeft (addRightStrictWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0))))
      (by simpa only [add_relabel, succ_relabel] using p)
  · apply impIntro
    apply mapLeWitness (succTerm s) t (succTerm (addTerm s a)) (addTerm t a) (assumption (by simp [ltFormula]))
    intro p
    simpa only [add_relabel, succ_relabel] using
      impElim (conjRight (addRightStrictWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0)))) p

def addLeftLe (s t a : LA.Term α) : Certificate false Γ
    (iffFormula (leFormula (addTerm a s) (addTerm a t)) (leFormula s t)) := by
  apply conjIntro
  · apply impIntro
    apply mapLeWitness (addTerm a s) (addTerm a t) (s) t (assumption (by simp))
    intro p
    exact impElim (conjLeft (addLeftWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0))))
      (by simpa only [add_relabel, succ_relabel] using p)
  · apply impIntro
    apply mapLeWitness (s) t (addTerm a s) (addTerm a t) (assumption (by simp))
    intro p
    simpa only [add_relabel, succ_relabel] using
      impElim (conjRight (addLeftWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0)))) p

def addLeftLt (s t a : LA.Term α) : Certificate false Γ
    (iffFormula (ltFormula (addTerm a s) (addTerm a t)) (ltFormula s t)) := by
  apply conjIntro
  · apply impIntro
    apply mapLeWitness (succTerm (addTerm a s)) (addTerm a t) (succTerm s) t (assumption (by simp [ltFormula]))
    intro p
    exact impElim (conjLeft (addLeftStrictWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0))))
      (by simpa only [add_relabel, succ_relabel] using p)
  · apply impIntro
    apply mapLeWitness (succTerm s) t (succTerm (addTerm a s)) (addTerm a t) (assumption (by simp [ltFormula]))
    intro p
    simpa only [add_relabel, succ_relabel] using
      impElim (conjRight (addLeftStrictWitness (s.relabel Sum.inl) (t.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr 0)))) p


end
end Lemmatheca.ProofTheory.HeytingArithmetic.Order
