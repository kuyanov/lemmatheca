import Lemmatheca.HeytingArithmeticBoundedFormulas.Decisions
import Lemmatheca.ArithmeticNegativeTranslation.QuantifierFree

namespace Lemmatheca.ProofTheory.HeytingArithmetic.BoundedNegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation (negative)
open Bounded StrongInduction
open _root_.Lemmatheca.ProofTheory.HeytingArithmetic.Order
noncomputable section
local instance bantConversionFormulaEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _
variable {α : Type}
open TheoryCertificate
open Lemmatheca.MathematicalLogic.FirstOrderProofs (term_subst_vars)

private def doubleNegate {Γ : Context α} {P : Formula α}
    (p : Certificate false Γ P) : Certificate false Γ (.neg (.neg P)) :=
  negIntro (negElim (p.weaken (Finset.subset_insert _ _))
    (assumption (Finset.mem_insert_self _ _)))


/-- Maps actual original HA certificates uniformly in every finite additional context. -/
abbrev ProofMap (P Q : Formula α) :=
  ∀ {Γ : Context α}, Certificate false Γ P → Certificate false Γ Q

/-- Two supplied proof-construction maps; no semantic consequence or new calculus. -/
structure Conversions (P Q : Formula α) where
  forward : ProofMap P Q
  backward : ProofMap Q P

abbrev Fixed (P : Formula α) := Conversions P (negative P)

/-- Transport a supplied certificate map without eliminating double negation. -/
def doubleNegationMap {P Q : Formula α} (f : ProofMap P Q) :
    ProofMap (.neg (.neg P)) (.neg (.neg Q)) := by
  intro Γ p
  apply negIntro
  have hn : Certificate false (insert (.neg Q) Γ) (.neg P) := by
    apply negIntro
    exact negElim (f (assumption (by simp))) (assumption (A := .neg Q) (by simp))
  exact negElim hn (p.weaken (Finset.subset_insert _ _))

/-- Use exactly the supplied native closed stability certificate. -/
def stableOutput {P Q : Formula α} (f : ProofMap P Q)
    (hQ : Certificate false (∅ : Context α) (.impl (.neg (.neg Q)) Q)) :
    ProofMap (.neg (.neg P)) Q := by
  intro Γ p
  exact impElim (hQ.weaken (Finset.empty_subset Γ)) (doubleNegationMap f p)

/-- Actual context-preserving native connective operations. -/
def negationConversions {P Q : Formula α} (c : Conversions P Q) :
    Conversions (.neg P) (.neg Q) := by
  refine ⟨?_, ?_⟩
  · intro Γ p
    exact negIntro (negElim (c.backward (assumption (by simp)))
      (p.weaken (Finset.subset_insert _ _)))
  · intro Γ p
    exact negIntro (negElim (c.forward (assumption (by simp)))
      (p.weaken (Finset.subset_insert _ _)))

def conjunctionConversions {P P' Q Q' : Formula α}
    (p : Conversions P P') (q : Conversions Q Q') :
    Conversions (.conj P Q) (.conj P' Q') := by
  exact ⟨fun h => conjIntro (p.forward (conjLeft h)) (q.forward (conjRight h)),
    fun h => conjIntro (p.backward (conjLeft h)) (q.backward (conjRight h))⟩

def implicationConversions {P P' Q Q' : Formula α}
    (p : Conversions P P') (q : Conversions Q Q') :
    Conversions (.impl P Q) (.impl P' Q') := by
  refine ⟨?_, ?_⟩
  · intro Γ h
    exact impIntro (q.forward (impElim (h.weaken (Finset.subset_insert _ _))
      (p.backward (assumption (by simp)))))
  · intro Γ h
    exact impIntro (q.backward (impElim (h.weaken (Finset.subset_insert _ _))
      (p.forward (assumption (by simp)))))

/-- Stability is required at the original whole disjunction. -/
def disjunctionConversions {P P' Q Q' : Formula α}
    (p : Conversions P P') (q : Conversions Q Q')
    (h : Certificate false (∅ : Context α)
      (.impl (.neg (.neg (.disj P Q))) (.disj P Q))) :
    Conversions (.disj P Q) (.neg (.neg (.disj P' Q'))) := by
  refine ⟨?_, ?_⟩
  · intro Γ r
    exact disjElim r
      (doubleNegate (disjLeft (p.forward (assumption (by simp)))))
      (doubleNegate (disjRight (q.forward (assumption (by simp)))))
  · intro Γ r
    apply stableOutput (P := .disj P' Q') (Q := .disj P Q) ?_ h r
    intro Δ t
    exact disjElim t (disjLeft (p.backward (assumption (by simp))))
      (disjRight (q.backward (assumption (by simp))))

private def inputEquiv (δ : Type) : (δ ⊕ Unit) ≃ (δ ⊕ Fin 1) where
  toFun := Sum.map id (fun _ => 0)
  invFun := Sum.map id (fun _ => ())
  left_inv x := by cases x <;> rfl
  right_inv x := by
    cases x with
    | inl a => rfl
    | inr i => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl

private def renameConversions {δ ε : Type} (e : δ ≃ ε)
    {P Q : Formula δ} (c : Conversions P Q) :
    Conversions (P.rename e) (Q.rename e) := by
  have round (F : Formula ε) : (F.rename e.symm).rename e = F :=
    formula_reindex_roundtrip e.symm F
  have contextRound (Γ : Context ε) :
      (Γ.image (fun F => F.rename e.symm)).image (fun F => F.rename e) = Γ := by
    simp only [Finset.image_image, Function.comp_def, round, Finset.image_id']
  refine ⟨?_, ?_⟩
  · intro Γ p
    have q : Certificate false (Γ.image (fun F => F.rename e.symm)) P := by
      simpa only [formula_reindex_roundtrip] using p.rename e.symm
    have r := (c.forward q).rename e
    simpa only [contextRound] using r
  · intro Γ p
    have q : Certificate false (Γ.image (fun F => F.rename e.symm)) Q := by
      simpa only [formula_reindex_roundtrip] using p.rename e.symm
    have r := (c.backward q).rename e
    simpa only [contextRound] using r

private theorem openInstance (D : BF α 1) :
    (D.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = D.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i => have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl

private def openAllUnit {Γ : Context α} (P : Formula (α ⊕ Unit))
    (p : Certificate false Γ (allUnit P)) :
    Certificate false (Γ.image (fun F => F.rename (Sum.inl : α → α ⊕ Fin 1)))
      (P.rename (inputEquiv α)) := by
  have pr := p.rename (Sum.inl : α → α ⊕ Fin 1)
  have pa : Certificate false (Γ.image (fun F => F.rename (Sum.inl : α → α ⊕ Fin 1)))
      (.all ((bindUnit P).rename Sum.inl)) := by
    simpa only [allUnit, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      subst_all] using pr
  have q := allElim (.var (.inr 0)) pa
  rw [openInstance, bindUnit_open] at q
  exact q

private def introduceOpenedEx (Q : Formula (α ⊕ Unit)) {Δ : Context (α ⊕ Fin 1)}
    (q : Certificate false Δ (Q.rename (inputEquiv α))) :
    Certificate false Δ ((exUnit Q).rename (Sum.inl : α → α ⊕ Fin 1)) := by
  have q' : Certificate false Δ
      (((bindUnit Q).rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0))) := by
    rw [openInstance, bindUnit_open]
    exact q
  have r := exIntro (D := (bindUnit Q).rename (Sum.inl : α → α ⊕ Fin 1))
    (.var (Sum.inr (0 : Fin 1)) : LA.Term (α ⊕ Fin 1)) q'
  simpa only [exUnit, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    subst_ex] using r

/-- Quantification acts on the actual one-input native bodies, including their scope tags. -/
def allUnitConversions {P Q : Formula (α ⊕ Unit)} (c : Conversions P Q) :
    Conversions (allUnit P) (allUnit Q) := by
  let c' := renameConversions (inputEquiv α) c
  refine ⟨?_, ?_⟩
  · intro Γ p
    apply allUnitIntro Q
    exact c'.forward (openAllUnit P p)
  · intro Γ p
    apply allUnitIntro P
    exact c'.backward (openAllUnit Q p)

def exUnitConversions {P Q : Formula (α ⊕ Unit)} (c : Conversions P Q) :
    Conversions (exUnit P) (exUnit Q) := by
  let c' := renameConversions (inputEquiv α) c
  refine ⟨?_, ?_⟩
  · intro Γ p
    apply exUnitEliminate P p
    exact introduceOpenedEx Q (c'.forward (assumption (Finset.mem_insert_self _ _)))
  · intro Γ p
    apply exUnitEliminate Q p
    exact introduceOpenedEx P (c'.backward (assumption (Finset.mem_insert_self _ _)))

private theorem negative_exUnit (A : Formula (α ⊕ Unit)) :
    negative (exUnit A) = .neg (.neg (exUnit (negative A))) := by
  simp only [exUnit, negative, NegativeTranslation.negative_bindUnit]

private def doubleNegatedConversions {P Q : Formula α} (c : Conversions P Q)
    (h : Certificate false (∅ : Context α) (.impl (.neg (.neg P)) P)) :
    Conversions P (.neg (.neg Q)) :=
  ⟨fun p => doubleNegate (c.forward p), stableOutput c.backward h⟩

private def quantifierFreeConversions (P : Formula α) (hP : P.QuantifierFree) : Fixed P :=
  ⟨NegativeTranslation.quantifierFreeToNegative P hP,
    NegativeTranslation.quantifierFreeFromNegative P hP⟩

/-- The defined additive order macro, with its actual difference existential. -/
def leConversions (s t : LA.Term α) : Fixed (leFormula s t) := by
  let cb := quantifierFreeConversions (leBody s t) trivial
  let ce := exUnitConversions cb
  have h : Certificate false (∅ : Context α)
      (.impl (.neg (.neg (leFormula s t))) (leFormula s t)) :=
    stabilityFromDecision _ (leDecision s t)
  simpa only [Fixed, leFormula, negative_exUnit] using doubleNegatedConversions ce h

def ltConversions (s t : LA.Term α) : Fixed (ltFormula s t) := leConversions (succTerm s) t

/-- Strict and inclusive universal guard bridges do not require body decidability. -/
def strictAllConversions (A : Formula (α ⊕ Unit)) (t : LA.Term α) (c : Fixed A) :
    Fixed (history A t) := by
  let cg := ltConversions (.var (.inr ())) (t.relabel Sum.inl)
  let cc := allUnitConversions (implicationConversions cg c)
  simpa only [Fixed, history, NegativeTranslation.negative_allUnit, negative] using cc

def inclusiveAllConversions (A : Formula (α ⊕ Unit)) (t : LA.Term α) (c : Fixed A) :
    Fixed (inclusiveAll A t) := by
  let cg := leConversions (.var (.inr ())) (t.relabel Sum.inl)
  let cc := allUnitConversions (implicationConversions cg c)
  simpa only [Fixed, inclusiveAll, NegativeTranslation.negative_allUnit, negative] using cc

/-- These operations retain the original whole-existential stability requirement. -/
def strictExistsConversions (A : Formula (α ⊕ Unit)) (t : LA.Term α) (c : Fixed A)
    (h : Certificate false (∅ : Context α)
      (.impl (.neg (.neg (strictExists A t))) (strictExists A t))) :
    Fixed (strictExists A t) := by
  let cg := ltConversions (.var (.inr ())) (t.relabel Sum.inl)
  let ce := exUnitConversions (conjunctionConversions cg c)
  simpa only [Fixed, strictExists, negative_exUnit, negative] using
    doubleNegatedConversions ce h

def inclusiveExistsConversions (A : Formula (α ⊕ Unit)) (t : LA.Term α) (c : Fixed A)
    (h : Certificate false (∅ : Context α)
      (.impl (.neg (.neg (inclusiveExists A t))) (inclusiveExists A t))) :
    Fixed (inclusiveExists A t) := by
  let cg := leConversions (.var (.inr ())) (t.relabel Sum.inl)
  let ce := exUnitConversions (conjunctionConversions cg c)
  simpa only [Fixed, inclusiveExists, negative_exUnit, negative] using
    doubleNegatedConversions ce h

/-- The recursive native proof construction on the actual bounded expression tree. -/
def boundedConversions {α : Type} [Fintype α] (B : Expr α) : Fixed B.expand := by
  revert ‹Fintype α›
  induction B with
  | falsum => intro _; exact quantifierFreeConversions .falsum trivial
  | equal s t => intro _; exact quantifierFreeConversions (termEqual s t) trivial
  | le s t => intro _; exact leConversions s t
  | lt s t => intro _; exact ltConversions s t
  | neg B ih => intro _; exact negationConversions ih
  | conj B C ihB ihC => intro _; exact conjunctionConversions ihB ihC
  | disj B C ihB ihC =>
    intro _
    exact disjunctionConversions ihB ihC (stability (.disj B C))
  | impl B C ihB ihC => intro _; exact implicationConversions ihB ihC
  | allLT t B ih => intro _; exact strictAllConversions B.expand t ih
  | exLT t B ih =>
    intro _
    exact strictExistsConversions B.expand t ih (stability (.exLT t B))
  | allLE t B ih => intro _; exact inclusiveAllConversions B.expand t ih
  | exLE t B ih =>
    intro _
    exact inclusiveExistsConversions B.expand t ih (stability (.exLE t B))

/-- Closed implications over the actual ordered original parameter tuple. -/
def boundedClosedForward {k : ℕ} (B : Expr (Fin k)) :
    Certificate false (∅ : Context Empty)
      (close (.impl B.expand (negative B.expand))) := by
  apply closeCertificate
  exact impIntro ((boundedConversions B).forward (assumption (Finset.mem_insert_self _ _)))

def boundedClosedBackward {k : ℕ} (B : Expr (Fin k)) :
    Certificate false (∅ : Context Empty)
      (close (.impl (negative B.expand) B.expand)) := by
  apply closeCertificate
  exact impIntro ((boundedConversions B).backward (assumption (Finset.mem_insert_self _ _)))

/-- The target name set may be infinite; only the original parameter tuple is finite. -/
def boundedInstanceConversions {k : ℕ} {β : Type} (B : Expr (Fin k))
    (σ : Fin k → LA.Term β) : Fixed (B.subst σ).expand := by
  have pf : Certificate false (∅ : Context (Fin k)) (.impl B.expand (negative B.expand)) :=
    impIntro ((boundedConversions B).forward (assumption (Finset.mem_insert_self _ _)))
  have pb : Certificate false (∅ : Context (Fin k)) (.impl (negative B.expand) B.expand) :=
    impIntro ((boundedConversions B).backward (assumption (Finset.mem_insert_self _ _)))
  have pf' : Certificate false (∅ : Context β)
      (.impl (B.subst σ).expand (negative (B.subst σ).expand)) := by
    simpa only [Finset.image_empty, subst_impl, expand_subst,
      Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.negative_subst] using pf.substitute σ
  have pb' : Certificate false (∅ : Context β)
      (.impl (negative (B.subst σ).expand) (B.subst σ).expand) := by
    simpa only [Finset.image_empty, subst_impl, expand_subst,
      Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation.negative_subst] using pb.substitute σ
  exact ⟨fun p => impElim (pf'.weaken (Finset.empty_subset _)) p,
    fun p => impElim (pb'.weaken (Finset.empty_subset _)) p⟩

end
end Lemmatheca.ProofTheory.HeytingArithmetic.BoundedNegativeTranslation
