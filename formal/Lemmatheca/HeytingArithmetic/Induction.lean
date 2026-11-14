import Lemmatheca.HeytingArithmetic.Certificates

namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder (ScopeSubst liftScope scopeInclusion)
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v
variable {α : Type u} {β : Type v}
noncomputable section
local instance haInductionEq {α : Type*} : DecidableEq (Formula α) := Classical.decEq _

def unitSubst (σ : α → LA.Term β) : α ⊕ Unit → LA.Term (β ⊕ Unit) :=
  Sum.elim (fun x => (σ x).relabel Sum.inl) (fun _ => .var (.inr ()))

theorem bindUnit_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (bindUnit A).subst σ = bindUnit (A.subst (unitSubst σ)) := by
  unfold bindUnit Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp, map_comp]
  congr 1
  funext z
  cases z with
  | inl a =>
    cases a with
    | inl a =>
      simp [freeScope, unitSubst, term_subst_relabel, Term.relabel_relabel]
    | inr u => rfl
  | inr i => exact i.elim0

theorem allUnit_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (allUnit A).subst σ = allUnit (A.subst (unitSubst σ)) := by
  unfold allUnit
  rw [subst_all, bindUnit_subst]

theorem exUnit_subst (A : Formula (α ⊕ Unit)) (σ : α → LA.Term β) :
    (exUnit A).subst σ = exUnit (A.subst (unitSubst σ)) := by
  unfold exUnit
  rw [subst_ex, bindUnit_subst]

@[simp] theorem zero_subst (σ : α → LA.Term β) : (zeroTerm : LA.Term α).subst σ = zeroTerm := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  exact i.elim0
@[simp] theorem zero_relabel (f : α → β) : (zeroTerm : LA.Term α).relabel f = zeroTerm := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  exact i.elim0
@[simp] theorem succ_subst (t : LA.Term α) (σ : α → LA.Term β) :
    (succTerm t).subst σ = succTerm (t.subst σ) := rfl
@[simp] theorem succ_relabel (t : LA.Term α) (f : α → β) :
    (succTerm t).relabel f = succTerm (t.relabel f) := rfl
@[simp] theorem add_subst (s t : LA.Term α) (σ : α → LA.Term β) :
    (addTerm s t).subst σ = addTerm (s.subst σ) (t.subst σ) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem mul_subst (s t : LA.Term α) (σ : α → LA.Term β) :
    (mulTerm s t).subst σ = mulTerm (s.subst σ) (t.subst σ) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem add_relabel (s t : LA.Term α) (f : α → β) :
    (addTerm s t).relabel f = addTerm (s.relabel f) (t.relabel f) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem mul_relabel (s t : LA.Term α) (f : α → β) :
    (mulTerm s t).relabel f = mulTerm (s.relabel f) (t.relabel f) := by
  change Term.func _ _ = Term.func _ _
  congr 1
  funext i
  fin_cases i <;> rfl

def slotSubst {n} (ts : Fin n → LA.Term α) : ScopeSubst LA α α n 0 :=
  Sum.elim (fun x => .var (.inl x)) (fun i => (ts i).relabel Sum.inl)

theorem instantiateSlots_zero (A : Formula α) (ts : Fin 0 → LA.Term α) :
    A.instantiateSlots ts = A := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
  have h : (Sum.elim (fun x => (.var (.inl x) : LA.Term (α ⊕ Fin 0)))
      (fun i => (ts i).relabel Sum.inl)) = Term.var := by
    funext z
    cases z with
    | inl a => rfl
    | inr i => exact i.elim0
  rw [h, map_id]

theorem instantiateSlots_last {n} (A : BF α (n+1)) (ts : Fin n → LA.Term α) (t : LA.Term α) :
    (A.map (liftScope (slotSubst ts))).instantiate t = A.instantiateSlots (Fin.snoc ts t) := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
  rw [map_comp]
  congr 1
  funext z
  cases z with
  | inl a => rfl
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [liftScope, Fin.snoc_last, Term.subst]
    · simp [liftScope, slotSubst, term_subst_relabel,
        Term.relabel_relabel, scopeInclusion]

theorem allSlots_subst {n} (A : BF α n) (σ : α → LA.Term β) :
    (allSlots A).subst σ = allSlots (A.subst σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [allSlots, subst_all] using ih (.all A)

theorem close_rename {k} (A : Formula (Fin k)) :
    (close A).rename (Empty.elim : Empty → α) =
      allSlots (A.map (Sum.elim (fun i => (.var (.inr i) : LA.Term (α ⊕ Fin k))) Fin.elim0)) := by
  unfold close Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
  rw [allSlots_subst]
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp]
  congr 2
  funext z
  cases z with
  | inl i => rfl
  | inr i => exact i.elim0

theorem close_instance {k} (A : Formula (Fin k)) (ts : Fin k → LA.Term α) :
    (A.map (Sum.elim (fun i => (.var (.inr i) : LA.Term (α ⊕ Fin k))) Fin.elim0)).instantiateSlots ts =
      A.subst ts := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [map_comp]
  congr 1
  funext z
  cases z with
  | inl i => rfl
  | inr i => exact i.elim0

namespace TheoryCertificate
variable {T : Set Sentence} {Γ : Context α} {c : Bool}

def allSlotsElim {n} (A : BF α n) (p : TheoryCertificate c T Γ (allSlots A))
    (ts : Fin n → LA.Term α) : TheoryCertificate c T Γ (A.instantiateSlots ts) := by
  induction n with
  | zero => simpa only [allSlots, instantiateSlots_zero] using p
  | succ n ih =>
    let initial : Fin n → LA.Term α := fun i => ts i.castSucc
    have q := ih (.all A) p initial
    change TheoryCertificate c T Γ (.all (A.map (liftScope (slotSubst initial)))) at q
    have r := allElim (ts (Fin.last n)) q
    rw [instantiateSlots_last] at r
    have hs : Fin.snoc initial (ts (Fin.last n)) = ts := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [initial]
    rw [hs] at r
    exact r

def closeElim {k} (A : Formula (Fin k)) (ts : Fin k → LA.Term α)
    (p : TheoryCertificate c T Γ ((close A).rename Empty.elim)) :
    TheoryCertificate c T Γ (A.subst ts) := by
  rw [close_rename] at p
  simpa only [close_instance] using allSlotsElim _ p ts

def allUnitElim (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : TheoryCertificate c T Γ (allUnit A)) :
    TheoryCertificate c T Γ (A.subst (Sum.elim Term.var (fun _ => t))) := by
  rw [← bindUnit_instance]
  exact allElim t p

def allUnitIntro (A : Formula (α ⊕ Unit))
    (p : TheoryCertificate c T (Γ.image (fun B => B.rename Sum.inl))
      (A.rename (Sum.map id (fun _ => (0 : Fin 1))))) :
    TheoryCertificate c T Γ (allUnit A) := by
  apply allIntro
  simpa only [bindUnit_open] using p

def exUnitIntro (A : Formula (α ⊕ Unit)) (t : LA.Term α)
    (p : TheoryCertificate c T Γ (A.subst (Sum.elim Term.var (fun _ => t)))) :
    TheoryCertificate c T Γ (exUnit A) := by
  apply exIntro t
  simpa only [bindUnit_instance] using p

end TheoryCertificate

/-- A finite proof construction over any arithmetic theory containing full induction. -/
def inductionFor {T : Set Sentence} (hT : inductionTheory ⊆ T) {k}
    (A : Formula (Fin k ⊕ Unit)) (Γ : Context (Fin k))
    (p0 : TheoryCertificate false T Γ (base A))
    (pstep : TheoryCertificate false T
      (insert (A.rename (Sum.map id (fun _ => (0 : Fin 1))))
        (Γ.image (fun B => B.rename (Sum.inl : Fin k → Fin k ⊕ Fin 1))))
      ((next A).rename (Sum.map id (fun _ => (0 : Fin 1))))) :
    TheoryCertificate false T Γ (allUnit A) := by
  let step : TheoryCertificate false T Γ (allUnit (.impl A (next A))) :=
    TheoryCertificate.allUnitIntro _ (by
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, subst_impl] using
        TheoryCertificate.impIntro pstep)
  let pa := TheoryCertificate.fromAxiom (c := false) (Γ := Γ) (inductionAxiom A)
    (hT ⟨k, A, rfl⟩)
  have pi : TheoryCertificate false T Γ
      (.impl (.conj (base A) (allUnit (.impl A (next A)))) (allUnit A)) := by
    have q := TheoryCertificate.closeElim
      (.impl (.conj (base A) (allUnit (.impl A (next A)))) (allUnit A)) Term.var pa
    simpa only [subst_id] using q
  exact TheoryCertificate.impElim pi (TheoryCertificate.conjIntro p0 step)

/-- The actual finite proof construction from a base and a protected step.
The finite original parameters and extra assumptions remain fixed. -/
def inductionRule {k} (A : Formula (Fin k ⊕ Unit)) (Γ : Context (Fin k))
    (p0 : Certificate false Γ (base A))
    (pstep : Certificate false
      (insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)) ))
        (Γ.image (fun B => B.rename (Sum.inl : Fin k → Fin k ⊕ Fin 1))))
      ((next A).rename (Sum.map id (fun _ => (0 : Fin 1))))) :
    Certificate false Γ (allUnit A) := by
  exact inductionFor (fun _ h => Or.inr h) A Γ p0 pstep

namespace TheoryCertificate
variable {T : Set Sentence} {Γ : Context α} {c : Bool}
def equalIntro (t : LA.Term α) : TheoryCertificate c T Γ (termEqual t t) :=
  ofProof (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof.equalIntro t)
end TheoryCertificate

theorem lastCases_one {δ : Sort*} (a : δ) (f : Fin 0 → δ) :
    Fin.lastCases a f (0 : Fin 1) = a := by
  change Fin.lastCases a f (Fin.last 0) = a
  exact Fin.lastCases_last
theorem lastCases_two_zero {δ : Sort*} (a : δ) (f : Fin 1 → δ) :
    Fin.lastCases a f (0 : Fin 2) = f 0 := by
  change Fin.lastCases a f (Fin.castSucc (0 : Fin 1)) = f 0
  exact Fin.lastCases_castSucc _
theorem lastCases_two_one {δ : Sort*} (a : δ) (f : Fin 1 → δ) :
    Fin.lastCases a f (1 : Fin 2) = a := by
  change Fin.lastCases a f (Fin.last 1) = a
  exact Fin.lastCases_last

/-- This supplied tree uses induction only, with no basic arithmetic axiom. -/
def zeroOrSuccessorProof : TheoryCertificate false inductionTheory (∅ : Context Empty)
    zeroOrSuccessor := by
  let A : Formula (Fin 0 ⊕ Unit) := .disj (termEqual (.var (.inr ())) zeroTerm)
    (exUnit (termEqual (.var (.inl (.inr ()))) (succTerm (.var (.inr ())))))
  have p0 : TheoryCertificate false inductionTheory (∅ : Context (Fin 0)) (base A) := by
    unfold base
    dsimp only [A]
    rw [subst_disj, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual_subst]
    simp only [Term.subst, Sum.elim_inr, zero_subst]
    exact TheoryCertificate.disjLeft (TheoryCertificate.equalIntro zeroTerm)
  let Γ : Context (Fin 0 ⊕ Fin 1) :=
    insert (A.rename (Sum.map id (fun _ => (0 : Fin 1)))) ∅
  let u : LA.Term (Fin 0 ⊕ Fin 1) := .var (.inr 0)
  let E : Formula ((Fin 0 ⊕ Fin 1) ⊕ Unit) :=
    termEqual ((succTerm u).relabel Sum.inl) (succTerm (.var (.inr ())))
  have pe : TheoryCertificate false inductionTheory Γ (exUnit E) := by
    apply TheoryCertificate.exUnitIntro E u
    simpa [E, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual_subst,
      term_subst_relabel, succ_subst, Term.subst] using
      (TheoryCertificate.equalIntro (c := false) (T := inductionTheory) (Γ := Γ) (succTerm u))
  have ps : TheoryCertificate false inductionTheory Γ
      ((next A).rename (Sum.map id (fun _ => (0 : Fin 1)))) := by
    simpa [A, next, E, u, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      subst_disj, exUnit_subst, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual_subst,
      unitSubst, succ_subst, zero_subst, term_subst_relabel, Term.subst] using
      (TheoryCertificate.disjRight (A := termEqual (succTerm u) zeroTerm) pe)
  have p := inductionFor (T := inductionTheory) (fun _ h => h) A ∅ p0
    (by simpa only [Γ, Finset.image_empty] using ps)
  have q := p.rename (Fin.elim0 : Fin 0 → Empty)
  let D : Formula (Fin 1) := .disj (termEqual (.var 0) zeroTerm)
    (exUnit (termEqual (.var (.inl 0)) (succTerm (.var (.inr ())))))
  change TheoryCertificate false inductionTheory (∅ : Context Empty) (close D)
  simpa [A, D, close, allSlots, allUnit, bindUnit, exUnit, liftScope, scopeInclusion, lastCases_one, lastCases_two_zero, lastCases_two_one,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual,
    term_subst_relabel, term_subst_vars, Term.relabel_relabel,
    zero_relabel, succ_relabel, Term.subst, Term.relabel, Finset.image_empty] using q

namespace TheoryCertificate
variable {T : Set Sentence} {c : Bool}
def closeOneIntro (D : Formula (Fin 1))
    (p : TheoryCertificate c T (∅ : Context (Fin 1)) D) :
    TheoryCertificate c T (∅ : Context Empty) (close D) := by
  let B : BF Empty 1 := D.map (Sum.elim (fun i => .var (.inr i)) Fin.elim0)
  have hb : B.toFormula = D.rename (Sum.inr : Fin 1 → Empty ⊕ Fin 1) := by
    unfold B Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    rw [map_comp]
    congr 1
    funext z
    cases z with
    | inl i => rfl
    | inr i => exact i.elim0
  change TheoryCertificate c T ∅ (.all B)
  apply allIntro
  simpa only [hb, Finset.image_empty] using p.rename (Sum.inr : Fin 1 → Empty ⊕ Fin 1)
end TheoryCertificate

/-- The omitted predecessor sentence has an actual constructive six-axiom proof. -/
def predecessorFromInduction : TheoryCertificate false sixTheory (∅ : Context Empty)
    qPredecessor := by
  let x : LA.Term (Fin 1) := .var 0
  let E : Formula (Fin 1 ⊕ Unit) := termEqual (.var (.inl 0)) (succTerm (.var (.inr ())))
  let Z : Formula (Fin 1) := .disj (termEqual x zeroTerm) (exUnit E)
  let D : Formula (Fin 1) := .impl (.neg (termEqual x zeroTerm)) (exUnit E)
  have z0 := zeroOrSuccessorProof.mono (S := sixTheory) (fun _ h => Or.inr h)
  have z1 := z0.rename (Empty.elim : Empty → Fin 1)
  have hz : close Z = zeroOrSuccessor := by rfl
  have z2 := TheoryCertificate.closeElim Z ![x]
    (by rw [hz]; simpa only [Finset.image_empty] using z1)
  have z : TheoryCertificate false sixTheory (∅ : Context (Fin 1)) Z := by
    simpa [Z, E, x, subst_disj, exUnit_subst,
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual_subst,
      unitSubst, succ_subst, zero_subst, term_subst_relabel, Term.subst] using z2
  have pd : TheoryCertificate false sixTheory (∅ : Context (Fin 1)) D := by
    apply TheoryCertificate.impIntro
    apply TheoryCertificate.disjElim (z.weaken (Finset.empty_subset _))
    · exact TheoryCertificate.falsumElim (TheoryCertificate.negElim
        (TheoryCertificate.assumption (Finset.mem_insert_self _ _))
        (TheoryCertificate.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
    · exact TheoryCertificate.assumption (Finset.mem_insert_self _ _)
  exact TheoryCertificate.closeOneIntro D pd

/-- Replace the omitted predecessor axiom in each finite supplied proof support. -/
def Certificate.toSix {α : Type*} {Γ : Context α} {A : Formula α}
    (p : Certificate false Γ A) : TheoryCertificate false sixTheory Γ A := by
  have supply (θ : Sentence) (hθ : θ ∈ theory) :
      TheoryCertificate false sixTheory Γ (θ.rename (Empty.elim : Empty → α)) := by
    by_cases hp : θ = qPredecessor
    · subst θ
      have q := predecessorFromInduction.universeRename (Empty.elim : Empty → α)
      have q' : TheoryCertificate false sixTheory (∅ : Context α)
          (qPredecessor.rename Empty.elim) := by simpa only [Finset.image_empty] using q
      exact q'.weaken (Finset.empty_subset _)
    · apply TheoryCertificate.fromAxiom
      rcases hθ with hb | hi
      · left
        simp only [basic, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
        simp only [basicSix, Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      · exact Or.inr hi
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.TheoryProof.replace p
  intro B hB
  by_cases hΓ : B ∈ Γ
  · exact TheoryCertificate.assumption hΓ
  · have hT : B ∈ liftTheory theory α := hB.resolve_right hΓ
    let θ := Classical.choose hT
    have hθ := Classical.choose_spec hT
    exact hθ.2 ▸ supply θ hθ.1

def Certificate.ofSix {α : Type*} {Γ : Context α} {A : Formula α}
    (p : TheoryCertificate false sixTheory Γ A) : Certificate false Γ A := by
  apply p.mono
  intro θ hθ
  rcases hθ with hb | hi
  · left
    simp only [basicSix, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    simp only [basic, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · exact Or.inr hi

theorem six_consequences_iff {α : Type*} (Γ : Context α) (A : Formula α) :
    Nonempty (TheoryCertificate false sixTheory Γ A) ↔ Provable false Γ A := by
  constructor
  · rintro ⟨p⟩
    exact ⟨Certificate.ofSix p⟩
  · rintro ⟨p⟩
    exact ⟨Certificate.toSix p⟩

end
end Lemmatheca.ProofTheory.HeytingArithmetic
