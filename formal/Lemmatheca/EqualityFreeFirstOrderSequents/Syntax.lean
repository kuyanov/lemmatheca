import Lemmatheca.FirstOrderProofFormulas.Classical

/-! Equality-free signed normal formulas. Terms and full formula readings use the
existing language, scoped terms and primitive full syntax; only the NNF view is new. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w w' w'' z

abbrev Full (L : Language.{u,v}) (α : Type w) (n : ℕ) :=
  Lemmatheca.ProofTheory.FirstOrder.BoundedFormula L α n

/-- An equality-free signed view with explicitly scoped quantified bodies. -/
inductive Nnf (L : Language.{u,v}) (α : Type w) : ℕ → Type max u v w
  | pos {n k} : L.Relations k → (Fin k → L.Term (α ⊕ Fin n)) → Nnf L α n
  | neg {n k} : L.Relations k → (Fin k → L.Term (α ⊕ Fin n)) → Nnf L α n
  | bot {n} : Nnf L α n
  | top {n} : Nnf L α n
  | and {n} : Nnf L α n → Nnf L α n → Nnf L α n
  | or {n} : Nnf L α n → Nnf L α n → Nnf L α n
  | all {n} : Nnf L α (n+1) → Nnf L α n
  | ex {n} : Nnf L α (n+1) → Nnf L α n

noncomputable instance instDecidableEqNnf (L : Language.{u,v}) (α : Type w) (n : ℕ) :
    DecidableEq (Nnf L α n) := Classical.decEq _

namespace Nnf
variable {L : Language.{u,v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- Classical negation expressed by reversing the signed normal tree. -/
def dual : ∀ {n}, Nnf L α n → Nnf L α n
  | _, .pos R ts => .neg R ts
  | _, .neg R ts => .pos R ts
  | _, .bot => .top
  | _, .top => .bot
  | _, .and A B => .or A.dual B.dual
  | _, .or A B => .and A.dual B.dual
  | _, .all A => .ex A.dual
  | _, .ex A => .all A.dual

/-- Logical rank is independent of the size of terms and literal signs. -/
def rank : ∀ {n}, Nnf L α n → ℕ
  | _, .pos _ _ | _, .neg _ _ | _, .bot | _, .top => 0
  | _, .and A B | _, .or A B => max A.rank B.rank + 1
  | _, .all A | _, .ex A => A.rank + 1

/-- The actual primitive full formula read from a signed tree. -/
def read : ∀ {n}, Nnf L α n → Full L α n
  | _, .pos R ts => .rel R ts
  | _, .neg R ts => .neg (.rel R ts)
  | _, .bot => .falsum
  | _, .top => .neg .falsum
  | _, .and A B => .conj A.read B.read
  | _, .or A B => .disj A.read B.read
  | _, .all A => .all A.read
  | _, .ex A => .ex A.read

/-- The finite free support of the full reading. -/
def freeVarFinset [DecidableEq α] {n} (A : Nnf L α n) : Finset α := A.read.freeVarFinset

/-- Absence of both quantified signed constructors. -/
def QuantifierFree {n} (A : Nnf L α n) : Prop := A.read.QuantifierFree

/-- Capture-free action of the shared all-variable scope substitution. -/
def map : ∀ {n m}, Nnf L α n →
    Lemmatheca.ProofTheory.FirstOrder.ScopeSubst L α β n m → Nnf L β m
  | _, _, .pos R ts, σ => .pos R (fun i => (ts i).subst σ)
  | _, _, .neg R ts, σ => .neg R (fun i => (ts i).subst σ)
  | _, _, .bot, _ => .bot
  | _, _, .top, _ => .top
  | _, _, .and A B, σ => .and (A.map σ) (B.map σ)
  | _, _, .or A B, σ => .or (A.map σ) (B.map σ)
  | _, _, .all A, σ => .all (A.map (Lemmatheca.ProofTheory.FirstOrder.liftScope σ))
  | _, _, .ex A, σ => .ex (A.map (Lemmatheca.ProofTheory.FirstOrder.liftScope σ))

def subst {n} (A : Nnf L α n) (σ : α → L.Term β) : Nnf L β n :=
  A.map (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope σ n)

def rename {n} (A : Nnf L α n) (f : α → β) : Nnf L β n := A.subst (fun x => .var (f x))

/-- Open all currently available slots as tagged free parameters. -/
def toFormula {n} (A : Nnf L α n) : Nnf L (α ⊕ Fin n) 0 :=
  A.map (fun x => .var (.inl x))

def instantiateSlots {n} (A : Nnf L α n) (ts : Fin n → L.Term α) : Nnf L α 0 :=
  A.map (Sum.elim (fun x => .var (.inl x)) (fun i => (ts i).relabel Sum.inl))

def instantiate (A : Nnf L α 1) (t : L.Term α) : Nnf L α 0 := A.instantiateSlots (fun _ => t)

/-- Positive/negative normalization of actual equality-free full formulas. -/
def normalize : ∀ {n} (A : Full L α n), A.EqualityFree → Bool → Nnf L α n
  | _, .falsum, _, true => .bot
  | _, .falsum, _, false => .top
  | _, .equal _ _, h, _ => False.elim h
  | _, .rel R ts, _, true => .pos R ts
  | _, .rel R ts, _, false => .neg R ts
  | _, .neg A, h, b => normalize A h (!b)
  | _, .conj A B, h, true => .and (normalize A h.1 true) (normalize B h.2 true)
  | _, .conj A B, h, false => .or (normalize A h.1 false) (normalize B h.2 false)
  | _, .disj A B, h, true => .or (normalize A h.1 true) (normalize B h.2 true)
  | _, .disj A B, h, false => .and (normalize A h.1 false) (normalize B h.2 false)
  | _, .impl A B, h, true => .or (normalize A h.1 false) (normalize B h.2 true)
  | _, .impl A B, h, false => .and (normalize A h.1 true) (normalize B h.2 false)
  | _, .all A, h, true => .all (normalize A h true)
  | _, .all A, h, false => .ex (normalize A h false)
  | _, .ex A, h, true => .ex (normalize A h true)
  | _, .ex A, h, false => .all (normalize A h false)

/-- Classical signed interpretation on the shared full reading. -/
def realize {M : Type*} [L.Structure M] {n} (A : Nnf L α n)
    (a : α ⊕ Fin n → M) : Prop := A.read.realize a

/-- Classical interpretation of a complete signed formula. -/
def Realize {M : Type*} [L.Structure M] (A : Nnf L α 0) (a : α → M) : Prop :=
  A.realize (Sum.elim a Fin.elim0)

end Nnf

/-- An equality-free full formula in the actual primitive syntax. -/
abbrev EqualityFreeFormula (L : Language.{u,v}) (α : Type w) :=
  {A : Full L α 0 // A.EqualityFree}

abbrev Sequent (L : Language.{u,v}) (α : Type w) := Finset (Nnf L α 0)

/-- Free renaming of a finite sequent. -/
noncomputable def renameContext {L : Language.{u,v}} {α : Type w} {β : Type w'}
    (Γ : Sequent L α) (f : α → β) : Sequent L β := Γ.image (fun A => A.rename f)

/-- Lift the side context through a newly tagged eigenparameter. -/
noncomputable def liftContext {L : Language.{u,v}} {α : Type w} (Γ : Sequent L α) :
    Sequent L (α ⊕ Fin 1) := renameContext Γ Sum.inl

/-- A sequent is true when one of its finitely many alternatives is true. -/
def SatisfiesSequent {L : Language.{u,v}} {α : Type w} {M : Type*} [L.Structure M]
    (Γ : Sequent L α) (a : α → M) : Prop := ∃ A ∈ Γ, A.Realize a

/-- Validity in nonempty structures, at all assignments. -/
def Valid {L : Language.{u,v}} {α : Type w} (Γ : Sequent L α) : Prop :=
  ∀ (M : Type z) [L.Structure M] [Nonempty M], ∀ a : α → M, SatisfiesSequent Γ a

/-- Negate the full premises and retain the positive full conclusions. -/
noncomputable def encode {L : Language.{u,v}} {α : Type w}
    (Λ Δ : Finset (EqualityFreeFormula L α)) : Sequent L α :=
  Λ.image (fun F => Nnf.normalize F.val F.property false) ∪
    Δ.image (fun F => Nnf.normalize F.val F.property true)

end Lemmatheca.ProofTheory.ClassicalFirstOrder
