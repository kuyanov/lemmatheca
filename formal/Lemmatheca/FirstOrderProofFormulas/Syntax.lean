import Lemmatheca.FirstOrderProofs.FirstOrderProofSyntax
import Mathlib.ModelTheory.Complexity

/-! Full connective-sensitive syntax, sharing the corpus language and term trees.
Available bound slots are indexed from the outside; a binder adds a newest last slot. -/
namespace Lemmatheca.ProofTheory.FirstOrder

open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w w' w''

/-- Full scoped first-order formula trees with all constructive connectives primitive. -/
inductive BoundedFormula (L : Language.{u, v}) (α : Type w) : ℕ → Type max u v w
  | falsum {n} : BoundedFormula L α n
  | equal {n} : L.Term (α ⊕ Fin n) → L.Term (α ⊕ Fin n) → BoundedFormula L α n
  | rel {n k} : L.Relations k → (Fin k → L.Term (α ⊕ Fin n)) → BoundedFormula L α n
  | neg {n} : BoundedFormula L α n → BoundedFormula L α n
  | conj {n} : BoundedFormula L α n → BoundedFormula L α n → BoundedFormula L α n
  | disj {n} : BoundedFormula L α n → BoundedFormula L α n → BoundedFormula L α n
  | impl {n} : BoundedFormula L α n → BoundedFormula L α n → BoundedFormula L α n
  | all {n} : BoundedFormula L α (n + 1) → BoundedFormula L α n
  | ex {n} : BoundedFormula L α (n + 1) → BoundedFormula L α n

/-- Full formulas with no externally available bound slot. -/
abbrev Formula (L : Language.{u, v}) (α : Type w) := BoundedFormula L α 0

namespace BoundedFormula
variable {L : Language.{u,v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- Logical depth counts formula constructors rather than term depth. -/
def depth : ∀ {n}, BoundedFormula L α n → ℕ
  | _, .falsum | _, .equal _ _ | _, .rel _ _ => 0
  | _, .neg A | _, .all A | _, .ex A => A.depth + 1
  | _, .conj A B | _, .disj A B | _, .impl A B => max A.depth B.depth + 1

/-- Absence of logical equality occurrences in the full tree. -/
def EqualityFree : ∀ {n}, BoundedFormula L α n → Prop
  | _, .falsum | _, .rel _ _ => True
  | _, .equal _ _ => False
  | _, .neg A | _, .all A | _, .ex A => A.EqualityFree
  | _, .conj A B | _, .disj A B | _, .impl A B => A.EqualityFree ∧ B.EqualityFree

/-- Absence of both quantifier constructors in the full tree. -/
def QuantifierFree : ∀ {n}, BoundedFormula L α n → Prop
  | _, .falsum | _, .rel _ _ | _, .equal _ _ => True
  | _, .neg A => A.QuantifierFree
  | _, .conj A B | _, .disj A B | _, .impl A B => A.QuantifierFree ∧ B.QuantifierFree
  | _, .all _ | _, .ex _ => False

/-- Finite support of free parameters; available placeholders are not free names. -/
def freeVarFinset [DecidableEq α] : ∀ {n}, BoundedFormula L α n → Finset α
  | _, .falsum => ∅
  | _, .equal s t => s.varFinsetLeft ∪ t.varFinsetLeft
  | _, .rel _ ts => Finset.univ.biUnion fun i => (ts i).varFinsetLeft
  | _, .neg A | _, .all A | _, .ex A => A.freeVarFinset
  | _, .conj A B | _, .disj A B | _, .impl A B => A.freeVarFinset ∪ B.freeVarFinset

end BoundedFormula

/-- Substitution for every free or currently available bound variable. -/
abbrev ScopeSubst (L : Language.{u,v}) (α : Type w) (β : Type w') (n m : ℕ) :=
  α ⊕ Fin n → L.Term (β ⊕ Fin m)

/-- Include every old variable while adding one newest bound slot. -/
def scopeInclusion {α : Type w} (n : ℕ) : α ⊕ Fin n → α ⊕ Fin (n+1) :=
  Sum.map id Fin.castSucc

/-- Extend a scope substitution under a binder, protecting its newest slot. -/
def liftScope {n m : ℕ} (σ : ScopeSubst L α β n m) : ScopeSubst L α β (n+1) (m+1) :=
  Sum.elim (fun x => (σ (.inl x)).relabel (scopeInclusion m))
    (Fin.lastCases (.var (.inr (Fin.last m)))
      (fun i => (σ (.inr i)).relabel (scopeInclusion m)))

namespace BoundedFormula
variable {L : Language.{u,v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- Capture-free substitution of all available variables, lifted under each binder. -/
def map : ∀ {n m}, BoundedFormula L α n → ScopeSubst L α β n m → BoundedFormula L β m
  | _, _, .falsum, _ => .falsum
  | _, _, .equal s t, σ => .equal (s.subst σ) (t.subst σ)
  | _, _, .rel R ts, σ => .rel R (fun i => (ts i).subst σ)
  | _, _, .neg A, σ => .neg (A.map σ)
  | _, _, .conj A B, σ => .conj (A.map σ) (B.map σ)
  | _, _, .disj A B, σ => .disj (A.map σ) (B.map σ)
  | _, _, .impl A B, σ => .impl (A.map σ) (B.map σ)
  | _, _, .all A, σ => .all (A.map (liftScope σ))
  | _, _, .ex A, σ => .ex (A.map (liftScope σ))

/-- A free substitution fixes all currently available placeholders. -/
def freeScope (σ : α → L.Term β) (n : ℕ) : ScopeSubst L α β n n :=
  Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))

/-- Substitute free parameters by terms, retaining the bound scope. -/
def subst {n} (A : BoundedFormula L α n) (σ : α → L.Term β) : BoundedFormula L β n :=
  A.map (freeScope σ n)

/-- Rename free parameters, retaining the bound scope. -/
def rename {n} (A : BoundedFormula L α n) (f : α → β) : BoundedFormula L β n :=
  A.subst (fun x => .var (f x))

/-- Open every available slot as a separately tagged free parameter. -/
def toFormula {n} (A : BoundedFormula L α n) : Formula L (α ⊕ Fin n) :=
  A.map (fun v => .var (.inl v))

/-- Instantiate all available slots simultaneously with complete terms. -/
def instantiateSlots {n} (A : BoundedFormula L α n) (ts : Fin n → L.Term α) : Formula L α :=
  A.map (Sum.elim (fun x => .var (.inl x)) (fun i => (ts i).relabel Sum.inl))

/-- Open the unique available slot at the supplied term. -/
def instantiate (A : BoundedFormula L α 1) (t : L.Term α) : Formula L α :=
  A.instantiateSlots (fun _ => t)

/-- Translate every full connective to the corpus's existing classical abbreviation. -/
def toClassical : ∀ {n}, BoundedFormula L α n → L.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal s t => .equal s t
  | _, .rel R ts => .rel R ts
  | _, .neg A => A.toClassical.not
  | _, .conj A B => A.toClassical ⊓ B.toClassical
  | _, .disj A B => A.toClassical ⊔ B.toClassical
  | _, .impl A B => A.toClassical.imp B.toClassical
  | _, .all A => A.toClassical.all
  | _, .ex A => A.toClassical.ex

/-- Include the five primitive constructors of the existing classical syntax. -/
def ofClassical : ∀ {n}, L.BoundedFormula α n → BoundedFormula L α n
  | _, .falsum => .falsum
  | _, .equal s t => .equal s t
  | _, .rel R ts => .rel R ts
  | _, .imp A B => .impl (ofClassical A) (ofClassical B)
  | _, .all A => .all (ofClassical A)

end BoundedFormula

/-- The same capture-free all-variable substitution on the small classical alphabet. -/
def classicalMap : ∀ {n m}, L.BoundedFormula α n → ScopeSubst L α β n m →
    L.BoundedFormula β m
  | _, _, .falsum, _ => .falsum
  | _, _, .equal s t, σ => .equal (s.subst σ) (t.subst σ)
  | _, _, .rel R ts, σ => .rel R (fun i => (ts i).subst σ)
  | _, _, .imp A B, σ => .imp (classicalMap A σ) (classicalMap B σ)
  | _, _, .all A, σ => .all (classicalMap A (liftScope σ))

/-- Extend a combined assignment by a value for the newest bound slot. -/
def extendAssignment {M : Type*} {n : ℕ} (a : α ⊕ Fin n → M) (x : M) :
    α ⊕ Fin (n+1) → M :=
  Sum.elim (fun y => a (.inl y)) (Fin.lastCases x (fun i => a (.inr i)))

namespace BoundedFormula
variable {L : Language.{u,v}} {α : Type w} {M : Type*} [L.Structure M]

/-- Classical interpretation of the full primitive constructors. -/
def realize : ∀ {n}, BoundedFormula L α n → (α ⊕ Fin n → M) → Prop
  | _, .falsum, _ => False
  | _, .equal s t, a => s.realize a = t.realize a
  | _, .rel R ts, a => Structure.RelMap R (fun i => (ts i).realize a)
  | _, .neg A, a => ¬A.realize a
  | _, .conj A B, a => A.realize a ∧ B.realize a
  | _, .disj A B, a => A.realize a ∨ B.realize a
  | _, .impl A B, a => A.realize a → B.realize a
  | _, .all A, a => ∀ x, A.realize (extendAssignment a x)
  | _, .ex A, a => ∃ x, A.realize (extendAssignment a x)

/-- Separate free-name and bound-slot assignments, matching the existing syntax. -/
def Realize {n} (A : BoundedFormula L α n) (a : α → M) (b : Fin n → M) : Prop :=
  A.realize (Sum.elim a b)

end BoundedFormula
end Lemmatheca.ProofTheory.FirstOrder
