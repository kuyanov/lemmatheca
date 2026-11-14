import Lemmatheca.EqualityFreeFirstOrderSequents.Operations
import Lemmatheca.HerbrandModels.HerbrandModels
import Lemmatheca.ClassicalPropositionalSequents.Calculus

/-! The weak existential fragment, exact matrix readings and actual witness data.
The propositional atoms are the existing complete relation-and-term tuples. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w w'
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}
noncomputable section
abbrev Atom := Lemmatheca.MathematicalLogic.HerbrandModels.Atom
abbrev PropNnf := Lemmatheca.ProofTheory.ClassicalPropositional.Nnf
abbrev PropProof {γ : Type*} [DecidableEq γ] (Γ : Finset (PropNnf γ)) :=
  Lemmatheca.ProofTheory.ClassicalPropositional.Proof Γ

/-- Close the newest last slots, retaining any earlier available slots. -/
def bindExists : (n : ℕ) → {m : ℕ} → Nnf L α (m+n) → Nnf L α m
  | 0, _, A => A
  | n+1, _, A => bindExists n (.ex A)

def bindForall : (n : ℕ) → {m : ℕ} → Nnf L α (m+n) → Nnf L α m
  | 0, _, A => A
  | n+1, _, A => bindForall n (.all A)

/-- The complete leading existential block, outermost slot first. -/
def existsBlock {n} (A : Nnf L α n) : Nnf L α 0 :=
  bindExists n ((Nat.zero_add n).symm ▸ A)

def forallBlock {n} (A : Nnf L α n) : Nnf L α 0 :=
  bindForall n ((Nat.zero_add n).symm ▸ A)

/-- Leading existentials may precede, but never enter, a QF binary matrix. -/
def Weak : ∀ {n}, Nnf L α n → Prop
  | _, .pos _ _ | _, .neg _ _ | _, .bot | _, .top => True
  | _, .and A B | _, .or A B => A.QuantifierFree ∧ B.QuantifierFree
  | _, .all _ => False
  | _, .ex B => Weak B

/-- Positive-length weak blocks have an outer existential constructor. -/
def ProperWeak : ∀ {n}, Nnf L α n → Prop
  | _, .ex B => Weak B
  | _, _ => False

/-- Read complete matrices on actual relation atoms, forgetting only the empty
available-slot tag. Values on quantified constructors are outside the QF domain. -/
def propositionalize : Nnf L α 0 → PropNnf (Atom L α)
  | .pos R ts => .pos ⟨_, R, fun i => (ts i).relabel (Sum.elim id Fin.elim0)⟩
  | .neg R ts => .neg ⟨_, R, fun i => (ts i).relabel (Sum.elim id Fin.elim0)⟩
  | .bot => .bot
  | .top => .top
  | .and A B => .and (propositionalize A) (propositionalize B)
  | .or A B => .or (propositionalize A) (propositionalize B)
  | .all _ | .ex _ => .bot

/-- Reinsert each recorded atom as the same relation application. -/
def embed : PropNnf (Atom L α) → Nnf L α 0
  | .pos a => .pos a.relation (fun i => (a.terms i).relabel Sum.inl)
  | .neg a => .neg a.relation (fun i => (a.terms i).relabel Sum.inl)
  | .bot => .bot
  | .top => .top
  | .and A B => .and (embed A) (embed B)
  | .or A B => .or (embed A) (embed B)

def readContext (Γ : Sequent L α) : Finset (PropNnf (Atom L α)) := Γ.image propositionalize

def embedContext (Γ : Finset (PropNnf (Atom L α))) : Sequent L α := Γ.image embed

def ContextQF (Γ : Sequent L α) : Prop := ∀ A ∈ Γ, A.QuantifierFree

def ContextProper (Γ : Sequent L α) : Prop := ∀ A ∈ Γ, ProperWeak A

/-- A terminal matrix or an actual existential choice followed by its remaining record. -/
inductive Witness : Nnf L α 0 → Type max u v w
  | terminal (A : Nnf L α 0) : A.QuantifierFree → Witness A
  | step (B : Nnf L α 1) (t : L.Term α) : Witness (B.instantiate t) → Witness (.ex B)

def Witness.value : {F : Nnf L α 0} → Witness F → Nnf L α 0
  | _, .terminal A _ => A
  | _, .step _ _ w => w.value

/-- The stored witness terms in their actual outermost-first order. -/
def Witness.terms : {F : Nnf L α 0} → Witness F → List (L.Term α)
  | _, .terminal _ _ => []
  | _, .step _ t w => t :: w.terms

/-- The exact originating endformula and its stored witness choices. -/
structure OriginWitness (Λ : Sequent L α) where
  origin : Nnf L α 0
  member : origin ∈ Λ
  witness : Witness origin

def values {Λ : Sequent L α} (ws : List (OriginWitness Λ)) : Sequent L α :=
  (ws.map (fun w => w.witness.value)).toFinset

/-- Actual factor data; fixed matrices and existential origins remain separate. -/
structure ExtractionResult (Δ Λ : Sequent L α) where
  fixed_qf : ContextQF Δ
  origins_proper : ContextProper Λ
  witnesses : List (OriginWitness Λ)
  factor : PropProof (readContext Δ ∪ readContext (values witnesses))

/-- A nonempty actual tuple list and an existing five-rule propositional proof. -/
structure Certificate {n} (A : Nnf L α n) where
  matrix_qf : A.QuantifierFree
  tuples : List (Fin n → L.Term α)
  nonempty : tuples ≠ []
  factor : PropProof ((tuples.map (fun ts => propositionalize (A.instantiateSlots ts))).toFinset)

/-- List disjunction has the explicitly stated final bottom convention. -/
def disjunction {γ : Type*} : List (PropNnf γ) → PropNnf γ
  | [] => .bot
  | A :: xs => .or A (disjunction xs)

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
