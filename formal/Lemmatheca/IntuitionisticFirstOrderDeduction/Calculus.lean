import Lemmatheca.FirstOrderProofFormulas.Classical

/-! Native first-order natural-deduction trees. The two flags enable classical
contradiction and logical equality independently; neither structural composition
nor substitution is a primitive rule. -/
namespace Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction

open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w

abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula

noncomputable section
local instance ndFormulaDecidableEq {L : Language.{u,v}} {α : Type w} :
    DecidableEq (Formula L α) := Classical.decEq _

/-- Finite sets of allowed full formulas. -/
abbrev Context (L : Language.{u,v}) (α : Type w) := Finset (Formula L α)

/-- Lift the original assumptions, leaving one protected eigenparameter unused. -/
def liftContext {L : Language.{u,v}} {α : Type w} (Γ : Context L α) :
    Context L (α ⊕ Fin 1) := Γ.image (fun A => A.rename Sum.inl)

/-- Logical equality of complete terms, included into the empty bound scope. -/
def termEqual {L : Language.{u,v}} {α : Type w} (s t : L.Term α) : Formula L α :=
  .equal (s.relabel Sum.inl) (t.relabel Sum.inl)

/-- A finite native proof tree. The free-name type is an index, so protected
eigenparameter branches change it without changing the language. -/
inductive Derivation (classical equality : Bool) (L : Language.{u,v}) :
    {α : Type w} → Context L α → Formula L α → Type max u v (w+1)
  | assumption {α Γ A} : A ∈ Γ → Derivation classical equality L (α := α) Γ A
  | conjIntro {α Γ A B} : Derivation classical equality L (α := α) Γ A →
      Derivation classical equality L Γ B → Derivation classical equality L Γ (.conj A B)
  | conjElimLeft {α Γ A B} : Derivation classical equality L (α := α) Γ (.conj A B) →
      Derivation classical equality L Γ A
  | conjElimRight {α Γ A B} : Derivation classical equality L (α := α) Γ (.conj A B) →
      Derivation classical equality L Γ B
  | disjIntroLeft {α Γ A B} : Derivation classical equality L (α := α) Γ A →
      Derivation classical equality L Γ (.disj A B)
  | disjIntroRight {α Γ A B} : Derivation classical equality L (α := α) Γ B →
      Derivation classical equality L Γ (.disj A B)
  | disjElim {α Γ A B C} : Derivation classical equality L (α := α) Γ (.disj A B) →
      Derivation classical equality L (insert A Γ) C →
      Derivation classical equality L (insert B Γ) C → Derivation classical equality L Γ C
  | impIntro {α Γ A B} : Derivation classical equality L (α := α) (insert A Γ) B →
      Derivation classical equality L Γ (.impl A B)
  | impElim {α Γ A B} : Derivation classical equality L (α := α) Γ (.impl A B) →
      Derivation classical equality L Γ A → Derivation classical equality L Γ B
  | negIntro {α Γ A} : Derivation classical equality L (α := α) (insert A Γ) .falsum →
      Derivation classical equality L Γ (.neg A)
  | negElim {α Γ A} : Derivation classical equality L (α := α) Γ A →
      Derivation classical equality L Γ (.neg A) → Derivation classical equality L Γ .falsum
  | falsumElim {α Γ A} : Derivation classical equality L (α := α) Γ .falsum →
      Derivation classical equality L Γ A
  | classicalContradiction {α Γ A} : classical = true →
      Derivation classical equality L (α := α) (insert (.neg A) Γ) .falsum →
      Derivation classical equality L Γ A
  | allElim {α Γ} {B : BF L α 1} (t : L.Term α) :
      Derivation classical equality L (α := α) Γ (.all B) →
      Derivation classical equality L Γ (B.instantiate t)
  | exIntro {α Γ} {B : BF L α 1} (t : L.Term α) :
      Derivation classical equality L (α := α) Γ (B.instantiate t) →
      Derivation classical equality L Γ (.ex B)
  | allIntro {α Γ} {B : BF L α 1} :
      Derivation classical equality L (α := α ⊕ Fin 1) (liftContext Γ) B.toFormula →
      Derivation classical equality L (α := α) Γ (.all B)
  | exElim {α Γ C} {B : BF L α 1} : Derivation classical equality L (α := α) Γ (.ex B) →
      Derivation classical equality L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl) →
      Derivation classical equality L Γ C
  | equalIntro {α Γ} (t : L.Term α) : equality = true →
      Derivation classical equality L (α := α) Γ (termEqual t t)
  | equalElim {α Γ} (B : BF L α 1) (s t : L.Term α) : equality = true →
      Derivation classical equality L (α := α) Γ (termEqual s t) →
      Derivation classical equality L Γ (B.instantiate s) →
      Derivation classical equality L Γ (B.instantiate t)

/-- A public certificate reserves a disjoint countable supply of auxiliary names. -/
def Proof (classical equality : Bool) (L : Language.{u,v}) {α : Type w}
    (Γ : Context L α) (A : Formula L α) : Type max u v (w+1) :=
  Derivation classical equality L (Γ.image (fun B => B.rename (Sum.inl : α → α ⊕ ℕ)))
    (A.rename Sum.inl)

/-- Propositional existence of a finite certificate; the actual tree remains in `Proof`. -/
def Derives (classical equality : Bool) (L : Language.{u,v}) {α : Type w}
    (Γ : Context L α) (A : Formula L α) : Prop := Nonempty (Proof classical equality L Γ A)

/-- Arbitrary-premise certificates carry a particular finite supporting context. -/
structure TheoryProof (classical equality : Bool) (L : Language.{u,v}) {α : Type w}
    (T : Set (Formula L α)) (A : Formula L α) : Type max u v (w+1) where
  assumptions : Context L α
  allowed : ∀ B ∈ assumptions, B ∈ T
  derivation : Proof classical equality L assumptions A

/-- Arbitrary-premise consequence is existence of a finitely supported certificate. -/
def TheoryDerives (classical equality : Bool) (L : Language.{u,v}) {α : Type w}
    (T : Set (Formula L α)) (A : Formula L α) : Prop :=
  Nonempty (TheoryProof classical equality L T A)

end
end Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
