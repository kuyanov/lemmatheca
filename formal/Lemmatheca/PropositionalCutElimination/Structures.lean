import Lemmatheca.ClassicalPropositionalSequents.Calculus

/-! Formula measures, finite trees with cut, and actual formula occurrences. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional

universe u
variable {α : Type u} [DecidableEq α]

/-- Number of nodes in the signed formula's expression tree. -/
def Nnf.formulaSize : Nnf α → ℕ
  | .pos _ | .neg _ | .bot | .top => 1
  | .and A B | .or A B => A.formulaSize + B.formulaSize + 1

/-- Number of rule applications in the actual cut-free tree, counting leaves. -/
def Proof.size : {Γ : Sequent α} → Proof Γ → ℕ
  | _, .identity _ _ _ | _, .truth _ => 1
  | _, .andIntro a b => a.size + b.size + 1
  | _, .orIntro a | _, .botIntro a => a.size + 1

/-- The same primitive rule system, with the displayed cut rule also permitted. -/
inductive CutProof : Sequent α → Type u
  | identity {Γ} (p : α) : Nnf.pos p ∈ Γ → Nnf.neg p ∈ Γ → CutProof Γ
  | truth {Γ} : Nnf.top ∈ Γ → CutProof Γ
  | andIntro {Γ A B} : CutProof (insert A Γ) → CutProof (insert B Γ) →
      CutProof (insert (.and A B) Γ)
  | orIntro {Γ A B} : CutProof (insert A (insert B Γ)) → CutProof (insert (.or A B) Γ)
  | botIntro {Γ} : CutProof Γ → CutProof (insert .bot Γ)
  | cut {Γ Δ} (A : Nnf α) : CutProof (insert A Γ) → CutProof (insert A.dual Δ) →
      CutProof (Γ ∪ Δ)

/-- Derivability in the finite six-rule proof system. -/
def CutDerives (Γ : Sequent α) : Prop := Nonempty (CutProof Γ)

/-- Count all rule applications in a finite tree that may contain cut. -/
def CutProof.size : {Γ : Sequent α} → CutProof Γ → ℕ
  | _, .identity _ _ _ | _, .truth _ => 1
  | _, .andIntro a b | _, .cut _ a b => a.size + b.size + 1
  | _, .orIntro a | _, .botIntro a => a.size + 1

/-- Embed an original primitive proof without introducing any cut. -/
def CutProof.ofProof : {Γ : Sequent α} → Proof Γ → CutProof Γ
  | _, .identity p hp hn => .identity p hp hn
  | _, .truth ht => .truth ht
  | _, .andIntro a b => .andIntro (ofProof a) (ofProof b)
  | _, .orIntro a => .orIntro (ofProof a)
  | _, .botIntro a => .botIntro (ofProof a)

/-- Structural subformula relation, including the formula itself. -/
inductive Nnf.Subformula : Nnf α → Nnf α → Prop
  | refl (A) : Subformula A A
  | andLeft {X A B} : Subformula X A → Subformula X (.and A B)
  | andRight {X A B} : Subformula X B → Subformula X (.and A B)
  | orLeft {X A B} : Subformula X A → Subformula X (.or A B)
  | orRight {X A B} : Subformula X B → Subformula X (.or A B)

/-- Every formula occurring in any context of the supplied primitive proof. -/
def Proof.occurrences : {Γ : Sequent α} → Proof Γ → Sequent α
  | Γ, .identity _ _ _ | Γ, .truth _ => Γ
  | _, @Proof.andIntro _ _ Γ A B a b =>
      insert (.and A B) Γ ∪ a.occurrences ∪ b.occurrences
  | _, @Proof.orIntro _ _ Γ A B a => insert (.or A B) Γ ∪ a.occurrences
  | _, @Proof.botIntro _ _ Γ a => insert .bot Γ ∪ a.occurrences

/-- Every formula occurring in any context of a supplied tree with cut. -/
def CutProof.occurrences : {Γ : Sequent α} → CutProof Γ → Sequent α
  | Γ, .identity _ _ _ | Γ, .truth _ => Γ
  | _, @CutProof.andIntro _ _ Γ A B a b =>
      insert (.and A B) Γ ∪ a.occurrences ∪ b.occurrences
  | _, @CutProof.cut _ _ Γ Δ _A a b => Γ ∪ Δ ∪ a.occurrences ∪ b.occurrences
  | _, @CutProof.orIntro _ _ Γ A B a => insert (.or A B) Γ ∪ a.occurrences
  | _, @CutProof.botIntro _ _ Γ a => insert .bot Γ ∪ a.occurrences

end Lemmatheca.ProofTheory.ClassicalPropositional
