import Lemmatheca.EqualityFreeFirstOrderSequents.Operations

/-! The seven primitive rules as finite Type-valued certificates, with tagged
fresh parameters and a separate reserve for names absent from the endsequent. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}}

/-- Actual raw trees with no cut or weakening constructor. -/
inductive CoreProof (L : Language.{u,v}) : {α : Type w} → Sequent L α → Type max u v (w+1)
  | identity {α Γ k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0)) :
      Nnf.pos R ts ∈ Γ → Nnf.neg R ts ∈ Γ → CoreProof L Γ
  | truth {α Γ} : Nnf.top ∈ Γ → CoreProof L (α := α) Γ
  | andIntro {α Γ A B} : CoreProof L (α := α) (insert A Γ) →
      CoreProof L (insert B Γ) → CoreProof L (insert (.and A B) Γ)
  | orIntro {α Γ A B} : CoreProof L (α := α) (insert A (insert B Γ)) →
      CoreProof L (insert (.or A B) Γ)
  | botIntro {α Γ} : CoreProof L (α := α) Γ → CoreProof L (insert .bot Γ)
  | allIntro {α Γ} (A : Nnf L α 1) :
      CoreProof L (insert A.toFormula (liftContext Γ)) → CoreProof L (insert (.all A) Γ)
  | exIntro {α Γ} (A : Nnf L α 1) (t : L.Term α) :
      CoreProof L (insert (A.instantiate t) Γ) → CoreProof L (insert (.ex A) Γ)

/-- The height of the actual raw tree; fresh-parameter branches are still finite. -/
noncomputable def CoreProof.height : {α : Type w} → {Γ : Sequent L α} → CoreProof L Γ → ℕ
  | _, _, .identity _ _ _ _ | _, _, .truth _ => 0
  | _, _, .andIntro p q => max p.height q.height + 1
  | _, _, .orIntro p | _, _, .botIntro p | _, _, .allIntro _ p | _, _, .exIntro _ _ p =>
      p.height + 1

/-- A public certificate reserves countably many auxiliary free names, all absent
from its displayed concluding sequent. -/
abbrev Proof {α : Type w} (Γ : Sequent L α) :=
  CoreProof L (renameContext Γ (Sum.inl : α → α ⊕ ℕ))

/-- Derivability means existence of the specified finite certificate. -/
def Derives {α : Type w} (Γ : Sequent L α) : Prop := Nonempty (Proof Γ)

end Lemmatheca.ProofTheory.ClassicalFirstOrder
