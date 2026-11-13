import Lemmatheca.ClassicalPropositionalSequents.Syntax

/-! Actual finite proof trees for the five-rule one-sided calculus. -/

namespace Lemmatheca.ProofTheory.ClassicalPropositional

universe u
variable {α : Type u} [DecidableEq α]

/-- A finite proof certificate; it contains only the five stated primitive rules. -/
inductive Proof : Sequent α → Type u
  | identity {Γ} (p : α) : Nnf.pos p ∈ Γ → Nnf.neg p ∈ Γ → Proof Γ
  | truth {Γ} : Nnf.top ∈ Γ → Proof Γ
  | andIntro {Γ A B} : Proof (insert A Γ) → Proof (insert B Γ) →
      Proof (insert (.and A B) Γ)
  | orIntro {Γ A B} : Proof (insert A (insert B Γ)) → Proof (insert (.or A B) Γ)
  | botIntro {Γ} : Proof Γ → Proof (insert .bot Γ)

/-- A derivation exists exactly when a finite primitive-rule certificate exists. -/
def Derives (Γ : Sequent α) : Prop := Nonempty (Proof Γ)

namespace Proof

/-- Maximum number of inferences on a branch; leaves have height zero. -/
def height : {Γ : Sequent α} → Proof Γ → ℕ
  | _, .identity _ _ _ | _, .truth _ => 0
  | _, .andIntro a b => max a.height b.height + 1
  | _, .orIntro a => a.height + 1
  | _, .botIntro a => a.height + 1

/-- Add the same alternatives to the context at every node of the actual proof. -/
def addContext (Θ : Sequent α) : {Γ : Sequent α} → Proof Γ → Proof (Γ ∪ Θ)
  | _, .identity p hp hn =>
      .identity p (Finset.mem_union_left _ hp) (Finset.mem_union_left _ hn)
  | _, .truth ht => .truth (Finset.mem_union_left _ ht)
  | _, @andIntro _ _ Γ A B pa pb => by
      have ha : Proof (insert A (Γ ∪ Θ)) := by
        simpa only [Finset.insert_union] using addContext Θ pa
      have hb : Proof (insert B (Γ ∪ Θ)) := by
        simpa only [Finset.insert_union] using addContext Θ pb
      simpa only [Finset.insert_union] using Proof.andIntro ha hb
  | _, @orIntro _ _ Γ A B pa => by
      have ha : Proof (insert A (insert B (Γ ∪ Θ))) := by
        simpa only [Finset.insert_union] using addContext Θ pa
      simpa only [Finset.insert_union] using Proof.orIntro ha
  | _, @botIntro _ _ Γ pa => by
      simpa only [Finset.insert_union] using Proof.botIntro (addContext Θ pa)

end Proof

end Lemmatheca.ProofTheory.ClassicalPropositional
