import Lemmatheca.EqualityFreeFirstOrderSequentSubstitution.Transformations

/-! The actual eight-constructor extension of the equality-free one-sided
calculus. Both parameter-changing primitives also have cutful children. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section

/-- All seven primitive constructors, and the split-context cut constructor. -/
inductive CutProof (L : Language.{u,v}) : {α : Type w} → Sequent L α → Type max u v (w+1)
  | identity {α Γ k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin 0)) :
      Nnf.pos R ts ∈ Γ → Nnf.neg R ts ∈ Γ → CutProof L Γ
  | truth {α Γ} : Nnf.top ∈ Γ → CutProof L (α := α) Γ
  | andIntro {α Γ A B} : CutProof L (α := α) (insert A Γ) →
      CutProof L (insert B Γ) → CutProof L (insert (.and A B) Γ)
  | orIntro {α Γ A B} : CutProof L (α := α) (insert A (insert B Γ)) →
      CutProof L (insert (.or A B) Γ)
  | botIntro {α Γ} : CutProof L (α := α) Γ → CutProof L (insert .bot Γ)
  | allIntro {α Γ} (A : Nnf L α 1) :
      CutProof L (insert A.toFormula (liftContext Γ)) → CutProof L (insert (.all A) Γ)
  | exIntro {α Γ} (A : Nnf L α 1) (t : L.Term α) :
      CutProof L (insert (A.instantiate t) Γ) → CutProof L (insert (.ex A) Γ)
  | cut {α Γ Δ} (A : Nnf L α 0) : CutProof L (insert A Γ) →
      CutProof L (insert A.dual Δ) → CutProof L (Γ ∪ Δ)

/-- The same countable reserve as the cut-free public calculus. -/
abbrev CutCertificate (Γ : Sequent L α) :=
  CutProof L (renameContext Γ (Sum.inl : α → α ⊕ ℕ))

def CutDerives (Γ : Sequent L α) : Prop := Nonempty (CutCertificate Γ)

/-- Copy each actual primitive node into the enlarged family. -/
def CutProof.ofCore {Γ : Sequent L α} (p : CoreProof L Γ) : CutProof L Γ := by
  induction p with
  | identity R ts hp hn => exact .identity R ts hp hn
  | truth ht => exact .truth ht
  | andIntro _ _ ihP ihQ => exact .andIntro ihP ihQ
  | orIntro _ ih => exact .orIntro ih
  | botIntro _ ih => exact .botIntro ih
  | allIntro B _ ih => exact .allIntro B ih
  | exIntro B t _ ih => exact .exIntro B t ih

/-- Rebuild all eight constructors in a larger target context. -/
def CutProof.weaken {Γ Δ : Sequent L α} (p : CutProof L Γ) (h : Γ ⊆ Δ) :
    CutProof L Δ := by
  induction p with
  | identity R ts hp hn => exact .identity R ts (h hp) (h hn)
  | truth ht => exact .truth (h ht)
  | @andIntro α Γ A B p q ihP ihQ =>
      have hs : Γ ⊆ Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have r := CutProof.andIntro (ihP (Finset.insert_subset_insert A hs))
        (ihQ (Finset.insert_subset_insert B hs))
      exact (Finset.insert_eq_of_mem (h (Finset.mem_insert_self _ _))) ▸ r
  | @orIntro α Γ A B p ih =>
      have hs : Γ ⊆ Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have r := CutProof.orIntro
        (ih (Finset.insert_subset_insert A (Finset.insert_subset_insert B hs)))
      exact (Finset.insert_eq_of_mem (h (Finset.mem_insert_self _ _))) ▸ r
  | @botIntro α Γ p ih =>
      have r := CutProof.botIntro (ih (fun _ hm => h (Finset.mem_insert_of_mem hm)))
      exact (Finset.insert_eq_of_mem (h (Finset.mem_insert_self _ _))) ▸ r
  | @allIntro α Γ B p ih =>
      have hs : Γ ⊆ Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have r := CutProof.allIntro B (ih
        (Finset.insert_subset_insert _ (Finset.image_subset_image hs)))
      exact (Finset.insert_eq_of_mem (h (Finset.mem_insert_self _ _))) ▸ r
  | @exIntro α Γ B t p ih =>
      have hs : Γ ⊆ Δ := fun _ hm => h (Finset.mem_insert_of_mem hm)
      have r := CutProof.exIntro B t (ih (Finset.insert_subset_insert _ hs))
      exact (Finset.insert_eq_of_mem (h (Finset.mem_insert_self _ _))) ▸ r
  | @cut α Γ Ξ A p q ihP ihQ =>
      have hp : Γ ⊆ Δ := fun _ hm => h (Finset.mem_union_left _ hm)
      have hq : Ξ ⊆ Δ := fun _ hm => h (Finset.mem_union_right _ hm)
      simpa only [Finset.union_self] using CutProof.cut A
        (ihP (Finset.insert_subset_insert A hp))
        (ihQ (Finset.insert_subset_insert A.dual hq))

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder
