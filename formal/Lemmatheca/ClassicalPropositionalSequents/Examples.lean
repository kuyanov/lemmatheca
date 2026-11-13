import Lemmatheca.ClassicalPropositionalSequents.Properties

namespace Lemmatheca.Entry.ClassicalPropositionalSequents

open Lemmatheca.ProofTheory.ClassicalPropositional

variable {α : Type*} [DecidableEq α]

theorem conjunction_exchange (A B : Nnf α) :
    Derives {(Nnf.and A B).dual, .and B A} := by
  rcases identity_expansion A with ⟨pa⟩
  rcases identity_expansion B with ⟨pb⟩
  have qa : Proof (insert A {A.dual, B.dual}) := pa.weaken (by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
    rcases hC with rfl | rfl <;> simp)
  have qb : Proof (insert B {A.dual, B.dual}) := pb.weaken (by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
    rcases hC with rfl | rfl <;> simp)
  have r : Proof (insert A.dual (insert B.dual {Nnf.and B A})) := by
    have hs : (insert (Nnf.and B A) {A.dual, B.dual} : Sequent α) =
        insert A.dual (insert B.dual {Nnf.and B A}) := by
      ext C
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
    exact hs ▸ Proof.andIntro qb qa
  exact ⟨by simpa [Nnf.dual, Finset.insert_comm, Finset.pair_comm] using Proof.orIntro r⟩

theorem atom_excluded_middle (p : α) : Derives {Nnf.or (.pos p) (.neg p)} := by
  have h : Proof (insert (Nnf.pos p) (insert (Nnf.neg p) ∅)) :=
    .identity p (by simp) (by simp)
  exact ⟨by simpa using Proof.orIntro h⟩

theorem atom_not_derivable (p : α) : ¬ Derives {Nnf.pos p} := by
  rintro ⟨proof⟩
  have h := proof.sound (fun _ => false)
  simp [SatisfiesSequent, Nnf.eval] at h

end Lemmatheca.Entry.ClassicalPropositionalSequents
