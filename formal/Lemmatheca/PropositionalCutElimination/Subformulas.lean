import Lemmatheca.PropositionalCutElimination.Transformations

namespace Lemmatheca.ProofTheory.ClassicalPropositional

universe u
variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
/-- Following one subformula route and then another is still a subformula route. -/
theorem Nnf.Subformula.trans {A B C : Nnf α}
    (hAB : A.Subformula B) (hBC : B.Subformula C) : A.Subformula C := by
  induction hBC with
  | refl => exact hAB
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih

/-- Every formula occurring anywhere in a primitive tree lies inside an end formula. -/
theorem Proof.subformula_property {Γ : Sequent α} (p : Proof Γ)
    {A : Nnf α} (hA : A ∈ p.occurrences) : ∃ B ∈ Γ, A.Subformula B := by
  induction p with
  | identity _ _ _ => exact ⟨A, hA, .refl A⟩
  | truth _ => exact ⟨A, hA, .refl A⟩
  | @andIntro Γ B C pa pb ihA ihB =>
      simp only [Proof.occurrences, Finset.mem_union] at hA
      rcases hA with (hA | hA) | hA
      · exact ⟨A, hA, .refl A⟩
      · rcases ihA hA with ⟨D, hD, hAD⟩
        rcases Finset.mem_insert.mp hD with hDB | hD
        · subst D
          exact ⟨.and B C, by simp, .andLeft hAD⟩
        · exact ⟨D, Finset.mem_insert_of_mem hD, hAD⟩
      · rcases ihB hA with ⟨D, hD, hAD⟩
        rcases Finset.mem_insert.mp hD with hDB | hD
        · subst D
          exact ⟨.and B C, by simp, .andRight hAD⟩
        · exact ⟨D, Finset.mem_insert_of_mem hD, hAD⟩
  | @orIntro Γ B C pa ih =>
      simp only [Proof.occurrences, Finset.mem_union] at hA
      rcases hA with hA | hA
      · exact ⟨A, hA, .refl A⟩
      · rcases ih hA with ⟨D, hD, hAD⟩
        rcases Finset.mem_insert.mp hD with hDB | hD
        · subst D
          exact ⟨.or B C, by simp, .orLeft hAD⟩
        · rcases Finset.mem_insert.mp hD with hDC | hD
          · subst D
            exact ⟨.or B C, by simp, .orRight hAD⟩
          · exact ⟨D, Finset.mem_insert_of_mem hD, hAD⟩
  | @botIntro Γ pa ih =>
      simp only [Proof.occurrences, Finset.mem_union] at hA
      rcases hA with hA | hA
      · exact ⟨A, hA, .refl A⟩
      · rcases ih hA with ⟨D, hD, hAD⟩
        exact ⟨D, Finset.mem_insert_of_mem hD, hAD⟩

/-- Elimination supplies an actual analytic proof of the original concluding sequent. -/
theorem CutProof.eliminate_analytic {Γ : Sequent α} (p : CutProof Γ)
    {A : Nnf α} (hA : A ∈ p.eliminate.occurrences) : ∃ B ∈ Γ, A.Subformula B := by
  exact p.eliminate.subformula_property hA

private theorem primitive_end_nonempty {Γ : Sequent α} (p : Proof Γ) : Γ.Nonempty := by
  cases p with
  | identity q hq _ => exact ⟨.pos q, hq⟩
  | truth ht => exact ⟨.top, ht⟩
  | @andIntro Γ B C _ _ => exact ⟨.and B C, by simp⟩
  | @orIntro Γ B C _ => exact ⟨.or B C, by simp⟩
  | botIntro _ => exact ⟨.bot, by simp⟩

/-- No primitive rule can be the last inference of an empty concluding context. -/
private theorem no_empty_primitive : ¬ Derives (∅ : Sequent α) := by
  rintro ⟨p⟩
  have h := primitive_end_nonempty p
  simp at h

/-- Bottom erasure rules out a primitive derivation of the falsity singleton. -/
private theorem no_bot_primitive : ¬ Derives ({Nnf.bot} : Sequent α) := by
  rintro ⟨p⟩
  apply no_empty_primitive (α := α)
  exact ⟨by simpa using p.eraseBot⟩

/-- Cut elimination rules out an empty context in the enlarged proof system. -/
theorem no_empty_with_cut : ¬ CutDerives (∅ : Sequent α) := by
  rintro ⟨p⟩
  exact no_empty_primitive ⟨p.eliminate⟩

/-- Cut elimination rules out the falsity singleton in the enlarged proof system. -/
theorem no_bot_with_cut : ¬ CutDerives ({Nnf.bot} : Sequent α) := by
  rintro ⟨p⟩
  exact no_bot_primitive ⟨p.eliminate⟩

end Lemmatheca.ProofTheory.ClassicalPropositional
