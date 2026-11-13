import Lemmatheca.IntuitionisticPropositionalSequents.Calculus

/-! Syntactic derived rules and exact native-calculus translations. -/

namespace Lemmatheca.ProofTheory.Intuitionistic.SequentCalculus

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

private theorem cut_same {Γ : Finset (PropFormula α)} {A C : PropFormula α}
    (hA : Derives Γ A) (hC : Derives (insert A Γ) C) : Derives Γ C := by
  simpa only [Finset.union_self] using (Derives.cut hA hC)

/-- The conjunction projections are derived using conjunction-left and cut. -/
theorem Derives.conj_elim_left {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (h : Derives Γ (conj A B)) : Derives Γ A := by
  apply cut_same h
  exact Derives.conjLeft (.identity (by simp))

theorem Derives.conj_elim_right {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (h : Derives Γ (conj A B)) : Derives Γ B := by
  apply cut_same h
  exact Derives.conjLeft (.identity (by simp))

/-- Modus ponens is a derived operation, rather than a sequent constructor. -/
theorem Derives.impl_elim {Γ : Finset (PropFormula α)} {A B : PropFormula α}
    (hAB : Derives Γ (impl A B)) (hA : Derives Γ A) : Derives Γ B := by
  apply cut_same hAB
  simpa only [Finset.union_self] using
    (Derives.implLeft hA (Derives.identity (by simp) : Derives (insert B Γ) B))

theorem Derives.neg_elim {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (hA : Derives Γ A) (hN : Derives Γ (neg A)) : Derives Γ falsum := by
  exact cut_same hN (Derives.negLeft (C := falsum) hA)

theorem Derives.falsum_elim {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ falsum) : Derives Γ A := by
  exact cut_same h (Derives.falsumLeft (by simp))

theorem Derives.disj_elim {Γ : Finset (PropFormula α)} {A B C : PropFormula α}
    (hAB : Derives Γ (disj A B)) (hA : Derives (insert A Γ) C)
    (hB : Derives (insert B Γ) C) : Derives Γ C := by
  exact cut_same hAB (Derives.disjLeft hA hB)

/-- Every primitive sequent inference translates into the established native ND rules. -/
theorem Derives.to_natural {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (h : Derives Γ A) :
    Lemmatheca.ProofTheory.Intuitionistic.Derives (Γ : Set (PropFormula α)) A := by
  induction h with
  | identity hA => exact .assumption hA
  | falsumLeft hf => exact .falsumElim (.assumption hf)
  | weakening _ hsub ih => exact ih.weaken hsub
  | @conjLeft Γ A B C _ ih =>
      have hAB : Lemmatheca.ProofTheory.Intuitionistic.Derives
          ((insert (conj A B) Γ : Finset (PropFormula α)) : Set (PropFormula α))
          (conj A B) := .assumption (by simp)
      apply ih.replace
      intro D hD
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hD
      rcases hD with hD | hD | hD
      · subst D
        exact .conjElimLeft hAB
      · subst D
        exact .conjElimRight hAB
      · exact .assumption (by simp [hD])
  | conjRight _ _ ihA ihB => exact .conjIntro ihA ihB
  | @disjLeft Γ A B C _ _ ihA ihB =>
      apply Lemmatheca.ProofTheory.Intuitionistic.Derives.disjElim (A := A) (B := B)
      · exact .assumption (by simp)
      · apply ihA.weaken
        intro D hD
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hD ⊢
        aesop
      · apply ihB.weaken
        intro D hD
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hD ⊢
        aesop
  | disjRightLeft _ ih => exact .disjIntroLeft ih
  | disjRightRight _ ih => exact .disjIntroRight ih
  | @implLeft Γ Δ A B C _ _ ihA ihC =>
      have ha : Lemmatheca.ProofTheory.Intuitionistic.Derives
          ((insert (impl A B) (Γ ∪ Δ) : Finset (PropFormula α)) : Set (PropFormula α))
          A := ihA.weaken (by
        intro D hD
        simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union]
        exact Or.inr (Or.inl hD))
      have hb : Lemmatheca.ProofTheory.Intuitionistic.Derives
          ((insert (impl A B) (Γ ∪ Δ) : Finset (PropFormula α)) : Set (PropFormula α))
          B := .implElim (.assumption (by simp)) ha
      apply ihC.replace
      intro D hD
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hD
      rcases hD with hD | hD
      · subst D
        exact hb
      · exact .assumption (by simp [hD])
  | implRight _ ih =>
      apply Lemmatheca.ProofTheory.Intuitionistic.Derives.implIntro
      simpa only [Finset.coe_insert] using ih
  | @negLeft Γ A C _ ih =>
      apply Lemmatheca.ProofTheory.Intuitionistic.Derives.falsumElim
      apply Lemmatheca.ProofTheory.Intuitionistic.Derives.negElim (A := A)
      · apply ih.weaken
        intro D hD
        simp only [Finset.coe_insert, Set.mem_insert_iff]
        exact Or.inr hD
      · exact .assumption (by simp)
  | negRight _ ih =>
      apply Lemmatheca.ProofTheory.Intuitionistic.Derives.negIntro
      simpa only [Finset.coe_insert] using ih
  | @cut Γ Δ A C _ _ ihA ihC =>
      have ha : Lemmatheca.ProofTheory.Intuitionistic.Derives
          ((Γ ∪ Δ : Finset (PropFormula α)) : Set (PropFormula α)) A :=
        ihA.weaken (by
          intro D hD
          simp only [Finset.coe_union, Set.mem_union]
          exact Or.inl hD)
      apply ihC.replace
      intro D hD
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hD
      rcases hD with hD | hD
      · subst D
        exact ha
      · exact .assumption (by simp [hD])

/-- The induction invariant for converting ND under any set of supplied sequent proofs. -/
theorem from_natural {Θ : Set (PropFormula α)} {A : PropFormula α}
    (h : Lemmatheca.ProofTheory.Intuitionistic.Derives Θ A)
    {Γ : Finset (PropFormula α)} (hΘ : ∀ B ∈ Θ, Derives Γ B) : Derives Γ A := by
  induction h generalizing Γ with
  | assumption hB => exact hΘ _ hB
  | conjIntro _ _ ihA ihB => exact .conjRight (ihA hΘ) (ihB hΘ)
  | conjElimLeft _ ih => exact (ih hΘ).conj_elim_left
  | conjElimRight _ ih => exact (ih hΘ).conj_elim_right
  | disjIntroLeft _ ih => exact .disjRightLeft (ih hΘ)
  | disjIntroRight _ ih => exact .disjRightRight (ih hΘ)
  | disjElim _ _ _ ihAB ihA ihB =>
      apply Derives.disj_elim (ihAB hΘ)
      · apply ihA
        intro X hX
        rcases Set.mem_insert_iff.mp hX with rfl | hX
        · exact .identity (by simp)
        · exact .weakening (hΘ X hX) (Finset.subset_insert _ _)
      · apply ihB
        intro X hX
        rcases Set.mem_insert_iff.mp hX with rfl | hX
        · exact .identity (by simp)
        · exact .weakening (hΘ X hX) (Finset.subset_insert _ _)
  | implIntro _ ih =>
      apply Derives.implRight
      apply ih
      intro X hX
      rcases Set.mem_insert_iff.mp hX with rfl | hX
      · exact .identity (by simp)
      · exact .weakening (hΘ X hX) (Finset.subset_insert _ _)
  | implElim _ _ ihAB ihA => exact (ihAB hΘ).impl_elim (ihA hΘ)
  | negIntro _ ih =>
      apply Derives.negRight
      apply ih
      intro X hX
      rcases Set.mem_insert_iff.mp hX with rfl | hX
      · exact .identity (by simp)
      · exact .weakening (hΘ X hX) (Finset.subset_insert _ _)
  | negElim _ _ ihA ihN => exact (ihA hΘ).neg_elim (ihN hΘ)
  | falsumElim _ ih => exact (ih hΘ).falsum_elim

/-- Exact equivalence on the same finite assumptions and native concluding formula. -/
theorem derives_iff_natural (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Derives Γ A ↔
      Lemmatheca.ProofTheory.Intuitionistic.Derives (Γ : Set (PropFormula α)) A := by
  constructor
  · exact Derives.to_natural
  · intro h
    exact from_natural h (fun B hB => .identity hB)

/-- Arbitrary ND premise sets correspond to some finite allowed sequent antecedent. -/
theorem finite_premises_iff (Θ : Set (PropFormula α)) (A : PropFormula α) :
    Lemmatheca.ProofTheory.Intuitionistic.Derives Θ A ↔
      ∃ Γ : Finset (PropFormula α), (Γ : Set (PropFormula α)) ⊆ Θ ∧ Derives Γ A := by
  classical
  constructor
  · intro h
    rcases Lemmatheca.ProofTheory.Intuitionistic.finite_support.mp h with ⟨Δ, hfin, hsub, hA⟩
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · simpa using hsub
    · apply from_natural hA
      intro B hB
      exact .identity (by simpa using hB)
  · rintro ⟨Γ, hsub, hA⟩
    exact hA.to_natural.weaken hsub

end Lemmatheca.ProofTheory.Intuitionistic.SequentCalculus
