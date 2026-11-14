import Lemmatheca.IntuitionisticPropositionalVerifications.Translations

namespace Lemmatheca.ProofTheory.Intuitionistic.Verification

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

mutual
  /-- All context members and conclusions at every node of a neutral tree. -/
  def Neutral.formulas {Γ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Neutral Γ A) : Finset (PropFormula α) :=
    match p with
    | .assumption _ => insert A Γ
    | .conjLeft p => insert A Γ ∪ p.formulas
    | .conjRight p => insert A Γ ∪ p.formulas
    | .implApply p q => insert A Γ ∪ p.formulas ∪ q.formulas
    | .negApply p q => insert A Γ ∪ p.formulas ∪ q.formulas
  /-- All context members and conclusions, including temporary assumptions. -/
  def Normal.formulas {Γ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Normal Γ A) : Finset (PropFormula α) :=
    match p with
    | .neutral p => insert A Γ ∪ p.formulas
    | .conjIntro p q => insert A Γ ∪ p.formulas ∪ q.formulas
    | .disjIntroLeft p => insert A Γ ∪ p.formulas
    | .disjIntroRight p => insert A Γ ∪ p.formulas
    | .implIntro p => insert A Γ ∪ p.formulas
    | .negIntro p => insert A Γ ∪ p.formulas
    | .cases p q r => insert A Γ ∪ p.formulas ∪ q.formulas ∪ r.formulas
    | .explode p => insert A Γ ∪ p.formulas
end

private theorem closure_self (A : PropFormula α) : A ∈ CutFree.analyticClosure A := by
  cases A <;> simp [CutFree.analyticClosure]

private theorem closure_bot (A : PropFormula α) : falsum ∈ CutFree.analyticClosure A := by
  induction A <;> simp_all [CutFree.analyticClosure]

private theorem closure_trans {A B : PropFormula α} (h : B ∈ CutFree.analyticClosure A) :
    CutFree.analyticClosure B ⊆ CutFree.analyticClosure A := by
  induction A generalizing B with
  | atom a =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.refl _
      · have hB := Finset.mem_singleton.mp h
        subst B
        simp [CutFree.analyticClosure]
  | falsum =>
      have hB : B = falsum := Finset.mem_singleton.mp h
      subst B
      exact Finset.Subset.refl _
  | neg A ih =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.refl _
      · exact (ih h).trans (Finset.subset_insert _ _)
  | conj A C ihA ihC =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.refl _
      · rcases Finset.mem_union.mp h with h | h
        · exact (ihA h).trans (Finset.subset_union_left.trans (Finset.subset_insert _ _))
        · exact (ihC h).trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))
  | disj A C ihA ihC =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.refl _
      · rcases Finset.mem_union.mp h with h | h
        · exact (ihA h).trans (Finset.subset_union_left.trans (Finset.subset_insert _ _))
        · exact (ihC h).trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))
  | impl A C ihA ihC =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.refl _
      · rcases Finset.mem_union.mp h with h | h
        · exact (ihA h).trans (Finset.subset_union_left.trans (Finset.subset_insert _ _))
        · exact (ihC h).trans (Finset.subset_union_right.trans (Finset.subset_insert _ _))


private theorem root_closed {Γ : Finset (PropFormula α)} {A : PropFormula α}
    {Ξ : Set (PropFormula α)} (hΓ : (Γ : Set (PropFormula α)) ⊆ Ξ) (hA : A ∈ Ξ) :
    ((insert A Γ : Finset (PropFormula α)) : Set (PropFormula α)) ⊆ Ξ := by
  simpa only [Finset.coe_insert] using Set.insert_subset hA hΓ

private theorem union_closed {S T : Finset (PropFormula α)} {Ξ : Set (PropFormula α)}
    (hS : (S : Set (PropFormula α)) ⊆ Ξ) (hT : (T : Set (PropFormula α)) ⊆ Ξ) :
    ((S ∪ T : Finset (PropFormula α)) : Set (PropFormula α)) ⊆ Ξ := by
  simpa only [Finset.coe_union] using Set.union_subset hS hT

mutual
  private theorem neutral_closed {Γ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Neutral Γ A) {Ξ : Set (PropFormula α)}
      (hΓ : (Γ : Set (PropFormula α)) ⊆ Ξ) (hbot : falsum ∈ Ξ)
      (hc : ∀ D ∈ Ξ, (CutFree.analyticClosure D : Set (PropFormula α)) ⊆ Ξ) :
      A ∈ Ξ ∧ (p.formulas : Set (PropFormula α)) ⊆ Ξ :=
    match p with
    | .assumption h => ⟨hΓ h, root_closed hΓ (hΓ h)⟩
    | @Neutral.conjLeft _ _ Γ X Y p => by
        rcases neutral_closed p hΓ hbot hc with ⟨hXY, ht⟩
        have hX : X ∈ Ξ := hc _ hXY (by simp [CutFree.analyticClosure, closure_self])
        exact ⟨hX, union_closed (root_closed hΓ hX) ht⟩
    | @Neutral.conjRight _ _ Γ X Y p => by
        rcases neutral_closed p hΓ hbot hc with ⟨hXY, ht⟩
        have hY : Y ∈ Ξ := hc _ hXY (by simp [CutFree.analyticClosure, closure_self])
        exact ⟨hY, union_closed (root_closed hΓ hY) ht⟩
    | @Neutral.implApply _ _ Γ X Y p q => by
        rcases neutral_closed p hΓ hbot hc with ⟨hXY, ht⟩
        have hX : X ∈ Ξ := hc _ hXY (by simp [CutFree.analyticClosure, closure_self])
        have hY : Y ∈ Ξ := hc _ hXY (by simp [CutFree.analyticClosure, closure_self])
        exact ⟨hY, union_closed (union_closed (root_closed hΓ hY) ht)
          (normal_closed q hΓ hX hbot hc)⟩
    | @Neutral.negApply _ _ Γ X p q => by
        rcases neutral_closed p hΓ hbot hc with ⟨hNX, ht⟩
        have hX : X ∈ Ξ := hc _ hNX (by simp [CutFree.analyticClosure, closure_self])
        exact ⟨hbot, union_closed (union_closed (root_closed hΓ hbot) ht)
          (normal_closed q hΓ hX hbot hc)⟩
  termination_by structural p

  private theorem normal_closed {Γ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Normal Γ A) {Ξ : Set (PropFormula α)}
      (hΓ : (Γ : Set (PropFormula α)) ⊆ Ξ) (hA : A ∈ Ξ) (hbot : falsum ∈ Ξ)
      (hc : ∀ D ∈ Ξ, (CutFree.analyticClosure D : Set (PropFormula α)) ⊆ Ξ) :
      (p.formulas : Set (PropFormula α)) ⊆ Ξ :=
    match p with
    | .neutral p => union_closed (root_closed hΓ hA) (neutral_closed p hΓ hbot hc).2
    | @Normal.conjIntro _ _ Γ X Y p q => by
        have hX : X ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        have hY : Y ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        exact union_closed (union_closed (root_closed hΓ hA) (normal_closed p hΓ hX hbot hc))
          (normal_closed q hΓ hY hbot hc)
    | @Normal.disjIntroLeft _ _ Γ X Y p => by
        have hX : X ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        exact union_closed (root_closed hΓ hA) (normal_closed p hΓ hX hbot hc)
    | @Normal.disjIntroRight _ _ Γ X Y p => by
        have hY : Y ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        exact union_closed (root_closed hΓ hA) (normal_closed p hΓ hY hbot hc)
    | @Normal.implIntro _ _ Γ X Y p => by
        have hX : X ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        have hY : Y ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        exact union_closed (root_closed hΓ hA)
          (normal_closed p (root_closed hΓ hX) hY hbot hc)
    | @Normal.negIntro _ _ Γ X p => by
        have hX : X ∈ Ξ := hc _ hA (by simp [CutFree.analyticClosure, closure_self])
        exact union_closed (root_closed hΓ hA)
          (normal_closed p (root_closed hΓ hX) hbot hbot hc)
    | @Normal.cases _ _ Γ X Y C p q r => by
        rcases neutral_closed p hΓ hbot hc with ⟨hXY, ht⟩
        have hX : X ∈ Ξ := hc _ hXY (by simp [CutFree.analyticClosure, closure_self])
        have hY : Y ∈ Ξ := hc _ hXY (by simp [CutFree.analyticClosure, closure_self])
        exact union_closed
          (union_closed (union_closed (root_closed hΓ hA) ht)
            (normal_closed q (root_closed hΓ hX) hA hbot hc))
          (normal_closed r (root_closed hΓ hY) hA hbot hc)
    | .explode p => union_closed (root_closed hΓ hA) (neutral_closed p hΓ hbot hc).2
  termination_by structural p
end

theorem Neutral.analytic {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Neutral Γ A) {Ξ : Set (PropFormula α)}
    (hΓ : (Γ : Set (PropFormula α)) ⊆ Ξ) (hbot : falsum ∈ Ξ)
    (hc : ∀ D ∈ Ξ, (CutFree.analyticClosure D : Set (PropFormula α)) ⊆ Ξ) :
    A ∈ Ξ ∧ (p.formulas : Set (PropFormula α)) ⊆ Ξ := by
  exact neutral_closed p hΓ hbot hc

theorem Normal.analytic {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Normal Γ A) {Ξ : Set (PropFormula α)}
    (hΓ : (Γ : Set (PropFormula α)) ⊆ Ξ) (hA : A ∈ Ξ) (hbot : falsum ∈ Ξ)
    (hc : ∀ D ∈ Ξ, (CutFree.analyticClosure D : Set (PropFormula α)) ⊆ Ξ) :
    (p.formulas : Set (PropFormula α)) ⊆ Ξ := by
  exact normal_closed p hΓ hA hbot hc

theorem Normal.formulas_subset {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Normal Γ A) : p.formulas ⊆ CutFree.sequentClosure Γ A := by
  apply p.analytic (Ξ := (CutFree.sequentClosure Γ A : Set (PropFormula α)))
  · intro D hD
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨D, hD, closure_self D⟩)
  · exact Finset.mem_union_left _ (closure_self A)
  · exact Finset.mem_union_left _ (closure_bot A)
  · intro D hD E hE
    rcases Finset.mem_union.mp hD with hD | hD
    · exact Finset.mem_union_left _ (closure_trans hD hE)
    · rcases Finset.mem_biUnion.mp hD with ⟨B, hB, hDB⟩
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨B, hB, closure_trans hDB hE⟩)

private theorem neutralOpen {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Neutral Γ A) : Γ.Nonempty :=
  match p with
  | .assumption h => ⟨_, h⟩
  | .conjLeft p => neutralOpen p
  | .conjRight p => neutralOpen p
  | .implApply p _ => neutralOpen p
  | .negApply p _ => neutralOpen p

/-- The neutral major-premise path cannot start from an empty context. -/
theorem no_closed_neutral {A : PropFormula α} (p : Neutral (α := α) ∅ A) : False := by
  exact Finset.not_nonempty_empty (neutralOpen p)

/-- Inspect the actual final constructor to choose the actual disjunct certificate. -/
def extractDisjunction {A B : PropFormula α} (p : Normal (α := α) ∅ (disj A B)) :
    Sum (Normal ∅ A) (Normal ∅ B) :=
  match p with
  | .neutral p => False.elim (no_closed_neutral p)
  | .disjIntroLeft p => Sum.inl p
  | .disjIntroRight p => Sum.inr p
  | .cases p _ _ => False.elim (no_closed_neutral p)
  | .explode p => False.elim (no_closed_neutral p)

def extractCutDisjunction {A B : PropFormula α}
    (p : CutFree.CutProof (α := α) ∅ (disj A B)) : Sum (Normal ∅ A) (Normal ∅ B) :=
  extractDisjunction (normalOfCut p)

theorem natural_disjunction (A B : PropFormula α) :
    Intuitionistic.Derives ∅ (disj A B) ↔
      Intuitionistic.Derives ∅ A ∨ Intuitionistic.Derives ∅ B := by
  constructor
  · intro h
    have hn : Nonempty (Normal ∅ (disj A B)) := (normal_iff_natural _ _).mpr (by simpa using h)
    rcases hn with ⟨p⟩
    cases extractDisjunction p with
    | inl p => exact Or.inl (by simpa using p.toSequent.to_natural)
    | inr p => exact Or.inr (by simpa using p.toSequent.to_natural)
  · rintro (h | h)
    · exact .disjIntroLeft h
    · exact .disjIntroRight h

end Lemmatheca.ProofTheory.Intuitionistic.Verification
