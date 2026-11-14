import Lemmatheca.IntuitionisticPropositionalCutElimination.Translations

namespace Lemmatheca.ProofTheory.Intuitionistic.CutFree

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

/-- Native subformulas, with falsum explicitly allowed for native negation rules. -/
def analyticClosure : PropFormula α → Finset (PropFormula α)
  | .atom a => {atom a, falsum}
  | .falsum => {falsum}
  | .neg A => insert (neg A) (analyticClosure A)
  | .conj A B => insert (conj A B) (analyticClosure A ∪ analyticClosure B)
  | .disj A B => insert (disj A B) (analyticClosure A ∪ analyticClosure B)
  | .impl A B => insert (impl A B) (analyticClosure A ∪ analyticClosure B)

def sequentClosure (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Finset (PropFormula α) := analyticClosure A ∪ Γ.biUnion analyticClosure

/-- Every antecedent and succedent formula displayed anywhere in the given tree. -/
def Proof.formulas {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) : Finset (PropFormula α) :=
  match p with
  | .atom _ => insert A Γ
  | .falsumLeft _ => insert A Γ
  | .conjLeft _ q => insert A Γ ∪ q.formulas
  | .conjRight p q => insert A Γ ∪ p.formulas ∪ q.formulas
  | .disjLeft _ p q => insert A Γ ∪ p.formulas ∪ q.formulas
  | .disjRightLeft p => insert A Γ ∪ p.formulas
  | .disjRightRight p => insert A Γ ∪ p.formulas
  | .implLeft _ p q => insert A Γ ∪ p.formulas ∪ q.formulas
  | .implRight p => insert A Γ ∪ p.formulas
  | .negLeft _ p => insert A Γ ∪ p.formulas
  | .negRight p => insert A Γ ∪ p.formulas

private theorem closure_self (A : PropFormula α) : A ∈ analyticClosure A := by
  cases A <;> simp [analyticClosure]

private theorem closure_bot (A : PropFormula α) : falsum ∈ analyticClosure A := by
  induction A <;> simp_all [analyticClosure]

private theorem closure_trans {A B : PropFormula α} (h : B ∈ analyticClosure A) :
    analyticClosure B ⊆ analyticClosure A := by
  induction A generalizing B with
  | atom a =>
      rcases Finset.mem_insert.mp h with rfl | h
      · exact Finset.Subset.refl _
      · have hB := Finset.mem_singleton.mp h
        subst B
        simp [analyticClosure]
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

private theorem displayed_closed {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) {Ξ : Finset (PropFormula α)}
    (hΓ : Γ ⊆ Ξ) (hA : A ∈ Ξ) (hbot : falsum ∈ Ξ)
    (hc : ∀ D ∈ Ξ, analyticClosure D ⊆ Ξ) : p.formulas ⊆ Ξ := by
  induction p generalizing Ξ with
  | atom _ => exact Finset.insert_subset hA hΓ
  | falsumLeft _ => exact Finset.insert_subset hA hΓ
  | @conjLeft Γ X Y C h _ ih =>
      have hX : X ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      have hY : Y ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      exact Finset.union_subset (Finset.insert_subset hA hΓ)
        (ih (Finset.insert_subset hX (Finset.insert_subset hY hΓ)) hA hbot hc)
  | @conjRight Γ X Y _ _ ihX ihY =>
      have hX : X ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      have hY : Y ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      exact Finset.union_subset
        (Finset.union_subset (Finset.insert_subset hA hΓ) (ihX hΓ hX hbot hc))
        (ihY hΓ hY hbot hc)
  | @disjLeft Γ X Y C h _ _ ihX ihY =>
      have hX : X ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      have hY : Y ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      exact Finset.union_subset
        (Finset.union_subset (Finset.insert_subset hA hΓ)
          (ihX (Finset.insert_subset hX hΓ) hA hbot hc))
        (ihY (Finset.insert_subset hY hΓ) hA hbot hc)
  | @disjRightLeft Γ X Y _ ih =>
      have hX : X ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      exact Finset.union_subset (Finset.insert_subset hA hΓ) (ih hΓ hX hbot hc)
  | @disjRightRight Γ X Y _ ih =>
      have hY : Y ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      exact Finset.union_subset (Finset.insert_subset hA hΓ) (ih hΓ hY hbot hc)
  | @implLeft Γ X Y C h _ _ ihX ihC =>
      have hX : X ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      have hY : Y ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      exact Finset.union_subset
        (Finset.union_subset (Finset.insert_subset hA hΓ) (ihX hΓ hX hbot hc))
        (ihC (Finset.insert_subset hY hΓ) hA hbot hc)
  | @implRight Γ X Y _ ih =>
      have hX : X ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      have hY : Y ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      exact Finset.union_subset (Finset.insert_subset hA hΓ)
        (ih (Finset.insert_subset hX hΓ) hY hbot hc)
  | @negLeft Γ X C h _ ih =>
      have hX : X ∈ Ξ := hc _ (hΓ h) (by simp [analyticClosure, closure_self])
      exact Finset.union_subset (Finset.insert_subset hA hΓ) (ih hΓ hX hbot hc)
  | @negRight Γ X _ ih =>
      have hX : X ∈ Ξ := hc _ hA (by simp [analyticClosure, closure_self])
      exact Finset.union_subset (Finset.insert_subset hA hΓ)
        (ih (Finset.insert_subset hX hΓ) hbot hbot hc)

theorem Proof.formulas_subset {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) : p.formulas ⊆ sequentClosure Γ A := by
  apply displayed_closed p
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

theorem no_closed_falsum : ¬ Nonempty (Proof (α := α) ∅ falsum) := by
  rintro ⟨p⟩
  cases p with
  | falsumLeft h => exact Finset.notMem_empty _ h
  | conjLeft h _ => exact Finset.notMem_empty _ h
  | disjLeft h _ _ => exact Finset.notMem_empty _ h
  | implLeft h _ _ => exact Finset.notMem_empty _ h
  | negLeft h _ => exact Finset.notMem_empty _ h

theorem no_lj_closed_falsum : ¬ SequentCalculus.Derives (α := α) ∅ falsum :=
  fun h => no_closed_falsum (from_lj h)

theorem no_natural_closed_falsum :
    ¬ Intuitionistic.Derives (α := α) ∅ falsum := by
  intro h
  apply no_closed_falsum (α := α)
  apply from_natural
  simpa only [Finset.coe_empty] using h

end Lemmatheca.ProofTheory.Intuitionistic.CutFree
