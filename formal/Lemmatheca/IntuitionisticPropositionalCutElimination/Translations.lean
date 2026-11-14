import Lemmatheca.IntuitionisticPropositionalCutElimination.Cut

namespace Lemmatheca.ProofTheory.Intuitionistic.CutFree

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

/-- The same primitive retained-principal rules, extended by an actual cut constructor. -/
inductive CutProof : Finset (PropFormula α) → PropFormula α → Type u
  | atom {Γ a} : atom a ∈ Γ → CutProof Γ (atom a)
  | falsumLeft {Γ C} : falsum ∈ Γ → CutProof Γ C
  | conjLeft {Γ A B C} : conj A B ∈ Γ → CutProof (insert A (insert B Γ)) C → CutProof Γ C
  | conjRight {Γ A B} : CutProof Γ A → CutProof Γ B → CutProof Γ (conj A B)
  | disjLeft {Γ A B C} : disj A B ∈ Γ → CutProof (insert A Γ) C →
      CutProof (insert B Γ) C → CutProof Γ C
  | disjRightLeft {Γ A B} : CutProof Γ A → CutProof Γ (disj A B)
  | disjRightRight {Γ A B} : CutProof Γ B → CutProof Γ (disj A B)
  | implLeft {Γ A B C} : impl A B ∈ Γ → CutProof Γ A → CutProof (insert B Γ) C → CutProof Γ C
  | implRight {Γ A B} : CutProof (insert A Γ) B → CutProof Γ (impl A B)
  | negLeft {Γ A C} : neg A ∈ Γ → CutProof Γ A → CutProof Γ C
  | negRight {Γ A} : CutProof (insert A Γ) falsum → CutProof Γ (neg A)
  | cut {Γ Δ A C} : CutProof Γ A → CutProof (insert A Δ) C → CutProof (Γ ∪ Δ) C

/-- Recurse on the supplied cut tree, replacing each cut after transforming its premises. -/
def CutProof.eliminate {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : CutProof Γ A) : Proof Γ A :=
  match p with
  | .atom h => .atom h
  | .falsumLeft h => .falsumLeft h
  | .conjLeft h p => .conjLeft h p.eliminate
  | .conjRight p q => .conjRight p.eliminate q.eliminate
  | .disjLeft h p q => .disjLeft h p.eliminate q.eliminate
  | .disjRightLeft p => .disjRightLeft p.eliminate
  | .disjRightRight p => .disjRightRight p.eliminate
  | .implLeft h p q => .implLeft h p.eliminate q.eliminate
  | .implRight p => .implRight p.eliminate
  | .negLeft h p => .negLeft h p.eliminate
  | .negRight p => .negRight p.eliminate
  | .cut p q => p.eliminate.cut q.eliminate

theorem Proof.to_lj {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) : SequentCalculus.Derives Γ A := by
  induction p with
  | atom h => exact .identity h
  | falsumLeft h => exact .falsumLeft h
  | conjLeft h _ ih =>
      simpa only [Finset.insert_eq_of_mem h] using SequentCalculus.Derives.conjLeft ih
  | conjRight _ _ ihA ihB => exact .conjRight ihA ihB
  | disjLeft h _ _ ihA ihB =>
      simpa only [Finset.insert_eq_of_mem h] using SequentCalculus.Derives.disjLeft ihA ihB
  | disjRightLeft _ ih => exact .disjRightLeft ih
  | disjRightRight _ ih => exact .disjRightRight ih
  | implLeft h _ _ ihA ihC =>
      simpa only [Finset.union_self, Finset.insert_eq_of_mem h] using
        SequentCalculus.Derives.implLeft ihA ihC
  | implRight _ ih => exact .implRight ih
  | negLeft h _ ih =>
      simpa only [Finset.insert_eq_of_mem h] using SequentCalculus.Derives.negLeft ih
  | negRight _ ih => exact .negRight ih

/-- Prop-valued derivability yields existence of certificates by syntactic rule induction. -/
theorem from_lj {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (h : SequentCalculus.Derives Γ A) : Nonempty (Proof Γ A) := by
  induction h with
  | identity hA => exact ⟨Proof.identity _ hA⟩
  | falsumLeft h => exact ⟨.falsumLeft h⟩
  | weakening _ hsub ih =>
      rcases ih with ⟨p⟩
      exact ⟨p.weaken hsub⟩
  | @conjLeft Γ A B C _ ih =>
      rcases ih with ⟨p⟩
      refine ⟨.conjLeft (A := A) (B := B) (by simp) (p.weaken ?_)⟩
      exact Finset.insert_subset_insert _
        (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  | conjRight _ _ ihA ihB =>
      rcases ihA with ⟨p⟩
      rcases ihB with ⟨q⟩
      exact ⟨.conjRight p q⟩
  | disjLeft _ _ ihA ihB =>
      rcases ihA with ⟨p⟩
      rcases ihB with ⟨q⟩
      exact ⟨.disjLeft (by simp)
        (p.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (q.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))⟩
  | disjRightLeft _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.disjRightLeft p⟩
  | disjRightRight _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.disjRightRight p⟩
  | @implLeft Γ Δ A B C _ _ ihA ihC =>
      rcases ihA with ⟨p⟩
      rcases ihC with ⟨q⟩
      refine ⟨.implLeft (A := A) (B := B) (by simp) (p.weaken ?_) (q.weaken ?_)⟩
      · exact Finset.subset_union_left.trans (Finset.subset_insert _ _)
      · exact Finset.insert_subset_insert _
          (Finset.subset_union_right.trans (Finset.subset_insert _ _))
  | implRight _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.implRight p⟩
  | negLeft _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.negLeft (by simp) (p.weaken (Finset.subset_insert _ _))⟩
  | negRight _ ih =>
      rcases ih with ⟨p⟩
      exact ⟨.negRight p⟩
  | cut _ _ ihA ihC =>
      rcases ihA with ⟨p⟩
      rcases ihC with ⟨q⟩
      exact ⟨p.cut q⟩

theorem proof_iff_lj (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Nonempty (Proof Γ A) ↔ SequentCalculus.Derives Γ A := by
  constructor
  · rintro ⟨p⟩
    exact p.to_lj
  · exact from_lj

theorem Proof.to_natural {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) : Intuitionistic.Derives (Γ : Set (PropFormula α)) A :=
  p.to_lj.to_natural

theorem from_natural {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (h : Intuitionistic.Derives (Γ : Set (PropFormula α)) A) :
    Nonempty (Proof Γ A) :=
  from_lj ((SequentCalculus.derives_iff_natural Γ A).mpr h)

theorem proof_iff_natural (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Nonempty (Proof Γ A) ↔ Intuitionistic.Derives (Γ : Set (PropFormula α)) A :=
  (proof_iff_lj Γ A).trans (SequentCalculus.derives_iff_natural Γ A)

theorem expandNegation_iff (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Nonempty (Proof Γ A) ↔
      Nonempty (Proof (Γ.image Intuitionistic.expandNegation) (Intuitionistic.expandNegation A)) :=
  by
    rw [proof_iff_natural, proof_iff_natural]
    simpa only [Finset.coe_image] using Intuitionistic.expandNegation_derives_iff
      (Γ : Set (PropFormula α)) A

end Lemmatheca.ProofTheory.Intuitionistic.CutFree
