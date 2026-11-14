import Lemmatheca.PropositionalFriedmanTranslation.Translation

namespace Lemmatheca.ProofTheory.Intuitionistic.FriedmanTranslation

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open CutFree

universe u
variable {α : Type u}

/-- Formula recursion constructs an actual cut-free tree from the parameter. -/
def parameterExplosion [DecidableEq α] (R : PropFormula α) (A : PropFormula α) :
    Proof {R} (formula R A) :=
  match A with
  | .atom _ => .disjRightRight (Proof.identity R (Finset.mem_singleton_self _))
  | .falsum => Proof.identity R (Finset.mem_singleton_self _)
  | .neg _ => .implRight (Proof.identity R
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  | .conj A B => .conjRight (parameterExplosion R A) (parameterExplosion R B)
  | .disj A _ => .disjRightLeft (parameterExplosion R A)
  | .impl A B => .implRight
      ((parameterExplosion R B).weaken (Finset.subset_insert (formula R A) {R}))

/-- The same supplied construction weakened to an ambient antecedent containing the parameter. -/
def parameterExplosionIn [DecidableEq α] (R A : PropFormula α)
    {Γ : Finset (PropFormula α)} (hR : R ∈ Γ) : Proof Γ (formula R A) :=
  (parameterExplosion R A).weaken (Finset.singleton_subset_iff.mpr hR)

/-- Structural recursion on the actual supplied tree, with all eleven primitive clauses. -/
def translate [DecidableEq α] (R : PropFormula α)
    {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : Proof Γ A) : Proof (finiteContext R Γ) (formula R A) :=
  match p with
  | .atom h => Proof.identity _ (mem_finiteContext R h)
  | .falsumLeft h => parameterExplosionIn R _ (mem_finiteContext R h)
  | .conjLeft h p => .conjLeft (mem_finiteContext R h)
      (by simpa only [finiteContext_insert] using translate R p)
  | .conjRight p q => .conjRight (translate R p) (translate R q)
  | .disjLeft h p q => .disjLeft (mem_finiteContext R h)
      (by simpa only [finiteContext_insert] using translate R p)
      (by simpa only [finiteContext_insert] using translate R q)
  | .disjRightLeft p => .disjRightLeft (translate R p)
  | .disjRightRight p => .disjRightRight (translate R p)
  | .implLeft h p q => .implLeft (mem_finiteContext R h) (translate R p)
      (by simpa only [finiteContext_insert] using translate R q)
  | .implRight p => .implRight
      (by simpa only [finiteContext_insert] using translate R p)
  | .negLeft h p => .implLeft (mem_finiteContext R h) (translate R p)
      (parameterExplosionIn R _ (Finset.mem_insert_self _ _))
  | .negRight p => .implRight
      (by simpa only [finiteContext_insert, formula] using translate R p)

/-- The cut-input map is literally elimination of this input followed by translation. -/
def translateCut [DecidableEq α] (R : PropFormula α)
    {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : CutProof Γ A) : Proof (finiteContext R Γ) (formula R A) :=
  translate R p.eliminate

/-- The Prop-valued native calculus asserts existence; this is not a choice of proof data. -/
theorem preserves {Γ : Set (PropFormula α)} {A : PropFormula α}
    (R : PropFormula α) (h : Derives Γ A) : Derives (context R Γ) (formula R A) := by
  classical
  obtain ⟨Δ, hfin, hsub, hd⟩ := finite_support.mp h
  have hfinite : Derives (hfin.toFinset : Set (PropFormula α)) A := by
    simpa only [Set.Finite.coe_toFinset] using hd
  obtain ⟨p⟩ := CutFree.from_natural hfinite
  have ht : Derives (context R Δ) (formula R A) := by
    simpa only [coe_finiteContext, Set.Finite.coe_toFinset] using (translate R p).to_natural
  exact ht.weaken (Set.image_mono hsub)

end Lemmatheca.ProofTheory.Intuitionistic.FriedmanTranslation
