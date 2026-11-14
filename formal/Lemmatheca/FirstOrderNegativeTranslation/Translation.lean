import Lemmatheca.FirstOrderNegativeTranslation.Stability

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
set_option maxHeartbeats 1200000
local instance negativeTranslationFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

variable {Γ : NaturalDeduction.Context L α} {A B C : Formula L α}

/-- Consume a double-negated native disjunction with the supplied stable-target branches. -/
def disjunctionElim (hC : Stable e C)
    (p : NaturalDeduction.Derivation false e L Γ (.neg (.neg (.disj A B))))
    (pa : NaturalDeduction.Derivation false e L (insert A Γ) C)
    (pb : NaturalDeduction.Derivation false e L (insert B Γ) C) :
    NaturalDeduction.Derivation false e L Γ C := by
  apply hC Γ
  apply NaturalDeduction.Derivation.negIntro
  have hn : NaturalDeduction.Derivation false e L (insert (.neg C) Γ) (.neg (.disj A B)) := by
    apply NaturalDeduction.Derivation.negIntro
    apply NaturalDeduction.Derivation.disjElim (.assumption (Finset.mem_insert_self _ _))
    · exact .negElim (pa.weaken (by
        intro F hF
        rcases Finset.mem_insert.mp hF with hF | hF <;> simp [hF]))
        (.assumption (by simp))
    · exact .negElim (pb.weaken (by
        intro F hF
        rcases Finset.mem_insert.mp hF with hF | hF <;> simp [hF]))
        (.assumption (by simp))
  exact .negElim hn (p.weaken (Finset.subset_insert _ _))

def disjunctionIntroLeft (B : Formula L α)
    (p : NaturalDeduction.Derivation false e L Γ (negative A)) :
    NaturalDeduction.Derivation false e L Γ (negative (.disj A B)) := by
  exact doubleNegIntro (.disjIntroLeft p)

def disjunctionIntroRight (A : Formula L α)
    (p : NaturalDeduction.Derivation false e L Γ (negative B)) :
    NaturalDeduction.Derivation false e L Γ (negative (.disj A B)) := by
  exact doubleNegIntro (.disjIntroRight p)

def universalIntro (B : BoundedFormula L α 1)
    (p : NaturalDeduction.Derivation false e L (context (NaturalDeduction.liftContext Γ))
      (negative B.toFormula)) :
    NaturalDeduction.Derivation false e L (context Γ) (negative (.all B)) := by
  rw [context_lift, negative_open] at p
  exact .allIntro p

def universalElim (B : BoundedFormula L α 1) (t : L.Term α)
    (p : NaturalDeduction.Derivation false e L (context Γ) (negative (.all B))) :
    NaturalDeduction.Derivation false e L (context Γ) (negative (B.instantiate t)) := by
  rw [negative_instantiate]
  exact .allElim t p

def existentialIntro (B : BoundedFormula L α 1) (t : L.Term α)
    (p : NaturalDeduction.Derivation false e L (context Γ) (negative (B.instantiate t))) :
    NaturalDeduction.Derivation false e L (context Γ) (negative (.ex B)) := by
  apply doubleNegIntro
  apply NaturalDeduction.Derivation.exIntro t
  rw [← negative_instantiate]
  exact p

/-- Use the actual protected witness branch, before stabilizing the endpoint. -/
def existentialElim (B : BoundedFormula L α 1)
    (p : NaturalDeduction.Derivation false e L (context Γ) (negative (.ex B)))
    (pb : NaturalDeduction.Derivation false e L
      (context (insert B.toFormula (NaturalDeduction.liftContext Γ)))
      (negative (C.rename Sum.inl))) :
    NaturalDeduction.Derivation false e L (context Γ) (negative C) := by
  apply negativeStable e C (context Γ)
  apply NaturalDeduction.Derivation.negIntro
  have branch : NaturalDeduction.Derivation false e L
      (insert (negative B).toFormula (NaturalDeduction.liftContext (context Γ)))
      ((negative C).rename Sum.inl) := by
    simpa only [context_insert, context_lift, negative_open, negative_rename] using pb
  have hn : NaturalDeduction.Derivation false e L (insert (.neg (negative C)) (context Γ))
      (.neg (.ex (negative B))) := by
    apply NaturalDeduction.Derivation.negIntro
    apply NaturalDeduction.Derivation.exElim (.assumption (Finset.mem_insert_self _ _))
    apply NaturalDeduction.Derivation.negElim (branch.weaken ?_) ?_
    · intro F hF
      simp only [NaturalDeduction.liftContext, Finset.image_insert, Finset.mem_insert] at hF ⊢
      rcases hF with hF | hF
      · exact Or.inl hF
      · exact Or.inr (Or.inr (Or.inr hF))
    · apply NaturalDeduction.Derivation.assumption
      simp only [NaturalDeduction.liftContext, Finset.image_insert]
      have he : (negative C).neg.rename (Sum.inl : α → α ⊕ Fin 1) =
          .neg ((negative C).rename Sum.inl) :=
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg _ _
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  exact .negElim hn (p.weaken (Finset.subset_insert _ _))

def equalityIntro (t : L.Term α) (he : e = true) :
    NaturalDeduction.Derivation false e L (context Γ) (negative (NaturalDeduction.termEqual t t)) := by
  exact doubleNegIntro (.equalIntro t he)

def equalityElim (B : BoundedFormula L α 1) (s t : L.Term α) (he : e = true)
    (peq : NaturalDeduction.Derivation false e L (context Γ)
      (negative (NaturalDeduction.termEqual s t)))
    (pb : NaturalDeduction.Derivation false e L (context Γ) (negative (B.instantiate s))) :
    NaturalDeduction.Derivation false e L (context Γ) (negative (B.instantiate t)) := by
  apply negativeStable e (B.instantiate t) (context Γ)
  apply NaturalDeduction.Derivation.negIntro
  have hn : NaturalDeduction.Derivation false e L
      (insert (.neg (negative (B.instantiate t))) (context Γ))
      (.neg (NaturalDeduction.termEqual s t)) := by
    apply NaturalDeduction.Derivation.negIntro
    have ht : NaturalDeduction.Derivation false e L
        (insert (NaturalDeduction.termEqual s t)
          (insert (.neg (negative (B.instantiate t))) (context Γ)))
        (negative (B.instantiate t)) := by
      have hs : NaturalDeduction.Derivation false e L
          (insert (NaturalDeduction.termEqual s t)
            (insert (.neg (negative (B.instantiate t))) (context Γ)))
          ((negative B).instantiate s) := by
        simpa only [negative_instantiate] using
          pb.weaken (Finset.Subset.trans (Finset.subset_insert _ _) (Finset.subset_insert _ _))
      have hp := NaturalDeduction.Derivation.equalElim (negative B) s t he
        (NaturalDeduction.Derivation.assumption (Finset.mem_insert_self _ _)) hs
      simpa only [negative_instantiate] using hp
    exact .negElim ht (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  exact .negElim hn (peq.weaken (Finset.subset_insert _ _))

def classicalStep
    (p : NaturalDeduction.Derivation false e L (context (insert (.neg A) Γ)) .falsum) :
    NaturalDeduction.Derivation false e L (context Γ) (negative A) := by
  apply negativeStable e A (context Γ)
  apply NaturalDeduction.Derivation.negIntro
  simpa only [context_insert, negative] using p

/-- Translate the particular supplied native classical tree with its equality mode unchanged. -/
def translate (p : NaturalDeduction.Derivation true e L Γ A) :
    NaturalDeduction.Derivation false e L (context Γ) (negative A) := by
  clear B C
  induction p with
  | assumption hA => exact .assumption (Finset.mem_image.mpr ⟨_, hA, rfl⟩)
  | conjIntro _ _ ihA ihB => exact .conjIntro ihA ihB
  | conjElimLeft _ ih => exact .conjElimLeft ih
  | conjElimRight _ ih => exact .conjElimRight ih
  | disjIntroLeft _ ih => exact disjunctionIntroLeft _ ih
  | disjIntroRight _ ih => exact disjunctionIntroRight _ ih
  | disjElim _ _ _ ihAB ihA ihB =>
      apply disjunctionElim (negativeStable e _) ihAB
      · simpa only [context_insert] using ihA
      · simpa only [context_insert] using ihB
  | impIntro _ ih =>
      apply NaturalDeduction.Derivation.impIntro
      simpa only [context_insert] using ih
  | impElim _ _ ihAB ihA => exact .impElim ihAB ihA
  | negIntro _ ih =>
      apply NaturalDeduction.Derivation.negIntro
      simpa only [context_insert, negative] using ih
  | negElim _ _ ihA ihnA => exact .negElim ihA ihnA
  | falsumElim _ ih => exact .falsumElim ih
  | classicalContradiction _ _ ih => exact classicalStep ih
  | allElim t _ ih => exact universalElim _ t ih
  | exIntro t _ ih => exact existentialIntro _ t ih
  | allIntro _ ih => exact universalIntro _ ih
  | exElim _ _ ihEx ihB => exact existentialElim _ ihEx ihB
  | equalIntro t he => exact equalityIntro t he
  | equalElim B s t he _ _ ihEq ihB => exact equalityElim B s t he ihEq ihB

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
