import Lemmatheca.FirstOrderNegativeTranslation.Classical

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
set_option maxHeartbeats 1200000
local instance negativeConventionsFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

/-- Two uniform supplied-tree conversions, with no reserve or ground-term assumption. -/
structure RawEquivalence (e : Bool) (A B : Formula L α) where
  forward : ∀ Γ : NaturalDeduction.Context L α,
    NaturalDeduction.Derivation false e L Γ A → NaturalDeduction.Derivation false e L Γ B
  backward : ∀ Γ : NaturalDeduction.Context L α,
    NaturalDeduction.Derivation false e L Γ B → NaturalDeduction.Derivation false e L Γ A

private theorem open_instance (B : BoundedFormula L α 1) :
    (B.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr x => have hx : x = 0 := Subsingleton.elim _ _; subst x; rfl

private def openAll {Γ : NaturalDeduction.Context L α} {B : BoundedFormula L α 1}
    (p : NaturalDeduction.Derivation false e L Γ (.all B)) :
    NaturalDeduction.Derivation false e L (NaturalDeduction.liftContext Γ) B.toFormula := by
  have hr := p.rename (Sum.inl : α → α ⊕ Fin 1)
  have he : (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all B).rename
      (Sum.inl : α → α ⊕ Fin 1) = .all (B.rename Sum.inl) :=
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all B _
  rw [he] at hr
  have hp := NaturalDeduction.Derivation.allElim (.var (.inr 0)) hr
  rw [open_instance] at hp
  exact hp

private def negateEquivalence {A B : Formula L α} (h : RawEquivalence e A B) :
    RawEquivalence e (.neg A) (.neg B) := by
  refine ⟨?_, ?_⟩
  · intro Γ p
    apply NaturalDeduction.Derivation.negIntro
    exact .negElim (h.backward _ (.assumption (Finset.mem_insert_self _ _)))
      (p.weaken (Finset.subset_insert _ _))
  · intro Γ p
    apply NaturalDeduction.Derivation.negIntro
    exact .negElim (h.forward _ (.assumption (Finset.mem_insert_self _ _)))
      (p.weaken (Finset.subset_insert _ _))

def negDisjunctionEquivalence (e : Bool) (C D : Formula L α) :
    RawEquivalence e (.neg (.disj C D)) (.conj (.neg C) (.neg D)) := by
  refine ⟨?_, ?_⟩
  · intro Γ p
    apply NaturalDeduction.Derivation.conjIntro
    · apply NaturalDeduction.Derivation.negIntro
      exact .negElim (.disjIntroLeft (.assumption (Finset.mem_insert_self _ _)))
        (p.weaken (Finset.subset_insert _ _))
    · apply NaturalDeduction.Derivation.negIntro
      exact .negElim (.disjIntroRight (.assumption (Finset.mem_insert_self _ _)))
        (p.weaken (Finset.subset_insert _ _))
  · intro Γ p
    apply NaturalDeduction.Derivation.negIntro
    apply NaturalDeduction.Derivation.disjElim (.assumption (Finset.mem_insert_self _ _))
    · exact .negElim (.assumption (Finset.mem_insert_self _ _))
        ((NaturalDeduction.Derivation.conjElimLeft p).weaken (by intro F hF; simp [hF]))
    · exact .negElim (.assumption (Finset.mem_insert_self _ _))
        ((NaturalDeduction.Derivation.conjElimRight p).weaken (by intro F hF; simp [hF]))

def negExistentialEquivalence (e : Bool) (E : BoundedFormula L α 1) :
    RawEquivalence e (.neg (.ex E)) (.all (.neg E)) := by
  refine ⟨?_, ?_⟩
  · intro Γ p
    apply NaturalDeduction.Derivation.allIntro
    apply NaturalDeduction.Derivation.negIntro
    have hr : NaturalDeduction.Derivation false e L (NaturalDeduction.liftContext Γ)
        (.neg (.ex (E.rename Sum.inl))) := by
      have hp := p.rename (Sum.inl : α → α ⊕ Fin 1)
      simpa only [NaturalDeduction.liftContext,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hp
    apply NaturalDeduction.Derivation.negElim ?_ (hr.weaken (Finset.subset_insert _ _))
    apply NaturalDeduction.Derivation.exIntro (.var (.inr 0))
    rw [open_instance]
    exact .assumption (Finset.mem_insert_self _ _)
  · intro Γ p
    apply NaturalDeduction.Derivation.negIntro
    apply NaturalDeduction.Derivation.exElim (.assumption (Finset.mem_insert_self _ _))
    exact .negElim (.assumption (Finset.mem_insert_self _ _))
      ((openAll (p.weaken (Finset.subset_insert (.ex E) Γ))).weaken
        (Finset.subset_insert E.toFormula _))

def disjunctionConvention (e : Bool) (C D : Formula L α) :
    RawEquivalence e (.neg (.neg (.disj C D))) (.neg (.conj (.neg C) (.neg D))) := by
  exact negateEquivalence (negDisjunctionEquivalence e C D)

def existentialConvention (e : Bool) (E : BoundedFormula L α 1) :
    RawEquivalence e (.neg (.neg (.ex E))) (.neg (.all (.neg E))) := by
  exact negateEquivalence (negExistentialEquivalence e E)

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
