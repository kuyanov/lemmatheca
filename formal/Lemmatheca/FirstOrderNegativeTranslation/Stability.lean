import Lemmatheca.FirstOrderNegativeTranslation.Syntax

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
set_option maxHeartbeats 1200000
local instance negativeStabilityFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

/-- A uniform operation on supplied intuitionistic raw trees, in every finite context. -/
def Stable (e : Bool) (C : Formula L α) : Type max u v (a+1) :=
  ∀ Γ : NaturalDeduction.Context L α,
    NaturalDeduction.Derivation false e L Γ (.neg (.neg C)) →
      NaturalDeduction.Derivation false e L Γ C

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

def doubleNegIntro {Γ : NaturalDeduction.Context L α} {C : Formula L α}
    (p : NaturalDeduction.Derivation false e L Γ C) :
    NaturalDeduction.Derivation false e L Γ (.neg (.neg C)) := by
  apply NaturalDeduction.Derivation.negIntro
  exact .negElim (p.weaken (Finset.subset_insert _ _)) (.assumption (Finset.mem_insert_self _ _))

def Stable.toClosed {C : Formula L α} (h : Stable e C) :
    NaturalDeduction.Derivation false e L ∅ (.impl (.neg (.neg C)) C) := by
  exact .impIntro (h _ (.assumption (Finset.mem_insert_self _ _)))

def Stable.ofClosed {C : Formula L α}
    (p : NaturalDeduction.Derivation false e L ∅ (.impl (.neg (.neg C)) C)) :
    Stable e C := by
  intro Γ h
  exact .impElim (p.weaken (Finset.empty_subset _)) h

def stableFalsum (e : Bool) : Stable e (.falsum : Formula L α) := by
  intro Γ p
  exact .negElim (.negIntro (.assumption (Finset.mem_insert_self _ _))) p

def stableNegation (e : Bool) (C : Formula L α) : Stable e (.neg C) := by
  intro Γ p
  apply NaturalDeduction.Derivation.negIntro
  exact .negElim (doubleNegIntro (.assumption (Finset.mem_insert_self _ _)))
    (p.weaken (Finset.subset_insert _ _))

def stableConjunction {C D : Formula L α} (hC : Stable e C) (hD : Stable e D) :
    Stable e (.conj C D) := by
  intro Γ p
  have hc : NaturalDeduction.Derivation false e L Γ (.neg (.neg C)) := by
    apply NaturalDeduction.Derivation.negIntro
    have hn : NaturalDeduction.Derivation false e L (insert (.neg C) Γ) (.neg (.conj C D)) := by
      apply NaturalDeduction.Derivation.negIntro
      exact .negElim (.conjElimLeft (.assumption (Finset.mem_insert_self _ _)))
        (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    exact .negElim hn (p.weaken (Finset.subset_insert _ _))
  have hd : NaturalDeduction.Derivation false e L Γ (.neg (.neg D)) := by
    apply NaturalDeduction.Derivation.negIntro
    have hn : NaturalDeduction.Derivation false e L (insert (.neg D) Γ) (.neg (.conj C D)) := by
      apply NaturalDeduction.Derivation.negIntro
      exact .negElim (.conjElimRight (.assumption (Finset.mem_insert_self _ _)))
        (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    exact .negElim hn (p.weaken (Finset.subset_insert _ _))
  exact .conjIntro (hC Γ hc) (hD Γ hd)

def stableImplication (C : Formula L α) {D : Formula L α} (hD : Stable e D) :
    Stable e (.impl C D) := by
  intro Γ p
  apply NaturalDeduction.Derivation.impIntro
  apply hD (insert C Γ)
  apply NaturalDeduction.Derivation.negIntro
  have hn : NaturalDeduction.Derivation false e L (insert (.neg D) (insert C Γ))
      (.neg (.impl C D)) := by
    apply NaturalDeduction.Derivation.negIntro
    exact .negElim (.impElim (.assumption (Finset.mem_insert_self _ _))
      (.assumption (by simp))) (.assumption (by simp))
  exact .negElim hn (p.weaken (by intro F hF; simp [hF]))

def stableUniversal (B : BoundedFormula L α 1) (hB : Stable e B.toFormula) :
    Stable e (.all B) := by
  intro Γ p
  apply NaturalDeduction.Derivation.allIntro
  apply hB (NaturalDeduction.liftContext Γ)
  apply NaturalDeduction.Derivation.negIntro
  let U : Formula L (α ⊕ Fin 1) := .all (B.rename Sum.inl)
  have hn : NaturalDeduction.Derivation false e L
      (insert (.neg B.toFormula) (NaturalDeduction.liftContext Γ)) (.neg U) := by
    apply NaturalDeduction.Derivation.negIntro
    have hu : NaturalDeduction.Derivation false e L
        (insert U (insert (.neg B.toFormula) (NaturalDeduction.liftContext Γ))) B.toFormula := by
      have hp := NaturalDeduction.Derivation.allElim (classical := false) (equality := e) (.var (.inr 0))
        (NaturalDeduction.Derivation.assumption (Γ := insert U
          (insert (.neg B.toFormula) (NaturalDeduction.liftContext Γ)))
          (Finset.mem_insert_self _ _))
      rw [open_instance] at hp
      exact hp
    exact .negElim hu (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hp : NaturalDeduction.Derivation false e L (NaturalDeduction.liftContext Γ)
      (.neg (.neg U)) := by
    have hr := p.rename (Sum.inl : α → α ⊕ Fin 1)
    simpa only [U, NaturalDeduction.liftContext,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using hr
  exact .negElim hn (hp.weaken (Finset.subset_insert _ _))

private def negativeStableAux (e : Bool) : {β : Type a} → (A : Formula L β) → Stable e (negative A)
  | β, A => by
    cases A with
    | falsum => exact stableFalsum e
    | equal s t => exact stableNegation e (.neg (.equal s t))
    | rel R ts => exact stableNegation e (.neg (.rel R ts))
    | neg C => exact stableNegation e (negative C)
    | conj C D => exact stableConjunction (negativeStableAux e C) (negativeStableAux e D)
    | disj C D => exact stableNegation e (.neg (.disj (negative C) (negative D)))
    | impl C D => exact stableImplication (negative C) (negativeStableAux e D)
    | all B =>
        apply stableUniversal (negative B)
        rw [← negative_open]
        exact negativeStableAux e B.toFormula
    | ex B => exact stableNegation e (.neg (.ex (negative B)))
termination_by β A => A.depth
decreasing_by
  all_goals subst_vars
  all_goals simp_all [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map]

def negativeStable (e : Bool) (A : Formula L α) : Stable e (negative A) :=
  negativeStableAux e A

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
