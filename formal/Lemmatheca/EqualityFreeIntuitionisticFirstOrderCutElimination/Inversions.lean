import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Structural

/-! Inversions of actual retained-principal constructive first-order trees. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifocutInversionFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

namespace CutFree
open Lemmatheca.MathematicalLogic.FirstOrderProofs

/-- Collapse only the newest protected free name to a supplied old-language term. -/
def freshSubst (t : L.Term α) : α ⊕ Fin 1 → L.Term α :=
  Sum.elim Term.var (fun _ => t)

theorem rename_substFresh (C : Formula L α) (t : L.Term α) :
    (C.rename (Sum.inl : α → α ⊕ Fin 1)).subst (freshSubst t) = C := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_rename_subst,
    freshSubst, Sum.elim_inl, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_id]

theorem open_substFresh (B : BF L α 1) (t : L.Term α) :
    B.toFormula.subst (freshSubst t) = B.instantiate t := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x <;> rfl

theorem liftContext_substFresh (Γ : Context L α) (t : L.Term α) :
    (liftContext Γ).image (fun A => A.subst (freshSubst t)) = Γ := by
  simp only [liftContext, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
    Finset.image_image, Function.comp_def, rename_substFresh, Finset.image_id']

theorem liftContext_insert (Γ : Context L α) (A : Formula L α) :
    liftContext (insert A Γ) = insert (A.rename Sum.inl) (liftContext Γ) := by
  simp only [liftContext, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
    Finset.image_insert]

theorem instantiate_rename {β : Type w} (B : BF L α 1) (t : L.Term α) (f : α → β) :
    (B.instantiate t).rename f = (B.rename f).instantiate (t.relabel f) := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst, term_subst_vars]

/-- The existential continuation at a supplied term retains only the instance. -/
def instantiateContinuation {Γ : Context L α} {B : BF L α 1} {C : Formula L α}
    (t : L.Term α)
    (r : CoreProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl)) :
    CoreProof L (insert (B.instantiate t) Γ) C := by
  have q := r.substitute (freshSubst t)
  rw [Finset.image_insert, open_substFresh, liftContext_substFresh, rename_substFresh] at q
  exact q
end CutFree

namespace CoreProof
variable {Γ : Context L α} {B D : Formula L α}

/-- Substitute the supplied term for the newest protected name. -/
def instantiateFresh {B : BF L α 1} (t : L.Term α)
    (p : CoreProof L (liftContext Γ) B.toFormula) :
    CoreProof L Γ (B.instantiate t) := by
  have q := p.substitute (CutFree.freshSubst t)
  rw [CutFree.liftContext_substFresh, CutFree.open_substFresh] at q
  exact q

private def invertConjAux {α : Type w} {Γ : Context L α} {E : Formula L α}
    (p : CoreProof L Γ E) : ∀ B D : Formula L α,
      E = .conj B D → CoreProof L Γ B × CoreProof L Γ D := by
  induction p with
  | relation _ _ _ => intro B D he; cases he
  | falsumLeft hm => intro B D _; exact ⟨.falsumLeft hm, .falsumLeft hm⟩
  | conjLeft hm _ ih =>
      intro B D he
      have q := ih B D he
      exact ⟨.conjLeft hm q.1, .conjLeft hm q.2⟩
  | conjRight p q _ _ => intro B D he; cases he; exact ⟨p, q⟩
  | disjLeft hm _ _ ihp ihq =>
      intro B D he
      have p := ihp B D he
      have q := ihq B D he
      exact ⟨.disjLeft hm p.1 q.1, .disjLeft hm p.2 q.2⟩
  | disjRightLeft _ _ => intro B D he; cases he
  | disjRightRight _ _ => intro B D he; cases he
  | implLeft hm p _ _ ih =>
      intro B D he
      have q := ih B D he
      exact ⟨.implLeft hm p q.1, .implLeft hm p q.2⟩
  | implRight _ _ => intro B D he; cases he
  | negLeft hm p _ => intro B D _; exact ⟨.negLeft hm p, .negLeft hm p⟩
  | negRight _ _ => intro B D he; cases he
  | allLeft t hm _ ih =>
      intro B D he
      have q := ih B D he
      exact ⟨.allLeft t hm q.1, .allLeft t hm q.2⟩
  | allRight _ _ => intro B D he; cases he
  | @exLeft α Γ E A hm _ ih =>
      intro B D he
      subst E
      have q := ih (B.rename Sum.inl) (D.rename Sum.inl) rfl
      exact ⟨.exLeft hm q.1, .exLeft hm q.2⟩
  | exRight _ _ _ => intro B D he; cases he

private def invertImplAux {α : Type w} {Γ : Context L α} {E : Formula L α}
    (p : CoreProof L Γ E) : ∀ B D : Formula L α,
      E = .impl B D → CoreProof L (insert B Γ) D := by
  induction p with
  | relation _ _ _ => intro B D he; cases he
  | falsumLeft hm => intro B D _; exact .falsumLeft (Finset.mem_insert_of_mem hm)
  | conjLeft hm _ ih =>
      intro B D he
      exact .conjLeft (Finset.mem_insert_of_mem hm)
        (by simpa only [Finset.insert_comm] using ih B D he)
  | conjRight _ _ _ _ => intro B D he; cases he
  | disjLeft hm _ _ ihp ihq =>
      intro B D he
      exact .disjLeft (Finset.mem_insert_of_mem hm)
        (by simpa only [Finset.insert_comm] using ihp B D he)
        (by simpa only [Finset.insert_comm] using ihq B D he)
  | disjRightLeft _ _ => intro B D he; cases he
  | disjRightRight _ _ => intro B D he; cases he
  | implLeft hm p _ _ ih =>
      intro B D he
      exact .implLeft (Finset.mem_insert_of_mem hm) (p.weaken (Finset.subset_insert _ _))
        (by simpa only [Finset.insert_comm] using ih B D he)
  | implRight p _ => intro B D he; cases he; exact p
  | negLeft hm p _ =>
      intro B D _
      exact .negLeft (Finset.mem_insert_of_mem hm) (p.weaken (Finset.subset_insert _ _))
  | negRight _ _ => intro B D he; cases he
  | allLeft t hm _ ih =>
      intro B D he
      exact .allLeft t (Finset.mem_insert_of_mem hm)
        (by simpa only [Finset.insert_comm] using ih B D he)
  | allRight _ _ => intro B D he; cases he
  | @exLeft α Γ E A hm _ ih =>
      intro B D he
      subst E
      apply CoreProof.exLeft (Finset.mem_insert_of_mem hm)
      simpa only [CutFree.liftContext_insert, Finset.insert_comm] using
        ih (B.rename Sum.inl) (D.rename Sum.inl) rfl
  | exRight _ _ _ => intro B D he; cases he

private def invertNegAux {α : Type w} {Γ : Context L α} {E : Formula L α}
    (p : CoreProof L Γ E) : ∀ B : Formula L α,
      E = .neg B → CoreProof L (insert B Γ) .falsum := by
  induction p with
  | relation _ _ _ => intro B he; cases he
  | falsumLeft hm => intro B _; exact .falsumLeft (Finset.mem_insert_of_mem hm)
  | conjLeft hm _ ih =>
      intro B he
      exact .conjLeft (Finset.mem_insert_of_mem hm)
        (by simpa only [Finset.insert_comm] using ih B he)
  | conjRight _ _ _ _ => intro B he; cases he
  | disjLeft hm _ _ ihp ihq =>
      intro B he
      exact .disjLeft (Finset.mem_insert_of_mem hm)
        (by simpa only [Finset.insert_comm] using ihp B he)
        (by simpa only [Finset.insert_comm] using ihq B he)
  | disjRightLeft _ _ => intro B he; cases he
  | disjRightRight _ _ => intro B he; cases he
  | implLeft hm p _ _ ih =>
      intro B he
      exact .implLeft (Finset.mem_insert_of_mem hm) (p.weaken (Finset.subset_insert _ _))
        (by simpa only [Finset.insert_comm] using ih B he)
  | implRight _ _ => intro B he; cases he
  | negLeft hm p _ =>
      intro B _
      exact .negLeft (Finset.mem_insert_of_mem hm) (p.weaken (Finset.subset_insert _ _))
  | negRight p _ => intro B he; cases he; exact p
  | allLeft t hm _ ih =>
      intro B he
      exact .allLeft t (Finset.mem_insert_of_mem hm)
        (by simpa only [Finset.insert_comm] using ih B he)
  | allRight _ _ => intro B he; cases he
  | @exLeft α Γ E A hm _ ih =>
      intro B he
      subst E
      apply CoreProof.exLeft (Finset.mem_insert_of_mem hm)
      simpa only [CutFree.liftContext_insert, Finset.insert_comm,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] using
        ih (B.rename Sum.inl) rfl
  | exRight _ _ _ => intro B he; cases he

private def invertAllAux {α : Type w} {Γ : Context L α} {E : Formula L α}
    (p : CoreProof L Γ E) : ∀ (B : BF L α 1) (t : L.Term α),
      E = .all B → CoreProof L Γ (B.instantiate t) := by
  induction p with
  | relation _ _ _ => intro B t he; cases he
  | falsumLeft hm => intro B t _; exact .falsumLeft hm
  | conjLeft hm _ ih => intro B t he; exact .conjLeft hm (ih B t he)
  | conjRight _ _ _ _ => intro B t he; cases he
  | disjLeft hm _ _ ihp ihq =>
      intro B t he
      exact .disjLeft hm (ihp B t he) (ihq B t he)
  | disjRightLeft _ _ => intro B t he; cases he
  | disjRightRight _ _ => intro B t he; cases he
  | implLeft hm p _ _ ih => intro B t he; exact .implLeft hm p (ih B t he)
  | implRight _ _ => intro B t he; cases he
  | negLeft hm p _ => intro B t _; exact .negLeft hm p
  | negRight _ _ => intro B t he; cases he
  | allLeft t' hm _ ih => intro B t he; exact .allLeft t' hm (ih B t he)
  | allRight p _ => intro B t he; cases he; exact p.instantiateFresh t
  | @exLeft α Γ E A hm _ ih =>
      intro B t he
      subst E
      apply CoreProof.exLeft hm
      rw [CutFree.instantiate_rename]
      exact ih (B.rename Sum.inl) (t.relabel Sum.inl)
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all B
          (fun x => .var (Sum.inl x)))
  | exRight _ _ _ => intro B t he; cases he

def invertConj (p : CoreProof L Γ (.conj B D)) :
    CoreProof L Γ B × CoreProof L Γ D := invertConjAux p B D rfl

def invertImpl (p : CoreProof L Γ (.impl B D)) :
    CoreProof L (insert B Γ) D := invertImplAux p B D rfl

def invertNeg (p : CoreProof L Γ (.neg B)) :
    CoreProof L (insert B Γ) .falsum := invertNegAux p B rfl

/-- Universal inversion requires an actual supplied term, even over no free names. -/
def invertAll {B : BF L α 1} (t : L.Term α)
    (p : CoreProof L Γ (.all B)) : CoreProof L Γ (B.instantiate t) := invertAllAux p B t rfl

end CoreProof

namespace CutFree
/-- Keep a continuation's protected name newest while adding a different old name. -/
def liftOldName (α : Type w) : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 :=
  Sum.elim (fun x => .inl (.inl x)) Sum.inr

theorem opening_liftOldName (B : BF L α 1) :
    B.toFormula.rename (liftOldName α) =
      (B.rename (Sum.inl : α → α ⊕ Fin 1)).toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x <;> rfl

/-- Transport the actual existential continuation across the producer's distinct tag. -/
def liftContinuation {Γ : Context L α} {C : Formula L α} {B D : BF L α 1}
    (r : CoreProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl)) :
    CoreProof L
      (insert (B.rename (Sum.inl : α → α ⊕ Fin 1)).toFormula
        (liftContext (insert D.toFormula (liftContext Γ))))
      ((C.rename (Sum.inl : α → α ⊕ Fin 1)).rename Sum.inl) := by
  have q := r.rename (liftOldName α)
  have hΓ : (liftContext Γ).image (fun A => A.rename (liftOldName α)) =
      liftContext (liftContext Γ) := by
    simp only [liftContext, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
      Finset.image_image, Function.comp_def,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename_comp,
      liftOldName, Sum.elim_inl]
  have hC : (C.rename (Sum.inl : α → α ⊕ Fin 1)).rename (liftOldName α) =
      (C.rename (Sum.inl : α → α ⊕ Fin 1)).rename Sum.inl := by
    simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename_comp,
      Function.comp_def, liftOldName, Sum.elim_inl]
  rw [Finset.image_insert, opening_liftOldName, hΓ, hC] at q
  rw [liftContext_insert]
  exact q.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))

end CutFree
end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
