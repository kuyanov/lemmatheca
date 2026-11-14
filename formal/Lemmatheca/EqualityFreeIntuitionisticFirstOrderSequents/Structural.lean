import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Calculus

namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u,v}} {α β : Type w}
noncomputable section
local instance ifoqStructuralFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _


/-- Opening a one-slot body is its instance at the protected fresh variable. -/
theorem instantiate_fresh (B : BF L α 1) :
    (B.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl

namespace CoreProof
private def substituteWithHeight {Γ : Context L α} {A : Formula L α}
    (p : CoreProof L Γ A) (σ : α → L.Term β) :
    {q : CoreProof L (Γ.image (fun B => B.subst σ)) (A.subst σ) // q.height = p.height} := by
  revert β
  induction p with
  | relation R ts hm =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_rel]
      exact ⟨.relation R _ (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_rel R ts σ⟩), rfl⟩
  | falsumLeft hm =>
      intro β σ
      exact ⟨.falsumLeft (Finset.mem_image.mpr ⟨_, hm, rfl⟩), rfl⟩
  | conjLeft hm _ ih =>
      intro β σ
      have h := ih σ
      rw [Finset.image_insert, Finset.image_insert] at h
      exact ⟨.conjLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj _ _ _⟩) h.1,
        by simp only [height, h.2]⟩
  | conjRight _ _ ihp ihq =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj]
      exact ⟨.conjRight (ihp σ).1 (ihq σ).1, by simp only [height, (ihp σ).2, (ihq σ).2]⟩
  | disjLeft hm _ _ ihp ihq =>
      intro β σ
      have p := ihp σ
      have q := ihq σ
      rw [Finset.image_insert] at p q
      exact ⟨.disjLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj _ _ _⟩) p.1 q.1,
        by simp only [height, p.2, q.2]⟩
  | disjRightLeft _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]
      exact ⟨.disjRightLeft (ih σ).1, by simp only [height, (ih σ).2]⟩
  | disjRightRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]
      exact ⟨.disjRightRight (ih σ).1, by simp only [height, (ih σ).2]⟩
  | implLeft hm _ _ ihp ihq =>
      intro β σ
      have q := ihq σ
      rw [Finset.image_insert] at q
      exact ⟨.implLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl _ _ _⟩) (ihp σ).1 q.1,
        congrArg (1 + ·) (congrArg₂ max (ihp σ).2 q.2)⟩
  | implRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl]
      have p := ih σ
      rw [Finset.image_insert] at p
      exact ⟨.implRight p.1, congrArg (1 + ·) p.2⟩
  | negLeft hm _ ih =>
      intro β σ
      exact ⟨.negLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg _ _⟩) (ih σ).1,
        by simp only [height, (ih σ).2]⟩
  | negRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg]
      have p := ih σ
      rw [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] at p
      exact ⟨.negRight p.1, congrArg (1 + ·) p.2⟩
  | allLeft t hm _ ih =>
      intro β σ
      have p := ih σ
      rw [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] at p
      exact ⟨.allLeft (t.subst σ) (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all _ _⟩) p.1,
        congrArg (1 + ·) p.2⟩
  | allRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all]
      have p := ih (liftSubst σ 1)
      rw [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext_subst, ← Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst] at p
      exact ⟨.allRight p.1, congrArg (1 + ·) p.2⟩
  | @exLeft α Γ C B hm _ ih =>
      intro β σ
      have p := ih (liftSubst σ 1)
      rw [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext_subst, ← Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst] at p
      have he : (C.rename Sum.inl).subst (liftSubst σ 1) = (C.subst σ).rename Sum.inl := by
        simp only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_rename_subst, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_subst_rename,
          liftSubst, Sum.elim_inl]
      rw [he] at p
      exact ⟨.exLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex _ _⟩) p.1,
        congrArg (1 + ·) p.2⟩
  | exRight t _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex]
      have p := ih σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] at p
      exact ⟨.exRight (t.subst σ) p.1, congrArg (1 + ·) p.2⟩


private def weakenWithHeight {Γ Δ : Context L α} {A : Formula L α}
    (p : CoreProof L Γ A) (h : Γ ⊆ Δ) : {q : CoreProof L Δ A // q.height = p.height} := by
  revert Δ
  induction p with
  | relation R ts hm => intro Δ hs; exact ⟨.relation R ts (hs hm), rfl⟩
  | falsumLeft hm => intro Δ hs; exact ⟨.falsumLeft (hs hm), rfl⟩
  | conjLeft hm _ ih =>
      intro Δ hs
      obtain ⟨q, hq⟩ := ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs))
      exact ⟨.conjLeft (hs hm) q, by simpa only [height] using congrArg (1 + ·) hq⟩
  | conjRight _ _ ihp ihq =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ihp hs
      obtain ⟨q, hq⟩ := ihq hs
      exact ⟨.conjRight p q, by simp only [height, hp, hq]⟩
  | disjLeft hm _ _ ihp ihq =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ihp (Finset.insert_subset_insert _ hs)
      obtain ⟨q, hq⟩ := ihq (Finset.insert_subset_insert _ hs)
      exact ⟨.disjLeft (hs hm) p q, by simp only [height, hp, hq]⟩
  | disjRightLeft _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.disjRightLeft p, by simp only [height, hp]⟩
  | disjRightRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.disjRightRight p, by simp only [height, hp]⟩
  | implLeft hm _ _ ihp ihq =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ihp hs
      obtain ⟨q, hq⟩ := ihq (Finset.insert_subset_insert _ hs)
      exact ⟨.implLeft (hs hm) p q, by simp only [height, hp, hq]⟩
  | implRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ hs)
      exact ⟨.implRight p, by simp only [height, hp]⟩
  | negLeft hm _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.negLeft (hs hm) p, by simp only [height, hp]⟩
  | negRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ hs)
      exact ⟨.negRight p, by simp only [height, hp]⟩
  | allLeft t hm _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ hs)
      exact ⟨.allLeft t (hs hm) p, by simp only [height, hp]⟩
  | allRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.image_subset_image hs)
      exact ⟨.allRight p, congrArg (1 + ·) hp⟩
  | exLeft hm _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ (Finset.image_subset_image hs))
      exact ⟨.exLeft (hs hm) p, congrArg (1 + ·) hp⟩
  | exRight t _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.exRight t p, by simp only [height, hp]⟩
/-- Expansion of compound identity into the primitive cut-free rules. -/
def identity {α : Type w} {Γ : Context L α} (A : Formula L α) (hA : A.EqualityFree) (hmem : A ∈ Γ) :
    CoreProof L Γ A := by
  cases A with
  | falsum => exact .falsumLeft hmem
  | equal s t => exact False.elim hA
  | rel R ts => exact .relation R ts hmem
  | conj A B =>
      exact .conjLeft hmem (.conjRight
        (identity A hA.1 (Finset.mem_insert_self _ _))
        (identity B hA.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  | disj A B =>
      exact .disjLeft hmem
        (.disjRightLeft (identity A hA.1 (Finset.mem_insert_self _ _)))
        (.disjRightRight (identity B hA.2 (Finset.mem_insert_self _ _)))
  | impl A B =>
      exact .implRight (.implLeft (Finset.mem_insert_of_mem hmem)
        (identity A hA.1 (Finset.mem_insert_self _ _))
        (identity B hA.2 (Finset.mem_insert_self _ _)))
  | neg A =>
      exact .negRight (.negLeft (Finset.mem_insert_of_mem hmem)
        (identity A hA (Finset.mem_insert_self _ _)))
  | all B =>
      apply CoreProof.allRight
      have hm : (.all (B.rename Sum.inl)) ∈ liftContext Γ := by
        refine Finset.mem_image.mpr ⟨.all B, hmem, ?_⟩
        exact Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all B (fun x => .var (Sum.inl x))
      apply CoreProof.allLeft (.var (.inr 0)) hm
      simpa only [instantiate_fresh] using
        identity B.toFormula ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hA)
          (Finset.mem_insert_self B.toFormula (liftContext Γ))
  | ex B =>
      apply CoreProof.exLeft hmem
      have q := CoreProof.exRight (B := B.rename (Sum.inl : α → α ⊕ Fin 1))
        (.var (.inr 0)) (by
          rw [instantiate_fresh]
          exact identity B.toFormula ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hA)
            (Finset.mem_insert_self B.toFormula (liftContext Γ)))
      simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using q
termination_by A.depth
decreasing_by all_goals simp_all [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map]


private def explodeAux {α : Type w} {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ C) : C = .falsum → ∀ A : Formula L α, CoreProof L Γ A := by
  induction p with
  | relation _ _ _ => intro he; cases he
  | falsumLeft hm => intro _ A; exact .falsumLeft hm
  | conjLeft hm _ ih => intro he A; exact .conjLeft hm (ih he A)
  | conjRight _ _ _ _ => intro he; cases he
  | disjLeft hm _ _ ihp ihq => intro he A; exact .disjLeft hm (ihp he A) (ihq he A)
  | disjRightLeft _ _ => intro he; cases he
  | disjRightRight _ _ => intro he; cases he
  | implLeft hm p _ _ ih => intro he A; exact .implLeft hm p (ih he A)
  | implRight _ _ => intro he; cases he
  | negLeft hm p _ => intro _ A; exact .negLeft hm p
  | negRight _ _ => intro he; cases he
  | allLeft t hm _ ih => intro he A; exact .allLeft t hm (ih he A)
  | allRight _ _ => intro he; cases he
  | @exLeft α Γ C B hm _ ih =>
      intro he A
      subst C
      exact .exLeft hm (ih rfl (A.rename Sum.inl))
  | exRight _ _ _ => intro he; cases he

/-- Transform a falsum tree by rebuilding its final inference. -/
def explode {α : Type w} {Γ : Context L α} (p : CoreProof L Γ .falsum)
    (A : Formula L α) : CoreProof L Γ A := explodeAux p rfl A


variable {Γ Δ : Context L α} {A : Formula L α}

def weaken (p : CoreProof L Γ A) (h : Γ ⊆ Δ) : CoreProof L Δ A :=
  (weakenWithHeight p h).1

theorem weaken_height (p : CoreProof L Γ A) (h : Γ ⊆ Δ) :
    (p.weaken h).height = p.height :=
  (weakenWithHeight p h).2



def substitute (p : CoreProof L Γ A) (σ : α → L.Term β) :
    CoreProof L (Γ.image (fun B => B.subst σ)) (A.subst σ) :=
  (substituteWithHeight p σ).1

theorem substitute_height (p : CoreProof L Γ A) (σ : α → L.Term β) :
    (p.substitute σ).height = p.height :=
  (substituteWithHeight p σ).2

def rename (p : CoreProof L Γ A) (f : α → β) :
    CoreProof L (Γ.image (fun B => B.rename f)) (A.rename f) :=
  p.substitute (fun x => .var (f x))

theorem rename_height (p : CoreProof L Γ A) (f : α → β) :
    (p.rename f).height = p.height :=
  p.substitute_height (fun x => .var (f x))


end CoreProof

namespace CutProof
private def substituteWithHeight {Γ : Context L α} {A : Formula L α}
    (p : CutProof L Γ A) (σ : α → L.Term β) :
    {q : CutProof L (Γ.image (fun B => B.subst σ)) (A.subst σ) // q.height = p.height} := by
  revert β
  induction p with
  | relation R ts hm =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_rel]
      exact ⟨.relation R _ (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_rel R ts σ⟩), rfl⟩
  | falsumLeft hm =>
      intro β σ
      exact ⟨.falsumLeft (Finset.mem_image.mpr ⟨_, hm, rfl⟩), rfl⟩
  | conjLeft hm _ ih =>
      intro β σ
      have h := ih σ
      rw [Finset.image_insert, Finset.image_insert] at h
      exact ⟨.conjLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj _ _ _⟩) h.1,
        by simp only [height, h.2]⟩
  | conjRight _ _ ihp ihq =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_conj]
      exact ⟨.conjRight (ihp σ).1 (ihq σ).1, by simp only [height, (ihp σ).2, (ihq σ).2]⟩
  | disjLeft hm _ _ ihp ihq =>
      intro β σ
      have p := ihp σ
      have q := ihq σ
      rw [Finset.image_insert] at p q
      exact ⟨.disjLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj _ _ _⟩) p.1 q.1,
        by simp only [height, p.2, q.2]⟩
  | disjRightLeft _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]
      exact ⟨.disjRightLeft (ih σ).1, by simp only [height, (ih σ).2]⟩
  | disjRightRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj]
      exact ⟨.disjRightRight (ih σ).1, by simp only [height, (ih σ).2]⟩
  | implLeft hm _ _ ihp ihq =>
      intro β σ
      have q := ihq σ
      rw [Finset.image_insert] at q
      exact ⟨.implLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl _ _ _⟩) (ihp σ).1 q.1,
        congrArg (1 + ·) (congrArg₂ max (ihp σ).2 q.2)⟩
  | implRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl]
      have p := ih σ
      rw [Finset.image_insert] at p
      exact ⟨.implRight p.1, congrArg (1 + ·) p.2⟩
  | negLeft hm _ ih =>
      intro β σ
      exact ⟨.negLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg _ _⟩) (ih σ).1,
        by simp only [height, (ih σ).2]⟩
  | negRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_neg]
      have p := ih σ
      rw [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] at p
      exact ⟨.negRight p.1, congrArg (1 + ·) p.2⟩
  | allLeft t hm _ ih =>
      intro β σ
      have p := ih σ
      rw [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] at p
      exact ⟨.allLeft (t.subst σ) (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all _ _⟩) p.1,
        congrArg (1 + ·) p.2⟩
  | allRight _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all]
      have p := ih (liftSubst σ 1)
      rw [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext_subst, ← Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst] at p
      exact ⟨.allRight p.1, congrArg (1 + ·) p.2⟩
  | @exLeft α Γ C B hm _ ih =>
      intro β σ
      have p := ih (liftSubst σ 1)
      rw [Finset.image_insert, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext_subst, ← Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula_subst] at p
      have he : (C.rename Sum.inl).subst (liftSubst σ 1) = (C.subst σ).rename Sum.inl := by
        simp only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_rename_subst, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_subst_rename,
          liftSubst, Sum.elim_inl]
      rw [he] at p
      exact ⟨.exLeft (Finset.mem_image.mpr ⟨_, hm, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex _ _⟩) p.1,
        congrArg (1 + ·) p.2⟩
  | exRight t _ ih =>
      intro β σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex]
      have p := ih σ
      rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst] at p
      exact ⟨.exRight (t.subst σ) p.1, congrArg (1 + ·) p.2⟩
  | cut hB _ _ ihp ihq =>
      intro β σ
      have q := ihq σ
      rw [Finset.image_insert] at q
      rw [Finset.image_union]
      exact ⟨.cut ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hB) (ihp σ).1 q.1,
        congrArg (1 + ·) (congrArg₂ max (ihp σ).2 q.2)⟩


private def weakenWithHeight {Γ Δ : Context L α} {A : Formula L α}
    (p : CutProof L Γ A) (h : Γ ⊆ Δ) : {q : CutProof L Δ A // q.height = p.height} := by
  revert Δ
  induction p with
  | relation R ts hm => intro Δ hs; exact ⟨.relation R ts (hs hm), rfl⟩
  | falsumLeft hm => intro Δ hs; exact ⟨.falsumLeft (hs hm), rfl⟩
  | conjLeft hm _ ih =>
      intro Δ hs
      obtain ⟨q, hq⟩ := ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs))
      exact ⟨.conjLeft (hs hm) q, by simpa only [height] using congrArg (1 + ·) hq⟩
  | conjRight _ _ ihp ihq =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ihp hs
      obtain ⟨q, hq⟩ := ihq hs
      exact ⟨.conjRight p q, by simp only [height, hp, hq]⟩
  | disjLeft hm _ _ ihp ihq =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ihp (Finset.insert_subset_insert _ hs)
      obtain ⟨q, hq⟩ := ihq (Finset.insert_subset_insert _ hs)
      exact ⟨.disjLeft (hs hm) p q, by simp only [height, hp, hq]⟩
  | disjRightLeft _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.disjRightLeft p, by simp only [height, hp]⟩
  | disjRightRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.disjRightRight p, by simp only [height, hp]⟩
  | implLeft hm _ _ ihp ihq =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ihp hs
      obtain ⟨q, hq⟩ := ihq (Finset.insert_subset_insert _ hs)
      exact ⟨.implLeft (hs hm) p q, by simp only [height, hp, hq]⟩
  | implRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ hs)
      exact ⟨.implRight p, by simp only [height, hp]⟩
  | negLeft hm _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.negLeft (hs hm) p, by simp only [height, hp]⟩
  | negRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ hs)
      exact ⟨.negRight p, by simp only [height, hp]⟩
  | allLeft t hm _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ hs)
      exact ⟨.allLeft t (hs hm) p, by simp only [height, hp]⟩
  | allRight _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.image_subset_image hs)
      exact ⟨.allRight p, congrArg (1 + ·) hp⟩
  | exLeft hm _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih (Finset.insert_subset_insert _ (Finset.image_subset_image hs))
      exact ⟨.exLeft (hs hm) p, congrArg (1 + ·) hp⟩
  | exRight t _ ih =>
      intro Δ hs
      obtain ⟨p, hp⟩ := ih hs
      exact ⟨.exRight t p, by simp only [height, hp]⟩
  | @cut α Γ Δ B A hB p₀ q₀ ihp ihq =>
      intro Θ hs
      obtain ⟨p, hp⟩ := ihp (fun _ hm => hs (Finset.mem_union_left _ hm))
      obtain ⟨q, hq⟩ := ihq (Finset.insert_subset_insert _
        (fun _ hm => hs (Finset.mem_union_right _ hm)))
      have out : {r : CutProof L (Θ ∪ Θ) A // r.height = 1 + max p₀.height q₀.height} :=
        ⟨.cut hB p q, by simp only [height, hp, hq]⟩
      have hctx : Θ ∪ Θ = Θ := Finset.union_self Θ
      rw [hctx] at out
      exact out
variable {Γ Δ : Context L α} {A : Formula L α}

def weaken (p : CutProof L Γ A) (h : Γ ⊆ Δ) : CutProof L Δ A :=
  (weakenWithHeight p h).1

theorem weaken_height (p : CutProof L Γ A) (h : Γ ⊆ Δ) :
    (p.weaken h).height = p.height :=
  (weakenWithHeight p h).2



def substitute (p : CutProof L Γ A) (σ : α → L.Term β) :
    CutProof L (Γ.image (fun B => B.subst σ)) (A.subst σ) :=
  (substituteWithHeight p σ).1

theorem substitute_height (p : CutProof L Γ A) (σ : α → L.Term β) :
    (p.substitute σ).height = p.height :=
  (substituteWithHeight p σ).2

def rename (p : CutProof L Γ A) (f : α → β) :
    CutProof L (Γ.image (fun B => B.rename f)) (A.rename f) :=
  p.substitute (fun x => .var (f x))

theorem rename_height (p : CutProof L Γ A) (f : α → β) :
    (p.rename f).height = p.height :=
  p.substitute_height (fun x => .var (f x))

/-- Include a cut-free tree by copying its primitive rules. -/
def ofCore (p : CoreProof L Γ A) : CutProof L Γ A := by
  clear Δ
  induction p with
  | relation R ts hm => exact .relation R ts hm
  | falsumLeft hm => exact .falsumLeft hm
  | conjLeft hm _ ih => exact .conjLeft hm ih
  | conjRight _ _ ihp ihq => exact .conjRight ihp ihq
  | disjLeft hm _ _ ihp ihq => exact .disjLeft hm ihp ihq
  | disjRightLeft _ ih => exact .disjRightLeft ih
  | disjRightRight _ ih => exact .disjRightRight ih
  | implLeft hm _ _ ihp ihq => exact .implLeft hm ihp ihq
  | implRight _ ih => exact .implRight ih
  | negLeft hm _ ih => exact .negLeft hm ih
  | negRight _ ih => exact .negRight ih
  | allLeft t hm _ ih => exact .allLeft t hm ih
  | allRight _ ih => exact .allRight ih
  | exLeft hm _ ih => exact .exLeft hm ih
  | exRight t _ ih => exact .exRight t ih

theorem ofCore_height (p : CoreProof L Γ A) : (ofCore p).height = p.height := by
  induction p <;> simp_all only [ofCore, CoreProof.height, height]

end CutProof

namespace RawProof
variable {Γ Δ : Context L α} {A : Formula L α}

def weaken (p : RawProof L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) : RawProof L Δ A :=
  ⟨p.tree.weaken h, hΔ, p.conclusion_pure⟩

theorem weaken_height (p : RawProof L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) :
    (p.weaken h hΔ).tree.height = p.tree.height :=
  p.tree.weaken_height h

def substitute (p : RawProof L Γ A) (σ : α → L.Term β) :
    RawProof L (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  refine ⟨p.tree.substitute σ, ?_, (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr p.conclusion_pure⟩
  intro B hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr (p.context_pure C hC)

theorem substitute_height (p : RawProof L Γ A) (σ : α → L.Term β) :
    (p.substitute σ).tree.height = p.tree.height :=
  p.tree.substitute_height σ

def rename (p : RawProof L Γ A) (f : α → β) :
    RawProof L (Γ.image (fun B => B.rename f)) (A.rename f) :=
  p.substitute (fun x => .var (f x))

theorem rename_height (p : RawProof L Γ A) (f : α → β) :
    (p.rename f).tree.height = p.tree.height :=
  p.substitute_height (fun x => .var (f x))

def identity (A : Formula L α) (hΓ : ContextPure Γ) (hA : A.EqualityFree)
    (hmem : A ∈ Γ) : RawProof L Γ A :=
  ⟨CoreProof.identity A hA hmem, hΓ, hA⟩

def explode (p : RawProof L Γ .falsum) (A : Formula L α) (hA : A.EqualityFree) :
    RawProof L Γ A :=
  ⟨p.tree.explode A, p.context_pure, hA⟩

def toCut (p : RawProof L Γ A) : RawCutProof L Γ A :=
  ⟨CutProof.ofCore p.tree, p.context_pure, p.conclusion_pure⟩

end RawProof

namespace RawCutProof
variable {Γ Δ : Context L α} {A : Formula L α}

def weaken (p : RawCutProof L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) : RawCutProof L Δ A :=
  ⟨p.tree.weaken h, hΔ, p.conclusion_pure⟩

theorem weaken_height (p : RawCutProof L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) :
    (p.weaken h hΔ).tree.height = p.tree.height :=
  p.tree.weaken_height h

def substitute (p : RawCutProof L Γ A) (σ : α → L.Term β) :
    RawCutProof L (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  refine ⟨p.tree.substitute σ, ?_, (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr p.conclusion_pure⟩
  intro B hB
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
  exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr (p.context_pure C hC)

theorem substitute_height (p : RawCutProof L Γ A) (σ : α → L.Term β) :
    (p.substitute σ).tree.height = p.tree.height :=
  p.tree.substitute_height σ

def rename (p : RawCutProof L Γ A) (f : α → β) :
    RawCutProof L (Γ.image (fun B => B.rename f)) (A.rename f) :=
  p.substitute (fun x => .var (f x))

theorem rename_height (p : RawCutProof L Γ A) (f : α → β) :
    (p.rename f).tree.height = p.tree.height :=
  p.substitute_height (fun x => .var (f x))

end RawCutProof

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
