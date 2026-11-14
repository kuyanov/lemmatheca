import Lemmatheca.EqualityFreeIntuitionisticFirstOrderCutElimination.Inversions

/-! Rank-uniform principal operations and generalized cut-free replacement. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifocutReplacementFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

namespace CutFree
/-- The actual generalized replacement operation with its context inclusion. -/
abbrev Replacement (A : Formula L α) : Type max u v (w+1) :=
  ∀ {Γ Δ : Context L α} {C : Formula L α},
    CoreProof L Γ A → CoreProof L Δ C → Δ ⊆ insert A Γ → CoreProof L Γ C

/-- Smaller replacements are available over every name type at the fixed universe. -/
abbrev SmallerReplacements (L : Language.{u,v}) (rank : ℕ) : Type max u v (w+1) :=
  ∀ {δ : Type w} (A : Formula L δ), A.EqualityFree → A.depth < rank → Replacement A

/-- Principal cases at one cut depth, uniformly over all protected extensions. -/
structure PrincipalReducers (L : Language.{u,v}) (rank : ℕ) where
  conjunction : ∀ {δ : Type w} {Γ : Context L δ} {B D C : Formula L δ},
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.conj B D).depth = rank → B.EqualityFree → D.EqualityFree →
    CoreProof L Γ (.conj B D) → CoreProof L (insert B (insert D Γ)) C → CoreProof L Γ C
  disjunction : ∀ {δ : Type w} {Γ : Context L δ} {B D C : Formula L δ},
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.disj B D).depth = rank → B.EqualityFree → D.EqualityFree →
    CoreProof L Γ (.disj B D) → CoreProof L (insert B Γ) C →
    CoreProof L (insert D Γ) C → CoreProof L Γ C
  implication : ∀ {δ : Type w} {Γ : Context L δ} {B D C : Formula L δ},
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.impl B D).depth = rank → B.EqualityFree → D.EqualityFree →
    CoreProof L Γ (.impl B D) → CoreProof L Γ B →
    CoreProof L (insert D Γ) C → CoreProof L Γ C
  negation : ∀ {δ : Type w} {Γ : Context L δ} {B C : Formula L δ},
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.neg B).depth = rank → B.EqualityFree →
    CoreProof L Γ (.neg B) → CoreProof L Γ B → CoreProof L Γ C
  universal : ∀ {δ : Type w} {Γ : Context L δ} {B : BF L δ 1} {C : Formula L δ},
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all B).depth = rank → B.EqualityFree → (t : L.Term δ) →
    CoreProof L Γ (.all B) → CoreProof L (insert (B.instantiate t) Γ) C → CoreProof L Γ C
  existential : ∀ {δ : Type w} {Γ : Context L δ} {B : BF L δ 1} {C : Formula L δ},
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex B).depth = rank → B.EqualityFree →
    CoreProof L Γ (.ex B) →
    CoreProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl) → CoreProof L Γ C

private theorem augment {Γ Δ : Context L α} {A X : Formula L α}
    (h : Δ ⊆ insert A Γ) : insert X Δ ⊆ insert A (insert X Γ) := by
  simpa only [Finset.insert_comm] using Finset.insert_subset_insert X h

private theorem augmentTwo {Γ Δ : Context L α} {A X Y : Formula L α}
    (h : Δ ⊆ insert A Γ) :
    insert X (insert Y Δ) ⊆ insert A (insert X (insert Y Γ)) := by
  simpa only [Finset.insert_comm] using
    Finset.insert_subset_insert X (Finset.insert_subset_insert Y h)

private theorem subsetTwo (Γ : Context L α) (X Y : Formula L α) :
    Γ ⊆ insert X (insert Y Γ) :=
  (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

private theorem liftInclusion {Γ Δ : Context L α} {A : Formula L α}
    (h : Δ ⊆ insert A Γ) : liftContext Δ ⊆ insert (A.rename Sum.inl) (liftContext Γ) := by
  simpa only [liftContext, Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
    Finset.image_insert] using
    (Finset.image_subset_image (f := fun C : Formula L α => C.rename
      (Sum.inl : α → α ⊕ Fin 1)) h)

private def pasteAux {rank : ℕ} (reducers : PrincipalReducers.{u,v,w} L rank)
    {α : Type w} {Δ : Context L α} {C : Formula L α} (q : CoreProof L Δ C) :
    ∀ (A : Formula L α), A.EqualityFree → A.depth = rank →
      ∀ {Γ : Context L α}, CoreProof L Γ A → Δ ⊆ insert A Γ → CoreProof L Γ C := by
  induction q with
  | relation R ts hm =>
      intro A hA hdepth Γ p hΔ
      by_cases he : (.rel R ts) = A
      · cases he; exact p
      · exact .relation R ts ((Finset.mem_insert.mp (hΔ hm)).resolve_left he)
  | falsumLeft hm =>
      intro A hA hdepth Γ p hΔ
      by_cases hb : (.falsum : Formula L _) ∈ Γ
      · exact .falsumLeft hb
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hb
        subst A
        exact p.explode _
  | @conjLeft α Δ B D C hm q ih =>
      intro A hA hdepth Γ p hΔ
      let out := ih A hA hdepth (p.weaken (subsetTwo Γ B D)) (augmentTwo hΔ)
      by_cases hc : (.conj B D) ∈ Γ
      · exact .conjLeft hc out
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hc
        subst A
        exact reducers.conjunction hdepth hA.1 hA.2 p out
  | conjRight _ _ ihp ihq =>
      intro A hA hdepth Γ p hΔ
      exact .conjRight (ihp A hA hdepth p hΔ) (ihq A hA hdepth p hΔ)
  | @disjLeft α Δ B D C hm _ _ ihp ihq =>
      intro A hA hdepth Γ p hΔ
      let outB := ihp A hA hdepth (p.weaken (Finset.subset_insert _ _)) (augment hΔ)
      let outD := ihq A hA hdepth (p.weaken (Finset.subset_insert _ _)) (augment hΔ)
      by_cases hc : (.disj B D) ∈ Γ
      · exact .disjLeft hc outB outD
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hc
        subst A
        exact reducers.disjunction hdepth hA.1 hA.2 p outB outD
  | disjRightLeft _ ih =>
      intro A hA hdepth Γ p hΔ
      exact .disjRightLeft (ih A hA hdepth p hΔ)
  | disjRightRight _ ih =>
      intro A hA hdepth Γ p hΔ
      exact .disjRightRight (ih A hA hdepth p hΔ)
  | @implLeft α Δ B D C hm _ _ ihp ihq =>
      intro A hA hdepth Γ p hΔ
      let outB := ihp A hA hdepth p hΔ
      let outD := ihq A hA hdepth (p.weaken (Finset.subset_insert _ _)) (augment hΔ)
      by_cases hc : (.impl B D) ∈ Γ
      · exact .implLeft hc outB outD
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hc
        subst A
        exact reducers.implication hdepth hA.1 hA.2 p outB outD
  | implRight _ ih =>
      intro A hA hdepth Γ p hΔ
      exact .implRight (ih A hA hdepth (p.weaken (Finset.subset_insert _ _)) (augment hΔ))
  | @negLeft α Δ B C hm _ ih =>
      intro A hA hdepth Γ p hΔ
      let outB := ih A hA hdepth p hΔ
      by_cases hc : (.neg B) ∈ Γ
      · exact .negLeft hc outB
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hc
        subst A
        exact reducers.negation hdepth hA p outB
  | negRight _ ih =>
      intro A hA hdepth Γ p hΔ
      exact .negRight (ih A hA hdepth (p.weaken (Finset.subset_insert _ _)) (augment hΔ))
  | @allLeft α Δ C B t hm _ ih =>
      intro A hA hdepth Γ p hΔ
      let out := ih A hA hdepth (p.weaken (Finset.subset_insert _ _)) (augment hΔ)
      by_cases hc : (.all B) ∈ Γ
      · exact .allLeft t hc out
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hc
        subst A
        exact reducers.universal hdepth hA t p out
  | @allRight α Δ B _ ih =>
      intro A hA hdepth Γ p hΔ
      have hpure : (A.rename (Sum.inl : α → α ⊕ Fin 1)).EqualityFree :=
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).mpr hA
      have hd : (A.rename (Sum.inl : α → α ⊕ Fin 1)).depth = rank := by
        simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map] using hdepth
      exact .allRight (ih (A.rename Sum.inl) hpure hd (p.rename Sum.inl) (liftInclusion hΔ))
  | @exLeft α Δ C B hm _ ih =>
      intro A hA hdepth Γ p hΔ
      have hpure : (A.rename (Sum.inl : α → α ⊕ Fin 1)).EqualityFree :=
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).mpr hA
      have hd : (A.rename (Sum.inl : α → α ⊕ Fin 1)).depth = rank := by
        simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map] using hdepth
      let out := ih (A.rename Sum.inl) hpure hd
        ((p.rename Sum.inl).weaken (Finset.subset_insert _ _)) (augment (liftInclusion hΔ))
      by_cases hc : (.ex B) ∈ Γ
      · exact .exLeft hc out
      · have he := (Finset.mem_insert.mp (hΔ hm)).resolve_right hc
        subst A
        exact reducers.existential hdepth hA p out
  | exRight t _ ih =>
      intro A hA hdepth Γ p hΔ
      exact .exRight t (ih A hA hdepth p hΔ)

/-- Consumer recursion removes every unwanted retained occurrence before reducing a principal. -/
def paste {rank : ℕ} (reducers : PrincipalReducers.{u,v,w} L rank)
    (A : Formula L α) (hA : A.EqualityFree) (hdepth : A.depth = rank) :
    Replacement A := by
  intro Γ Δ C p q hΔ
  exact pasteAux reducers q A hA hdepth p hΔ

def reduceConj {B D : Formula L α} (kB : Replacement B) (kD : Replacement D)
    {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ (.conj B D))
    (r : CoreProof L (insert B (insert D Γ)) C) : CoreProof L Γ C := by
  exact kD p.invertConj.2
    (kB (p.invertConj.1.weaken (Finset.subset_insert _ _)) r (Finset.Subset.refl _))
    (Finset.Subset.refl _)

def reduceImpl {B D : Formula L α} (kB : Replacement B) (kD : Replacement D)
    {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ (.impl B D)) (b : CoreProof L Γ B)
    (r : CoreProof L (insert D Γ) C) : CoreProof L Γ C := by
  exact kD (kB b p.invertImpl (Finset.Subset.refl _)) r (Finset.Subset.refl _)

def reduceNeg {B : Formula L α} (kB : Replacement B)
    {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ (.neg B)) (b : CoreProof L Γ B) : CoreProof L Γ C := by
  exact (kB b p.invertNeg (Finset.Subset.refl _)).explode C

private def liftedBranch {Γ : Context L α} {B C : Formula L α}
    (r : CoreProof L (insert B Γ) C) (D : Formula L (α ⊕ Fin 1)) :
    CoreProof L (insert (B.rename Sum.inl) (insert D (liftContext Γ))) (C.rename Sum.inl) := by
  have q := r.rename (Sum.inl : α → α ⊕ Fin 1)
  rw [Finset.image_insert] at q
  exact q.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))

private def reduceDisjAux {rank : ℕ} (smaller : SmallerReplacements.{u,v,w} L rank)
    {α : Type w} {Γ : Context L α} {E : Formula L α} (p : CoreProof L Γ E) :
    ∀ (B D : Formula L α), (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.disj B D).depth = rank →
      B.EqualityFree → D.EqualityFree → E = .disj B D →
      ∀ C : Formula L α, CoreProof L (insert B Γ) C → CoreProof L (insert D Γ) C →
        CoreProof L Γ C := by
  induction p with
  | relation _ _ _ => intro B D hd hB hD he; cases he
  | falsumLeft hm => intro B D hd hB hD he C rB rD; exact .falsumLeft hm
  | @conjLeft α Γ X Y E hm _ ih =>
      intro B D hd hB hD he C rB rD
      exact .conjLeft hm (ih B D hd hB hD he C
        (rB.weaken (Finset.insert_subset_insert _ (subsetTwo Γ X Y)))
        (rD.weaken (Finset.insert_subset_insert _ (subsetTwo Γ X Y))))
  | conjRight _ _ _ _ => intro B D hd hB hD he; cases he
  | @disjLeft α Γ X Y E hm _ _ ihp ihq =>
      intro B D hd hB hD he C rB rD
      exact .disjLeft hm
        (ihp B D hd hB hD he C
          (rB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
          (rD.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
        (ihq B D hd hB hD he C
          (rB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
          (rD.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
  | @disjRightLeft α Γ X Y p _ =>
      intro B D hd hB hD he C rB rD
      cases he
      exact smaller X hB (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega)
        p rB (Finset.Subset.refl _)
  | @disjRightRight α Γ X Y p _ =>
      intro B D hd hB hD he C rB rD
      cases he
      exact smaller Y hD (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega)
        p rD (Finset.Subset.refl _)
  | @implLeft α Γ X Y E hm p _ _ ih =>
      intro B D hd hB hD he C rB rD
      exact .implLeft hm p (ih B D hd hB hD he C
        (rB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (rD.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
  | implRight _ _ => intro B D hd hB hD he; cases he
  | negLeft hm p _ => intro B D hd hB hD he C rB rD; exact .negLeft hm p
  | negRight _ _ => intro B D hd hB hD he; cases he
  | @allLeft α Γ E X t hm _ ih =>
      intro B D hd hB hD he C rB rD
      exact .allLeft t hm (ih B D hd hB hD he C
        (rB.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        (rD.weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
  | allRight _ _ => intro B D hd hB hD he; cases he
  | @exLeft α Γ E X hm _ ih =>
      intro B D hd hB hD he C rB rD
      subst E
      apply CoreProof.exLeft hm
      apply ih (B.rename Sum.inl) (D.rename Sum.inl)
      · simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map] using hd
      · exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).mpr hB
      · exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map D _).mpr hD
      · rfl
      · exact liftedBranch rB X.toFormula
      · exact liftedBranch rD X.toFormula
  | exRight _ _ _ => intro B D hd hB hD he; cases he

private def reduceExAux {rank : ℕ} (smaller : SmallerReplacements.{u,v,w} L rank)
    {α : Type w} {Γ : Context L α} {E : Formula L α} (p : CoreProof L Γ E) :
    ∀ (B : BF L α 1), (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex B).depth = rank →
      B.EqualityFree → E = .ex B → ∀ C : Formula L α,
      CoreProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl) →
        CoreProof L Γ C := by
  induction p with
  | relation _ _ _ => intro B hd hB he; cases he
  | falsumLeft hm => intro B hd hB he C r; exact .falsumLeft hm
  | @conjLeft α Γ X Y E hm _ ih =>
      intro B hd hB he C r
      apply CoreProof.conjLeft hm
      apply ih B hd hB he C
      apply r.weaken
      apply Finset.insert_subset_insert
      exact Finset.image_subset_image (subsetTwo Γ X Y)
  | conjRight _ _ _ _ => intro B hd hB he; cases he
  | @disjLeft α Γ X Y E hm _ _ ihp ihq =>
      intro B hd hB he C r
      apply CoreProof.disjLeft hm
      · apply ihp B hd hB he C
        exact r.weaken (Finset.insert_subset_insert _
          (Finset.image_subset_image (Finset.subset_insert _ _)))
      · apply ihq B hd hB he C
        exact r.weaken (Finset.insert_subset_insert _
          (Finset.image_subset_image (Finset.subset_insert _ _)))
  | disjRightLeft _ _ => intro B hd hB he; cases he
  | disjRightRight _ _ => intro B hd hB he; cases he
  | @implLeft α Γ X Y E hm p _ _ ih =>
      intro B hd hB he C r
      apply CoreProof.implLeft hm p
      apply ih B hd hB he C
      exact r.weaken (Finset.insert_subset_insert _
        (Finset.image_subset_image (Finset.subset_insert _ _)))
  | implRight _ _ => intro B hd hB he; cases he
  | negLeft hm p _ => intro B hd hB he C r; exact .negLeft hm p
  | negRight _ _ => intro B hd hB he; cases he
  | @allLeft α Γ E X t hm _ ih =>
      intro B hd hB he C r
      apply CoreProof.allLeft t hm
      apply ih B hd hB he C
      exact r.weaken (Finset.insert_subset_insert _
        (Finset.image_subset_image (Finset.subset_insert _ _)))
  | allRight _ _ => intro B hd hB he; cases he
  | @exLeft α Γ E X hm _ ih =>
      intro B hd hB he C r
      subst E
      apply CoreProof.exLeft hm
      apply ih (B.rename Sum.inl)
      · simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
          Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map] using hd
      · exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).mpr hB
      · exact Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex B
          (fun x => .var (Sum.inl x))
      · exact liftContinuation (D := X) r
  | @exRight α Γ X t p _ =>
      intro B hd hB he C r
      cases he
      exact smaller (X.instantiate t)
        ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map X _).mpr hB)
        (by
          simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
            Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
            Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map]
          simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd
          omega)
        p (instantiateContinuation t r) (Finset.Subset.refl _)

/-- Traverse a disjunction producer, transporting both continuations at protected branches. -/
def reduceDisj {rank : ℕ} (smaller : SmallerReplacements.{u,v,w} L rank)
    {B D : Formula L α} (hdepth : (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.disj B D).depth = rank)
    (hB : B.EqualityFree) (hD : D.EqualityFree)
    {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ (.disj B D))
    (rB : CoreProof L (insert B Γ) C) (rD : CoreProof L (insert D Γ) C) :
    CoreProof L Γ C :=
  reduceDisjAux smaller p B D hdepth hB hD rfl C rB rD

/-- The consumer's actual term selects the smaller body replacement. -/
def reduceAll {rank : ℕ} (smaller : SmallerReplacements.{u,v,w} L rank)
    {B : BF L α 1} (hdepth : (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all B).depth = rank) (hB : B.EqualityFree)
    {Γ : Context L α} {C : Formula L α} (t : L.Term α)
    (p : CoreProof L Γ (.all B)) (r : CoreProof L (insert (B.instantiate t) Γ) C) :
    CoreProof L Γ C := by
  exact smaller (B.instantiate t)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).mpr hB)
    (by
      simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots,
        Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth_map]
      simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hdepth
      omega)
    (CoreProof.invertAll t p) r (Finset.Subset.refl _)

/-- Traverse the supplied existential producer with its exact protected continuation. -/
def reduceEx {rank : ℕ} (smaller : SmallerReplacements.{u,v,w} L rank)
    {B : BF L α 1} (hdepth : (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex B).depth = rank) (hB : B.EqualityFree)
    {Γ : Context L α} {C : Formula L α}
    (p : CoreProof L Γ (.ex B))
    (r : CoreProof L (insert B.toFormula (liftContext Γ)) (C.rename Sum.inl)) :
    CoreProof L Γ C :=
  reduceExAux smaller p B hdepth hB rfl C r

/-- Assemble all same-depth handlers from already constructed smaller replacements. -/
def principalReducers (rank : ℕ) (smaller : SmallerReplacements.{u,v,w} L rank) :
    PrincipalReducers.{u,v,w} L rank := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro δ Γ B D C hd hB hD p r
    exact reduceConj
      (smaller B hB (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega))
      (smaller D hD (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega)) p r
  · intro δ Γ B D C hd hB hD p rB rD
    exact reduceDisj smaller hd hB hD p rB rD
  · intro δ Γ B D C hd hB hD p b r
    exact reduceImpl
      (smaller B hB (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega))
      (smaller D hD (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega)) p b r
  · intro δ Γ B C hd hB p b
    exact reduceNeg
      (smaller B hB (by simp only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.depth] at hd; omega)) p b
  · intro δ Γ B C hd hB t p r
    exact reduceAll smaller hd hB t p r
  · intro δ Γ B C hd hB p r
    exact reduceEx smaller hd hB p r

private def atDepth (rank : ℕ) :
    ∀ {δ : Type w} (A : Formula L δ), A.EqualityFree → A.depth = rank → Replacement A := by
  intro δ A hA hd
  exact paste (principalReducers rank (fun {ε} B hB hlt => atDepth B.depth B hB rfl)) A hA hd
termination_by rank
decreasing_by exact hlt

end CutFree

/-- Strong depth recursion supplies replacement in the actual primitive rules. -/
def CoreProof.replace (A : Formula L α) (hA : A.EqualityFree) :
    CutFree.Replacement A := CutFree.atDepth A.depth A hA rfl

def CoreProof.cut {Γ Δ : Context L α} {A C : Formula L α} (hA : A.EqualityFree)
    (p : CoreProof L Γ A) (q : CoreProof L (insert A Δ) C) :
    CoreProof L (Γ ∪ Δ) C :=
  CoreProof.replace A hA (p.weaken Finset.subset_union_left) q
    (Finset.insert_subset_insert _ Finset.subset_union_right)

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
