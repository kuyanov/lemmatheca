import Lemmatheca.ClassicalPropositionalSequents.Properties
import Lemmatheca.EqualityFreeFirstOrderExistentialHerbrandExtraction.Factors
import Lemmatheca.EqualityFreeFirstOrderCutElimination.Deductions

/-! Nonempty term tuples from supplied raw/public/native proof certificates,
including exact leading-universal scopes and removal of a specified reserve. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section

private theorem list_imageE {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (xs : List γ) (f : γ → δ) : xs.toFinset.image f = (xs.map f).toFinset := by
  ext a
  simp

private def singletonWitness {F : Nnf L α 0} (w : OriginWitness {F}) : Witness F :=
  (Finset.mem_singleton.mp w.member) ▸ w.witness

private theorem singleton_value {F : Nnf L α 0} (w : OriginWitness {F}) :
    (singletonWitness w).value = w.witness.value := by
  cases w with
  | mk origin member witness =>
      have he := Finset.mem_singleton.mp member
      subst origin
      rfl

private theorem instantiate_empty (A : Nnf L α 0) : A.instantiateSlots Fin.elim0 = A := by
  unfold Nnf.instantiateSlots
  have he : (Sum.elim (fun x => Term.var (Sum.inl x))
      (fun i : Fin 0 => (Fin.elim0 i : L.Term α).relabel Sum.inl)) = Term.var := by
    funext x
    cases x with
    | inl a => rfl
    | inr i => exact Fin.elim0 i
  rw [he,Nnf.map_id]

/-- Extract actual tuples and the actual five-rule factor tree from a supplied tree. -/
def extractRaw {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (p : CoreProof L {existsBlock A}) : Certificate A := by
  classical
  cases n with
  | zero =>
      refine ⟨h,[Fin.elim0],by simp,?_⟩
      have pp := toPropositional p (by
        intro C hc
        have he : C = A := Finset.mem_singleton.mp hc
        exact he ▸ h)
      simpa only [existsBlock,bindExists,readContext,Finset.image_singleton,
        List.map_cons,List.map_nil,List.toFinset_cons,List.toFinset_nil,
        instantiate_empty,Finset.insert_empty] using pp
  | succ n =>
      let E := existsBlock A
      have hd : ContextQF (∅ : Sequent L α) := by simp [ContextQF]
      have hl : ContextProper {E} := by
        intro C hc
        have he : C = E := Finset.mem_singleton.mp hc
        subst C
        exact existsBlock_proper A h (Nat.zero_lt_succ n)
      let e := extractWeak p ∅ {E} hd hl (by intro C hc; simpa only [E,Finset.empty_union] using hc)
      let ts := e.witnesses.map (fun w => (singletonWitness w).tuple A h)
      refine ⟨h,ts,?_,?_⟩
      · intro he
        have hw : e.witnesses = [] := List.map_eq_nil_iff.mp he
        have pe : PropProof (∅ : Finset (PropNnf (Atom L α))) := by
          simpa [hw,readContext,values] using e.factor
        exact ClassicalPropositional.empty_not_derivable ⟨pe⟩
      · have heq : readContext (values e.witnesses) =
            (ts.map (fun ss => propositionalize (A.instantiateSlots ss))).toFinset := by
          unfold readContext values ts
          rw [list_imageE]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro w hw
          dsimp only [Function.comp_apply]
          rw [← Witness.value_tuple A h,singleton_value]
        simpa only [readContext,Finset.image_empty,Finset.empty_union,← heq] using e.factor

def extractCut {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (p : CutProof L {existsBlock A}) : Certificate A := extractRaw A h p.eliminate

/-- The exact equality-disabled native system supplies the same signed singleton. -/
def extractNative {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation true false L ∅
      (existsBlock A).read) : Certificate A := by
  have hpure : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure
      (∅ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) := by
    intro F hf; simp at hf
  have q := CutDeductions.fromNative p hpure (Nnf.read_equalityFree _)
  have qc : CoreProof L {existsBlock A} := by
    simpa [CutDeductions.encodeNative,CutDeductions.negativeContext] using q
  exact extractRaw A h qc

theorem raw_exists_iff {n} (A : Nnf L α n) (h : A.QuantifierFree) :
    Nonempty (CoreProof L {existsBlock A}) ↔ Nonempty (Certificate A) :=
  ⟨fun ⟨p⟩ => ⟨extractRaw A h p⟩,fun ⟨H⟩ => ⟨reconstruct A H⟩⟩

/-- No reserve variable is deleted from the stored terms. -/
def extractPublic {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (p : Proof {existsBlock A}) : Certificate (A.rename (Sum.inl : α → α ⊕ ℕ)) := by
  change CoreProof L (renameContext {existsBlock A} (Sum.inl : α → α ⊕ ℕ)) at p
  have q : CoreProof L {existsBlock (A.rename (Sum.inl : α → α ⊕ ℕ))} := by
    simpa only [renameContext,Finset.image_singleton,Nnf.rename,existsBlock_subst] using p
  exact extractRaw _ ((Nnf.quantifierFree_map _ _).mpr h) q

def extractNativePublic {n} (A : Nnf L α n) (h : A.QuantifierFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true false L ∅
      (existsBlock A).read) : Certificate (A.rename (Sum.inl : α → α ⊕ ℕ)) := by
  have hpure : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.ContextPure
      (∅ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) := by
    intro F hf; simp at hf
  have q := CutDeductions.fromNativePublic p hpure (Nnf.read_equalityFree _)
  have qc : Proof {existsBlock A} := by
    simpa [CutDeductions.encodeNative,CutDeductions.negativeContext] using q
  exact extractPublic A h qc

def reconstructPublic {n} (A : Nnf L α n)
    (H : Certificate (A.rename (Sum.inl : α → α ⊕ ℕ))) : Proof {existsBlock A} := by
  change CoreProof L (renameContext {existsBlock A} (Sum.inl : α → α ⊕ ℕ))
  have q := reconstruct _ H
  simpa only [renameContext,Finset.image_singleton,Nnf.rename,existsBlock_subst] using q

theorem public_exists_iff {n} (A : Nnf L α n) (h : A.QuantifierFree) :
    Derives {existsBlock A} ↔ Nonempty (Certificate (A.rename (Sum.inl : α → α ⊕ ℕ))) :=
  ⟨fun ⟨p⟩ => ⟨extractPublic A h p⟩,fun ⟨H⟩ => ⟨reconstructPublic A H⟩⟩

private def lastScope {k} : Lemmatheca.ProofTheory.FirstOrder.ScopeSubst L α (α ⊕ Fin k) (k+1) 1 :=
  Sum.elim (fun a => .var (.inl (.inl a)))
    (Fin.lastCases (.var (.inr 0)) (fun i => .var (.inl (.inr i))))

private def openLast {k} (B : Nnf L α (k+1)) : Nnf L (α ⊕ Fin k) 1 := B.map lastScope

private def flattenNames {k} : (α ⊕ Fin k) ⊕ Fin 1 → α ⊕ Fin (k+1) :=
  Sum.elim (Sum.elim Sum.inl (fun i => .inr i.castSucc)) (fun _ => .inr (Fin.last k))

private def expandNames {k} : α ⊕ Fin (k+1) → (α ⊕ Fin k) ⊕ Fin 1 :=
  Sum.elim (fun a => .inl (.inl a)) (Fin.lastCases (.inr 0) (fun i => .inl (.inr i)))

private theorem openLast_all {k} (B : Nnf L α (k+1)) :
    Nnf.all (openLast B) = (Nnf.all B).toFormula := by
  have hs : (lastScope : Lemmatheca.ProofTheory.FirstOrder.ScopeSubst L α (α ⊕ Fin k) (k+1) 1) =
      Lemmatheca.ProofTheory.FirstOrder.liftScope (fun x : α ⊕ Fin k => Term.var (Sum.inl x)) := by
    funext x
    cases x with
    | inl a => rfl
    | inr i =>
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp [lastScope,Lemmatheca.ProofTheory.FirstOrder.liftScope,
            Lemmatheca.ProofTheory.FirstOrder.scopeInclusion,Term.relabel]
  exact congrArg (fun σ => Nnf.all (B.map σ)) hs

private theorem openLast_flat {k} (B : Nnf L α (k+1)) :
    (openLast B).toFormula.rename flattenNames = B.toFormula := by
  unfold openLast Nnf.toFormula Nnf.rename Nnf.subst
  rw [Nnf.map_comp,Nnf.map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp [lastScope,flattenNames,Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
          Term.subst]

private theorem openLast_expand {k} (B : Nnf L α (k+1)) :
    B.toFormula.rename expandNames = (openLast B).toFormula := by
  unfold openLast Nnf.toFormula Nnf.rename Nnf.subst
  rw [Nnf.map_comp,Nnf.map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;>
        simp [lastScope,expandNames,Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,
          Term.subst]

private theorem toFormula_zero (B : Nnf L α 0) :
    B.toFormula = B.rename (Sum.inl : α → α ⊕ Fin 0) := by
  unfold Nnf.toFormula Nnf.rename Nnf.subst
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i => exact Fin.elim0 i

private theorem forallBlock_succ {k} (B : Nnf L α (k+1)) :
    forallBlock B = forallBlock (Nnf.all B) := by
  have hc : (Nat.zero_add k).symm ▸ Nnf.all B =
      Nnf.all ((Nat.zero_add (k+1)).symm ▸ B) := by
    have aux : ∀ {a b} (e : a = b) (C : Nnf L α (a+1)),
        e ▸ Nnf.all C = Nnf.all ((congrArg (· + 1) e) ▸ C) := by
      intro a b e C
      subst b
      rfl
    exact aux (Nat.zero_add k).symm B
  unfold forallBlock
  rw [hc]
  rfl

private def openAll {k} (B : Nnf L α k) (p : CoreProof L {forallBlock B}) :
    CoreProof L {B.toFormula} := by
  induction k with
  | zero =>
      have q := p.rename (Sum.inl : α → α ⊕ Fin 0)
      simpa only [forallBlock,bindForall,renameContext,Finset.image_singleton,toFormula_zero] using q
  | succ k ih =>
      have pi : CoreProof L {forallBlock (Nnf.all B)} := by
        simpa only [forallBlock_succ] using p
      have q := ih (.all B) pi
      have qa : CoreProof L {Nnf.all (openLast B)} := by
        simpa only [openLast_all] using q
      have qr := qa.rename (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ Fin 1)
      have qi := CoreProof.invertAll ((openLast B).rename (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ Fin 1))
        (.var (.inr 0)) (Δ := ∅) qr (by
          simp only [renameContext,Finset.image_singleton,Nnf.rename,Nnf.subst_all,
            Finset.insert_empty]
          exact Finset.Subset.refl _)
      have qo : CoreProof L {(openLast B).toFormula} := by
        simpa only [Nnf.instantiate_rename_fresh,Finset.insert_empty] using qi
      have qf := qo.rename flattenNames
      simpa only [renameContext,Finset.image_singleton,openLast_flat] using qf

private def closeAll {k} (B : Nnf L α k) (p : CoreProof L {B.toFormula}) :
    CoreProof L {forallBlock B} := by
  induction k with
  | zero =>
      have q := p.rename (Sum.elim id Fin.elim0 : α ⊕ Fin 0 → α)
      have he : B.toFormula.rename (Sum.elim id Fin.elim0 : α ⊕ Fin 0 → α) = B := by
        rw [toFormula_zero,Nnf.rename_comp]
        exact Nnf.rename_id B
      simpa only [renameContext,Finset.image_singleton,he,forallBlock,bindForall] using q
  | succ k ih =>
      have qe := p.rename expandNames
      have qo : CoreProof L {(openLast B).toFormula} := by
        simpa only [renameContext,Finset.image_singleton,openLast_expand] using qe
      have qa := CoreProof.allIntro (Γ := ∅) (openLast B)
        (by simpa only [liftContext,renameContext,Finset.image_empty,Finset.insert_empty] using qo)
      have qi : CoreProof L {(Nnf.all B).toFormula} := by
        simpa only [Finset.insert_empty,openLast_all] using qa
      have q := ih (.all B) qi
      simpa only [forallBlock_succ] using q

/-- Use the actual strong universal-instance operation at the finite fresh names. -/
def openUniversalProof {k n} (A : Nnf L α (k+n))
    (p : CoreProof L {universalExistential A}) :
    CoreProof L {existsBlock (openUniversalMatrix A)} := by
  have q := openAll (bindExists n A) p
  simpa only [opened_block] using q

/-- Close the actual protected parameter tags in reverse order. -/
def closeUniversalProof {k n} (A : Nnf L α (k+n))
    (p : CoreProof L {existsBlock (openUniversalMatrix A)}) :
    CoreProof L {universalExistential A} := by
  have q : CoreProof L {(bindExists n A).toFormula} := by
    simpa only [opened_block] using p
  exact closeAll (bindExists n A) q

def extractUniversal {k n} (A : Nnf L α (k+n)) (h : A.QuantifierFree)
    (p : CoreProof L {universalExistential A}) : Certificate (openUniversalMatrix A) :=
  extractRaw _ ((Nnf.quantifierFree_map _ _).mpr h) (openUniversalProof A p)

def extractUniversalCut {k n} (A : Nnf L α (k+n)) (h : A.QuantifierFree)
    (p : CutProof L {universalExistential A}) : Certificate (openUniversalMatrix A) :=
  extractUniversal A h p.eliminate

def reconstructUniversal {k n} (A : Nnf L α (k+n))
    (H : Certificate (openUniversalMatrix A)) : CoreProof L {universalExistential A} :=
  closeUniversalProof A (reconstruct _ H)

private def swapNames {k} : (α ⊕ ℕ) ⊕ Fin k → (α ⊕ Fin k) ⊕ ℕ :=
  Sum.elim (Sum.elim (fun a => .inl (.inl a)) Sum.inr) (fun i => .inl (.inr i))

private def unswapNames {k} : (α ⊕ Fin k) ⊕ ℕ → (α ⊕ ℕ) ⊕ Fin k :=
  Sum.elim (Sum.elim (fun a => .inl (.inl a)) Sum.inr) (fun i => .inl (.inr i))

private theorem open_swap {k n} (A : Nnf L α (k+n)) :
    (openUniversalMatrix (A.rename (Sum.inl : α → α ⊕ ℕ))).rename swapNames =
      (openUniversalMatrix A).rename (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ ℕ) := by
  unfold openUniversalMatrix Nnf.rename Nnf.subst
  rw [Nnf.map_comp,Nnf.map_comp,Nnf.map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
      induction i using Fin.addCases with
      | left i => simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,Term.subst,swapNames]
      | right i => simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,Term.subst,swapNames]

private theorem open_unswap {k n} (A : Nnf L α (k+n)) :
    ((openUniversalMatrix A).rename (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ ℕ)).rename unswapNames =
      openUniversalMatrix (A.rename (Sum.inl : α → α ⊕ ℕ)) := by
  unfold openUniversalMatrix Nnf.rename Nnf.subst
  rw [Nnf.map_comp,Nnf.map_comp,Nnf.map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i =>
      induction i using Fin.addCases with
      | left i => simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,Term.subst,unswapNames]
      | right i => simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeScope,Term.subst,unswapNames]

private theorem universal_rename {k n} (A : Nnf L α (k+n))
    (f : α → α ⊕ ℕ) :
    (universalExistential A).rename f = universalExistential (A.rename f) := by
  unfold universalExistential Nnf.rename
  rw [forallBlock_subst]
  congr 1
  -- Closing only the last n slots commutes with free substitution as well.
  have hb : ∀ (j m : ℕ) (B : Nnf L α (m+j)),
      (bindExists j B).subst (fun x => Term.var (f x)) =
        bindExists j (B.subst (fun x => Term.var (f x))) := by
    intro j
    induction j with
    | zero => intro m B; rfl
    | succ j ih =>
        intro m B
        simpa only [bindExists,Nnf.subst_ex] using ih m (.ex B)
  exact hb n k A

/-- The finite opened tags precede the public reserve in the stated output type. -/
def extractUniversalPublic {k n} (A : Nnf L α (k+n)) (h : A.QuantifierFree)
    (p : Proof {universalExistential A}) :
    Certificate ((openUniversalMatrix A).rename (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ ℕ)) := by
  have q : CoreProof L {universalExistential (A.rename (Sum.inl : α → α ⊕ ℕ))} := by
    change CoreProof L (renameContext {universalExistential A} (Sum.inl : α → α ⊕ ℕ)) at p
    simpa only [renameContext,Finset.image_singleton,universal_rename] using p
  let H := extractUniversal _ ((Nnf.quantifierFree_map _ _).mpr h) q
  have hs := H.substitute (fun x => Term.var (swapNames x))
  change Certificate ((openUniversalMatrix (A.rename (Sum.inl : α → α ⊕ ℕ))).rename swapNames) at hs
  exact open_swap A ▸ hs

def reconstructUniversalPublic {k n} (A : Nnf L α (k+n))
    (H : Certificate ((openUniversalMatrix A).rename (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ ℕ))) :
    Proof {universalExistential A} := by
  have hs := H.substitute (fun x => Term.var (unswapNames x))
  change Certificate (((openUniversalMatrix A).rename
    (Sum.inl : α ⊕ Fin k → (α ⊕ Fin k) ⊕ ℕ)).rename unswapNames) at hs
  have ht : Certificate (openUniversalMatrix (A.rename (Sum.inl : α → α ⊕ ℕ))) :=
    open_unswap A ▸ hs
  have q := reconstructUniversal _ ht
  change CoreProof L (renameContext {universalExistential A} (Sum.inl : α → α ⊕ ℕ))
  simpa only [renameContext,Finset.image_singleton,universal_rename] using q

private theorem reserve_matrix {n} (A : Nnf L α n) (r : L.Term α) :
    (A.rename (Sum.inl : α → α ⊕ ℕ)).subst (reserveReplacement r) = A := by
  unfold Nnf.rename
  rw [Nnf.subst_comp]
  exact Nnf.subst_id A

private theorem cast_certificate_tuples {n} {A B : Nnf L α n} (he : A = B)
    (H : Certificate A) : (he ▸ H : Certificate B).tuples = H.tuples := by
  subst B
  rfl

/-- This supplied original term replaces every reserve variable simultaneously. -/
def removeReserve {n} (A : Nnf L α n) (r : L.Term α)
    (H : Certificate (A.rename (Sum.inl : α → α ⊕ ℕ))) : Certificate A :=
  reserve_matrix A r ▸ H.substitute (reserveReplacement r)

theorem removeReserve_tuples {n} (A : Nnf L α n) (r : L.Term α)
    (H : Certificate (A.rename (Sum.inl : α → α ⊕ ℕ))) :
    (removeReserve A r H).tuples =
      H.tuples.map (fun ts i => (ts i).subst (reserveReplacement r)) := by
  unfold removeReserve
  rw [cast_certificate_tuples,Certificate.substitute_tuples]

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.ExistentialHerbrand
