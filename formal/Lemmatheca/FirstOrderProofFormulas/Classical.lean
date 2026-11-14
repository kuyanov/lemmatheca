import Lemmatheca.FirstOrderProofFormulas.Operations

/-! Exact comparison to the existing classical language, and classical truth. -/
namespace Lemmatheca.ProofTheory.FirstOrder
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w w' w''
variable {L : Language.{u,v}} {α : Type w} {β : Type w'} {γ : Type w''}

/-- Absence of equality in the five-constructor classical syntax. -/
def classicalEqualityFree : ∀ {n}, L.BoundedFormula α n → Prop
  | _, .falsum | _, .rel _ _ => True
  | _, .equal _ _ => False
  | _, .imp A B => classicalEqualityFree A ∧ classicalEqualityFree B
  | _, .all A => classicalEqualityFree A

@[simp] theorem classicalMap_freeScope {n} (A : L.BoundedFormula α n) (σ : α → L.Term β) :
    classicalMap A (BoundedFormula.freeScope σ n) = A.subst σ := by
  induction A with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | imp A B ihA ihB => simp only [classicalMap, formula_subst_imp, ihA, ihB]
  | all A ih => simp only [classicalMap, BoundedFormula.liftScope_freeScope, formula_subst_all, ih]


private theorem relabelAux_inclusion {k m} (g : β → γ ⊕ Fin k) :
    Language.BoundedFormula.relabelAux g (m+1) ∘ scopeInclusion m =
      scopeInclusion (k+m) ∘ Language.BoundedFormula.relabelAux g m := by
  funext x
  cases x with
  | inl a =>
    cases h : g a with
    | inl b => simp [scopeInclusion, Language.BoundedFormula.relabelAux, h]
    | inr i =>
      simp [scopeInclusion, Language.BoundedFormula.relabelAux, h]
      exact Fin.ext rfl
  | inr i =>
    simp [scopeInclusion, Language.BoundedFormula.relabelAux]

private theorem relabelAux_last {k m} (g : β → γ ⊕ Fin k) :
    Language.BoundedFormula.relabelAux g (m+1) (.inr (Fin.last m)) =
      .inr (Fin.last (k+m)) := by
  simp [Language.BoundedFormula.relabelAux]

private theorem liftScope_relabel {n m k} (σ : ScopeSubst L α β n m) (g : β → γ ⊕ Fin k) :
    liftScope (fun x => (σ x).relabel (Language.BoundedFormula.relabelAux g m)) =
      (fun x => (liftScope σ x).relabel (Language.BoundedFormula.relabelAux g (m+1))) := by
  funext x
  cases x with
  | inl a =>
    simp only [liftScope, Sum.elim_inl, Term.relabel_relabel]
    congr 1
    exact (relabelAux_inclusion g).symm
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [liftScope_last, Term.relabel]
      exact congrArg Term.var (relabelAux_last g).symm
    · simp only [liftScope, Sum.elim_inr, Fin.lastCases_castSucc, Term.relabel_relabel]
      congr 1
      exact (relabelAux_inclusion g).symm

private theorem classicalMap_relabel {n m k} (A : L.BoundedFormula α n)
    (σ : ScopeSubst L α β n m) (g : β → γ ⊕ Fin k) :
    (classicalMap A σ).relabel g =
      classicalMap A (fun x => (σ x).relabel (Language.BoundedFormula.relabelAux g m)) := by
  induction A generalizing m with
  | falsum => rfl
  | equal s t =>
    simp only [classicalMap, Language.BoundedFormula.relabel,
      Language.BoundedFormula.mapTermRel, term_relabel_subst]
  | rel R ts =>
    simp only [classicalMap, Language.BoundedFormula.relabel,
      Language.BoundedFormula.mapTermRel, term_relabel_subst]
    rfl
  | imp A B ihA ihB =>
    simp only [classicalMap, Language.BoundedFormula.relabel_imp, ihA, ihB]
  | all A ih =>
    simp only [classicalMap, Language.BoundedFormula.relabel_all]
    rw [ih]
    rw [liftScope_relabel]

theorem classicalMap_toFormula {n} (A : L.BoundedFormula α n) :
    classicalMap A (fun x => .var (.inl x)) = A.toFormula := by
  induction A with
  | falsum => rfl
  | equal s t =>
    simp [classicalMap, Language.BoundedFormula.toFormula, Term.equal, Term.bdEqual,
      term_subst_vars]
  | rel R ts =>
    simp [classicalMap, Language.BoundedFormula.toFormula, Relations.formula,
      Relations.boundedFormula, term_subst_vars]
  | imp A B ihA ihB =>
    simp only [classicalMap, Language.BoundedFormula.toFormula, ihA, ihB]
  | @all n A ih =>
    simp only [classicalMap, Language.BoundedFormula.toFormula]
    rw [← ih, classicalMap_relabel]
    congr 1
    apply congrArg (classicalMap A)
    funext x
    cases x with
    | inl a => simp [liftScope, scopeInclusion, Language.BoundedFormula.relabelAux, Term.relabel]
    | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hlast : (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1)).symm (Fin.last n) =
            .inr 0 := by
          apply (Equiv.symm_apply_eq finSumFinEquiv).mpr
          exact Fin.ext rfl
        simp [liftScope, scopeInclusion, Language.BoundedFormula.relabelAux, Term.relabel, hlast]
        exact Fin.ext rfl
      · have hcast : (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1)).symm j.castSucc =
            .inl j := by
          apply (Equiv.symm_apply_eq finSumFinEquiv).mpr
          exact Fin.ext rfl
        simp [liftScope, scopeInclusion, Language.BoundedFormula.relabelAux, Term.relabel, hcast]


private theorem qf_falsum {n} :
    (_root_.FirstOrder.Language.BoundedFormula.falsum : L.BoundedFormula α n).IsQF ↔ True :=
  iff_true_intro .falsum
private theorem qf_bot {n} :
    (⊥ : L.BoundedFormula α n).IsQF ↔ True :=
  iff_true_intro _root_.FirstOrder.Language.BoundedFormula.isQF_bot
private theorem qf_equal {n} (s t : L.Term (α ⊕ Fin n)) :
    (_root_.FirstOrder.Language.BoundedFormula.equal s t).IsQF ↔ True :=
  iff_true_intro (.of_isAtomic (.equal s t))
private theorem qf_rel {n k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) :
    (_root_.FirstOrder.Language.BoundedFormula.rel R ts).IsQF ↔ True :=
  iff_true_intro (.of_isAtomic (.rel R ts))
private theorem qf_imp {n} (A B : L.BoundedFormula α n) :
    (A.imp B).IsQF ↔ A.IsQF ∧ B.IsQF := by
  constructor
  · intro h
    cases h with
    | of_isAtomic h => cases h
    | imp hA hB => exact ⟨hA,hB⟩
  · rintro ⟨hA,hB⟩
    exact .imp hA hB
private theorem qf_all {n} (A : L.BoundedFormula α (n+1)) :
    A.all.IsQF ↔ False := iff_false_intro (_root_.FirstOrder.Language.BoundedFormula.not_all_isQF A)

namespace BoundedFormula

@[simp] theorem toClassical_map {n m} (A : BoundedFormula L α n)
    (σ : ScopeSubst L α β n m) :
    (A.map σ).toClassical = classicalMap A.toClassical σ := by
  induction A generalizing m with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | neg A ih => simp only [map, toClassical, _root_.FirstOrder.Language.BoundedFormula.not, classicalMap, ih]; rfl
  | conj A B ihA ihB => simp only [map, toClassical, min, _root_.FirstOrder.Language.BoundedFormula.not, classicalMap, ihA, ihB]; rfl
  | disj A B ihA ihB => simp only [map, toClassical, max, _root_.FirstOrder.Language.BoundedFormula.not, classicalMap, ihA, ihB]; rfl
  | impl A B ihA ihB => simp only [map, toClassical, classicalMap, ihA, ihB]
  | all A ih => simp only [map, toClassical, classicalMap, ih]
  | ex A ih => simp only [map, toClassical, _root_.FirstOrder.Language.BoundedFormula.ex, _root_.FirstOrder.Language.BoundedFormula.not, classicalMap, ih]; rfl


@[simp] theorem toClassical_subst {n} (A : BoundedFormula L α n) (σ : α → L.Term β) :
    (A.subst σ).toClassical = A.toClassical.subst σ := by
  rw [subst, toClassical_map, classicalMap_freeScope]


@[simp] theorem toClassical_ofClassical {n} (A : L.BoundedFormula α n) :
    (ofClassical A).toClassical = A := by
  induction A with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | imp A B ihA ihB => simp only [ofClassical, toClassical, ihA, ihB]
  | all A ih => simp only [ofClassical, toClassical, ih]


@[simp] theorem toClassical_freeVarFinset [DecidableEq α] {n} (A : BoundedFormula L α n) :
    A.toClassical.freeVarFinset = A.freeVarFinset := by
  induction A with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | neg A ih => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.not, _root_.FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty, freeVarFinset] using ih
  | conj A B ihA ihB => simpa only [toClassical, min, _root_.FirstOrder.Language.BoundedFormula.not, _root_.FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty, freeVarFinset] using congrArg₂ (fun (s t : Finset α) => s ∪ t) ihA ihB
  | disj A B ihA ihB => simpa only [toClassical, max, _root_.FirstOrder.Language.BoundedFormula.not, _root_.FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty, freeVarFinset] using congrArg₂ (fun (s t : Finset α) => s ∪ t) ihA ihB
  | impl A B ihA ihB => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.freeVarFinset, freeVarFinset] using congrArg₂ (fun (s t : Finset α) => s ∪ t) ihA ihB
  | all A ih => exact ih
  | ex A ih => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.ex, _root_.FirstOrder.Language.BoundedFormula.not, _root_.FirstOrder.Language.BoundedFormula.freeVarFinset, Finset.union_empty, freeVarFinset] using ih


@[simp] theorem toClassical_equalityFree {n} (A : BoundedFormula L α n) :
    classicalEqualityFree A.toClassical ↔ A.EqualityFree := by
  induction A <;> simp_all [toClassical, classicalEqualityFree, EqualityFree, min, max, _root_.FirstOrder.Language.BoundedFormula.not, _root_.FirstOrder.Language.BoundedFormula.ex]


@[simp] theorem toClassical_quantifierFree {n} (A : BoundedFormula L α n) :
    A.toClassical.IsQF ↔ A.QuantifierFree := by
  induction A <;> simp_all only [toClassical, QuantifierFree, min, max,
    _root_.FirstOrder.Language.BoundedFormula.not,
    _root_.FirstOrder.Language.BoundedFormula.ex,
    qf_falsum, qf_bot, qf_equal, qf_rel, qf_imp, qf_all, and_true]

@[simp] theorem toClassical_toFormula {n} (A : BoundedFormula L α n) :
    A.toFormula.toClassical = A.toClassical.toFormula := by
  rw [toFormula, toClassical_map, classicalMap_toFormula]

@[simp] theorem toClassical_instantiate (A : BoundedFormula L α 1) (t : L.Term α) :
    (A.instantiate t).toClassical =
      Lemmatheca.MathematicalLogic.FirstOrderProofs.instantiate A.toClassical t := by
  have h : A.instantiate t = A.toFormula.subst (Sum.elim Term.var (fun _ => t)) := by
    unfold instantiate instantiateSlots toFormula subst
    rw [map_comp]
    congr 1
    funext x
    cases x <;> rfl
  rw [h, toClassical_subst, toClassical_toFormula]
  rfl

variable {M : Type*} [L.Structure M]


private theorem extend_scopeInclusion {n} (a : α ⊕ Fin n → M) (x : M) :
    (extendAssignment a x) ∘ scopeInclusion n = a := by
  funext v
  cases v with
  | inl v => rfl
  | inr i => simp [scopeInclusion, extendAssignment]

private theorem eval_liftScope {n m} (σ : ScopeSubst L α β n m)
    (a : β ⊕ Fin m → M) (x : M) :
    (fun v => (liftScope σ v).realize (extendAssignment a x)) =
      extendAssignment (fun v => (σ v).realize a) x := by
  funext v
  cases v with
  | inl v =>
      change ((σ (.inl v)).relabel (scopeInclusion m)).realize (extendAssignment a x) = (σ (.inl v)).realize a
      rw [Term.realize_relabel, extend_scopeInclusion]
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [liftScope, extendAssignment]
      · simp only [liftScope, Sum.elim_inr, Fin.lastCases_castSucc]
        conv_rhs => simp only [extendAssignment, Sum.elim_inr, Fin.lastCases_castSucc]
        rw [Term.realize_relabel, extend_scopeInclusion]

private theorem extend_sum {n} (a : α → M) (b : Fin n → M) (x : M) :
    extendAssignment (Sum.elim a b) x = Sum.elim a (Fin.snoc b x) := by
  funext v
  cases v with
  | inl v => rfl
  | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [extendAssignment]
      · simp [extendAssignment]


theorem realize_map {n m} (A : BoundedFormula L α n) (σ : ScopeSubst L α β n m)
    (a : β ⊕ Fin m → M) :
    (A.map σ).realize a ↔ A.realize (fun x => (σ x).realize a) := by
  induction A generalizing m with
  | falsum => rfl
  | equal s t => simp only [map, realize, Term.realize_subst]
  | rel R ts => simp only [map, realize, Term.realize_subst]
  | neg A ih => exact not_congr (ih σ a)
  | conj A B ihA ihB => exact and_congr (ihA σ a) (ihB σ a)
  | disj A B ihA ihB => exact or_congr (ihA σ a) (ihB σ a)
  | impl A B ihA ihB => exact imp_congr (ihA σ a) (ihB σ a)
  | all A ih =>
      simp only [map, realize, ih, eval_liftScope]
  | ex A ih =>
      simp only [map, realize, ih, eval_liftScope]


theorem toClassical_realize {n} (A : BoundedFormula L α n) (a : α → M) (b : Fin n → M) :
    A.toClassical.Realize a b ↔ A.Realize a b := by
  induction A with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | neg A ih => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.realize_not, Realize, realize] using not_congr (ih b)
  | conj A B ihA ihB => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.realize_inf, Realize, realize] using and_congr (ihA b) (ihB b)
  | disj A B ihA ihB => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.realize_sup, Realize, realize] using or_congr (ihA b) (ihB b)
  | impl A B ihA ihB => simpa only [toClassical, _root_.FirstOrder.Language.BoundedFormula.realize_imp, Realize, realize] using imp_congr (ihA b) (ihB b)
  | all A ih =>
      simp only [toClassical, _root_.FirstOrder.Language.BoundedFormula.realize_all, ih, Realize, realize, extend_sum]
  | ex A ih =>
      simp only [toClassical, _root_.FirstOrder.Language.BoundedFormula.realize_ex, ih, Realize, realize, extend_sum]


end BoundedFormula
end Lemmatheca.ProofTheory.FirstOrder
