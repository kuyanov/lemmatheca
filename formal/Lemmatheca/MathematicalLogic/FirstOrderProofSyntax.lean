import Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-! Syntactic identities used by finite proof-tree transformations. -/
namespace Lemmatheca.MathematicalLogic.FirstOrderProofs
open FirstOrder FirstOrder.Language
universe u v w w' w'' w'''
variable {L : Language.{u, v}} {α : Type w} {β : Type w'} {γ : Type w''}
noncomputable section
local instance {δ : Type w} : DecidableEq (L.Formula δ) := Classical.decEq _
local instance {δ : Type w} : DecidableEq δ := Classical.decEq _

@[simp] theorem term_subst_subst (t : L.Term α) (σ : α → L.Term β) (τ : β → L.Term γ) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.subst, ih]

@[simp] theorem term_subst_relabel (t : L.Term α) (f : α → β) (σ : β → L.Term γ) :
    (t.relabel f).subst σ = t.subst (fun x => σ (f x)) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

@[simp] theorem term_relabel_subst (t : L.Term α) (σ : α → L.Term β) (f : β → γ) :
    (t.subst σ).relabel f = t.subst (fun x => (σ x).relabel f) := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

@[simp] theorem term_subst_var (t : L.Term α) : t.subst Term.var = t := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.subst, ih]

@[simp] theorem term_subst_vars (t : L.Term α) (f : α → β) :
    t.subst (fun x => .var (f x)) = t.relabel f := by
  induction t with
  | var x => rfl
  | func f ts ih => simp [Term.relabel, Term.subst, ih]

/-- Lift a substitution past a finite collection of protected names. -/
def liftSubst (σ : α → L.Term β) (n : ℕ) : α ⊕ Fin n → L.Term (β ⊕ Fin n) :=
  Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))

@[simp] theorem formula_subst_subst {n : ℕ} (φ : L.BoundedFormula α n)
    (σ : α → L.Term β) (τ : β → L.Term γ) :
    (φ.subst σ).subst τ = φ.subst (fun x => (σ x).subst τ) := by
  simp only [BoundedFormula.subst, BoundedFormula.mapTermRel_mapTermRel]
  congr 1
  funext k t
  simp only [Function.comp_apply, term_subst_subst]
  congr 1
  funext x
  cases x <;> simp [term_subst_relabel, term_relabel_subst]

@[simp] theorem formula_subst_var {n : ℕ} (φ : L.BoundedFormula α n) :
    φ.subst Term.var = φ := by
  have h (k : ℕ) : (Sum.elim (Term.relabel Sum.inl ∘ (Term.var : α → L.Term α))
      (Term.var ∘ Sum.inr) : α ⊕ Fin k → L.Term (α ⊕ Fin k)) = Term.var := by
    funext x
    cases x <;> rfl
  simp only [BoundedFormula.subst, h, term_subst_var]
  exact BoundedFormula.mapTermRel_id_id_id φ

theorem formula_subst_vars_aux {n : ℕ} (φ : L.BoundedFormula α n) (f : α → β) :
    (φ.relabel (Sum.inl ∘ f)).castLE (by omega : 0 + n ≤ n) =
      φ.subst (fun x => .var (f x)) := by
  have h (k : ℕ) : (Sum.elim (Term.relabel Sum.inl ∘ (fun x =>
      (Term.var (f x) : L.Term β))) (Term.var ∘ Sum.inr) :
      α ⊕ Fin k → L.Term (β ⊕ Fin k)) = fun x => .var (Sum.map f id x) := by
    funext x
    cases x <;> rfl
  induction φ with
  | falsum => rfl
  | equal s t =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.castLE, BoundedFormula.subst, h, term_subst_vars,
        Term.relabel_relabel]
      congr 1 <;> (congr 1; funext x; cases x <;> simp [BoundedFormula.relabelAux]; exact Fin.ext rfl)
  | rel R ts =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.castLE, BoundedFormula.subst, h, term_subst_vars]
      congr 1
      funext i
      simp only [Function.comp_apply, Term.relabel_relabel]
      congr 1
      funext x
      cases x <;> simp [BoundedFormula.relabelAux]
      exact Fin.ext rfl
  | imp φ ψ ihφ ihψ =>
      simp only [BoundedFormula.relabel_imp, BoundedFormula.castLE, BoundedFormula.subst,
        BoundedFormula.mapTermRel] at ihφ ihψ ⊢
      exact congrArg₂ BoundedFormula.imp ihφ ihψ
  | all φ ih =>
      simp only [BoundedFormula.relabel_all, BoundedFormula.castLE]
      change _ = (φ.subst _).all
      exact congrArg BoundedFormula.all ih

@[simp] theorem formula_subst_vars (φ : L.Formula α) (f : α → β) :
    φ.subst (fun x => .var (f x)) = φ.relabel f := by
  simpa only [Formula.relabel, BoundedFormula.castLE_rfl] using
    (formula_subst_vars_aux φ f).symm

@[simp] theorem formula_subst_bot {n : ℕ} (σ : α → L.Term β) :
    (⊥ : L.BoundedFormula α n).subst σ = ⊥ := rfl
@[simp] theorem formula_subst_imp {n : ℕ} (φ ψ : L.BoundedFormula α n)
    (σ : α → L.Term β) : (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl
@[simp] theorem formula_subst_not {n : ℕ} (φ : L.BoundedFormula α n)
    (σ : α → L.Term β) : φ.not.subst σ = (φ.subst σ).not := rfl
@[simp] theorem formula_subst_all {n : ℕ} (φ : L.BoundedFormula α (n+1))
    (σ : α → L.Term β) : φ.all.subst σ = (φ.subst σ).all := rfl
@[simp] theorem formula_subst_ex {n : ℕ} (φ : L.BoundedFormula α (n+1))
    (σ : α → L.Term β) : φ.ex.subst σ = (φ.subst σ).ex := rfl
@[simp] theorem formula_subst_inf {n : ℕ} (φ ψ : L.BoundedFormula α n)
    (σ : α → L.Term β) : (φ ⊓ ψ).subst σ = φ.subst σ ⊓ ψ.subst σ := rfl
@[simp] theorem formula_subst_sup {n : ℕ} (φ ψ : L.BoundedFormula α n)
    (σ : α → L.Term β) : (φ ⊔ ψ).subst σ = φ.subst σ ⊔ ψ.subst σ := rfl

/-- Renaming names into free or protected slots commutes with substitution when
all term images agree. -/
theorem relabel_subst_comm {m n : ℕ} {δ : Type w'''}
    (φ : L.BoundedFormula α n) (f : α → β ⊕ Fin m)
    (g : γ → δ ⊕ Fin m) (σ : α → L.Term γ) (τ : β → L.Term δ)
    (h : ∀ x, (σ x).relabel g = (Term.var (f x)).subst (liftSubst τ m)) :
    (φ.subst σ).relabel g = (φ.relabel f).subst τ := by
  induction φ with
  | falsum => rfl
  | @equal n s t =>
      simp only [BoundedFormula.subst, BoundedFormula.relabel,
        BoundedFormula.mapTermRel]
      congr 1 <;> rw [term_relabel_subst, term_subst_relabel]
      all_goals congr 1; funext x; cases x with
      | inl x =>
          have hg : BoundedFormula.relabelAux g n ∘ Sum.inl =
              Sum.map id (Fin.castAdd n) ∘ g := by
            funext z
            cases e : g z <;> simp [BoundedFormula.relabelAux, e]
          simp only [Sum.elim_inl, Function.comp_apply, Term.relabel_relabel]
          rw [hg]
          have hx := congrArg (Term.relabel (Sum.map id (Fin.castAdd n))) (h x)
          rw [Term.relabel_relabel] at hx
          rw [hx]
          cases hf : f x <;> simp [liftSubst, hf, BoundedFormula.relabelAux,
            Term.relabel_relabel, Function.comp_def]
      | inr i => simp [BoundedFormula.relabelAux]
  | @rel n l R ts =>
      simp only [BoundedFormula.subst, BoundedFormula.relabel,
        BoundedFormula.mapTermRel]
      congr 1
      funext i
      rw [term_relabel_subst, term_subst_relabel]
      congr 1
      funext x
      cases x with
      | inl x =>
          have hg : BoundedFormula.relabelAux g n ∘ Sum.inl =
              Sum.map id (Fin.castAdd n) ∘ g := by
            funext z
            cases e : g z <;> simp [BoundedFormula.relabelAux, e]
          simp only [Sum.elim_inl, Function.comp_apply, Term.relabel_relabel]
          rw [hg]
          have hx := congrArg (Term.relabel (Sum.map id (Fin.castAdd n))) (h x)
          rw [Term.relabel_relabel] at hx
          rw [hx]
          cases hf : f x <;> simp [liftSubst, hf, BoundedFormula.relabelAux,
            Term.relabel_relabel, Function.comp_def]
      | inr i => simp [BoundedFormula.relabelAux]
  | imp φ ψ ihφ ihψ => simp only [formula_subst_imp, BoundedFormula.relabel_imp, ihφ, ihψ]
  | all φ ih => simp only [formula_subst_all, BoundedFormula.relabel_all, ih]

@[simp] theorem toFormula_subst {n : ℕ} (φ : L.BoundedFormula α n)
    (σ : α → L.Term β) :
    (φ.subst σ).toFormula = φ.toFormula.subst (liftSubst σ n) := by
  induction φ with
  | falsum => rfl
  | equal s t =>
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel,
        BoundedFormula.toFormula, Term.equal, Term.bdEqual]
      congr 1 <;> simp [term_relabel_subst, term_subst_relabel, liftSubst,
        Function.comp_def]
  | rel R ts =>
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel,
        BoundedFormula.toFormula, Relations.formula, Relations.boundedFormula]
      congr 1
      funext i
      simp [term_relabel_subst, term_subst_relabel, liftSubst, Function.comp_def]
  | imp φ ψ ihφ ihψ => simp only [formula_subst_imp, BoundedFormula.toFormula, ihφ, ihψ]
  | @all n φ ih =>
      simp only [formula_subst_all, BoundedFormula.toFormula, ih]
      congr 1
      apply relabel_subst_comm
      intro x
      cases x with
      | inl x => simp [liftSubst, Term.relabel_relabel, Function.comp_def]
      | inr i =>
          rcases e : finSumFinEquiv.symm i with j | j <;> simp [liftSubst, Term.subst, Term.relabel, e]

theorem relabelAux_comp (m n k : ℕ)
    (f : α → β ⊕ Fin m) (g : β → γ ⊕ Fin n) :
    Sum.map id (Fin.castLE (by omega : n + (m+k) ≤ (n+m)+k)) ∘
      BoundedFormula.relabelAux g (m+k) ∘ BoundedFormula.relabelAux f k =
      BoundedFormula.relabelAux (BoundedFormula.relabelAux g m ∘ f) k := by
  funext x
  cases x with
  | inl x =>
      cases ef : f x with
      | inl y =>
          cases eg : g y <;> simp [BoundedFormula.relabelAux, ef, eg]
          apply Fin.ext
          rfl
      | inr i =>
          simp [BoundedFormula.relabelAux, ef]
          apply Fin.ext
          rfl
  | inr i =>
      simp [BoundedFormula.relabelAux]
      apply Fin.ext
      simp [Nat.add_assoc]

theorem bounded_relabel_comp {m n k : ℕ} (φ : L.BoundedFormula α k)
    (f : α → β ⊕ Fin m) (g : β → γ ⊕ Fin n) :
    ((φ.relabel f).relabel g).castLE (by omega : n + (m+k) ≤ (n+m)+k) =
      φ.relabel (BoundedFormula.relabelAux g m ∘ f) := by
  induction φ with
  | falsum => rfl
  | equal s t =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.castLE, Term.relabel_relabel]
      congr 1 <;> (congr 1; exact relabelAux_comp _ _ _ _ _)
  | rel R ts =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.castLE]
      congr 1
      funext i
      simp only [Function.comp_apply, Term.relabel_relabel]
      congr 1
      exact relabelAux_comp _ _ _ _ _
  | imp φ ψ ihφ ihψ =>
      simp only [BoundedFormula.relabel_imp, BoundedFormula.castLE]
      exact congrArg₂ BoundedFormula.imp ihφ ihψ
  | all φ ih =>
      simp only [BoundedFormula.relabel_all, BoundedFormula.castLE]
      exact congrArg BoundedFormula.all ih

@[simp] theorem relabel_toFormula {n : ℕ} (φ : L.BoundedFormula α n) :
    (BoundedFormula.relabel id φ.toFormula : L.BoundedFormula α n) = φ := by
  induction φ with
  | falsum => rfl
  | @equal n s t =>
      simp only [BoundedFormula.toFormula, Term.equal, Term.bdEqual,
        BoundedFormula.relabel, BoundedFormula.mapTermRel, Term.relabel_relabel]
      have h : BoundedFormula.relabelAux (id : α ⊕ Fin n → α ⊕ Fin n) 0 ∘ Sum.inl = id := by
        funext x
        cases x <;> simp [BoundedFormula.relabelAux]
        exact Fin.ext rfl
      simp only [h, Term.relabel_id]
  | @rel n l R ts =>
      simp only [BoundedFormula.toFormula, Relations.formula, Relations.boundedFormula,
        BoundedFormula.relabel, BoundedFormula.mapTermRel, Term.relabel_relabel]
      have h : BoundedFormula.relabelAux (id : α ⊕ Fin n → α ⊕ Fin n) 0 ∘ Sum.inl = id := by
        funext x
        cases x <;> simp [BoundedFormula.relabelAux]
        exact Fin.ext rfl
      simp only [h, Term.relabel_id]
      rfl
  | imp φ ψ ihφ ihψ =>
      simp only [BoundedFormula.toFormula, BoundedFormula.relabel_imp, ihφ, ihψ]
  | @all n φ ih =>
      simp only [BoundedFormula.toFormula, BoundedFormula.relabel_all]
      congr 1
      have hh := bounded_relabel_comp φ.toFormula
        (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm))
        (id : α ⊕ Fin n → α ⊕ Fin n)
      simp only [BoundedFormula.castLE_rfl] at hh
      rw [hh]
      have hf : BoundedFormula.relabelAux (id : α ⊕ Fin n → α ⊕ Fin n) 1 ∘
          Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ finSumFinEquiv.symm) = id := by
        funext x
        cases x with
        | inl x => simp [BoundedFormula.relabelAux]
        | inr i =>
            rcases e : finSumFinEquiv.symm i with j | j
            · have hi := congrArg finSumFinEquiv e
              simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left] at hi
              simp [BoundedFormula.relabelAux, hi]
            · have hi := congrArg finSumFinEquiv e
              simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right] at hi
              simp [BoundedFormula.relabelAux, hi]
      rw [hf]
      exact ih

@[simp] theorem toFormula_relabel {m n : ℕ} (φ : L.BoundedFormula α n)
    (f : α → β ⊕ Fin m) :
    (φ.relabel f).toFormula = φ.toFormula.relabel (BoundedFormula.relabelAux f n) := by
  induction φ with
  | equal s t =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.toFormula, Formula.relabel, Term.equal, Term.bdEqual]
      congr 1 <;> simp [Term.relabel_relabel, BoundedFormula.relabelAux, Function.comp_def]
  | rel R ts =>
      simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
        BoundedFormula.toFormula, Formula.relabel, Relations.formula,
        Relations.boundedFormula]
      congr 1
      funext i
      simp only [Term.relabel_relabel]
      congr 1
  | falsum => rfl
  | imp φ ψ ihφ ihψ =>
      simp only [BoundedFormula.relabel_imp, BoundedFormula.toFormula, ihφ, ihψ]
      rfl
  | @all n φ ih =>
      simp only [BoundedFormula.relabel_all, BoundedFormula.toFormula, ih,
        Formula.relabel, BoundedFormula.relabel_all]
      congr 1
      have hs := formula_subst_vars_aux
        (BoundedFormula.relabel (Sum.elim (Sum.inl ∘ Sum.inl)
          (Sum.map Sum.inr id ∘ finSumFinEquiv.symm)) φ.toFormula :
          L.BoundedFormula (α ⊕ Fin n) 1)
        (BoundedFormula.relabelAux f n)
      simp only [BoundedFormula.castLE_rfl] at hs
      rw [hs]
      change BoundedFormula.relabel _
        (Formula.relabel (BoundedFormula.relabelAux f (n+1)) φ.toFormula) = _
      rw [← formula_subst_vars]
      apply relabel_subst_comm
      intro x
      cases x with
      | inl x =>
          cases e : f x with
          | inl y => simp [BoundedFormula.relabelAux, liftSubst, e]
          | inr j =>
              have hj : Fin.castAdd (n+1) j = (Fin.castAdd n j).castAdd 1 := Fin.ext rfl
              simp [BoundedFormula.relabelAux, liftSubst, e, hj]
      | inr i =>
          rcases e : finSumFinEquiv.symm i with j | j
          · have hi := congrArg finSumFinEquiv e
            simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_left] at hi
            have hj : Fin.natAdd m (j.castAdd 1) = (Fin.natAdd m j).castAdd 1 := Fin.ext rfl
            simp [BoundedFormula.relabelAux, liftSubst, hi, hj]
          · have hi := congrArg finSumFinEquiv e
            simp only [Equiv.apply_symm_apply, finSumFinEquiv_apply_right] at hi
            have hj : Fin.natAdd m (Fin.natAdd n j) = Fin.natAdd (m+n) j := by
              apply Fin.ext
              simp only [Fin.val_natAdd, Nat.add_assoc]
            simp [BoundedFormula.relabelAux, liftSubst, hi, hj]

/-- Open the distinguished bound slot at one term. -/
def instantiate (φ : L.BoundedFormula α 1) (t : L.Term α) : L.Formula α :=
  φ.toFormula.subst (Sum.elim Term.var (fun _ => t))

/-- Simultaneously fill finitely many distinguished slots with terms. -/
def instantiateSlots {n : ℕ} (φ : L.BoundedFormula α n) (ts : Fin n → L.Term α) :
    L.Formula α := φ.toFormula.subst (Sum.elim Term.var ts)

/-- Add a new parameter name disjoint from the old names. -/
def liftContext (Γ : Finset (L.Formula α)) : Finset (L.Formula (α ⊕ Fin 1)) := by
  classical
  exact Γ.image (Formula.relabel Sum.inl)

@[simp] theorem formula_relabel_subst (φ : L.Formula α) (f : α → β)
    (σ : β → L.Term γ) :
    (φ.relabel f).subst σ = φ.subst (fun x => σ (f x)) := by
  rw [← formula_subst_vars, formula_subst_subst]
  rfl

@[simp] theorem formula_subst_relabel (φ : L.Formula α) (σ : α → L.Term β)
    (f : β → γ) :
    Formula.relabel f (φ.subst σ) = φ.subst (fun x => (σ x).relabel f) := by
  rw [← formula_subst_vars, formula_subst_subst]
  simp only [term_subst_vars]

@[simp] theorem formula_relabel_relabel (φ : L.Formula α) (f : α → β) (g : β → γ) :
    (φ.relabel f).relabel g = φ.relabel (g ∘ f) := by
  rw [← formula_subst_vars, formula_relabel_subst]
  exact formula_subst_vars _ _

@[simp] theorem instantiate_subst (φ : L.BoundedFormula α 1) (t : L.Term α)
    (σ : α → L.Term β) :
    (instantiate φ t).subst σ = instantiate (φ.subst σ) (t.subst σ) := by
  simp only [instantiate, toFormula_subst, formula_subst_subst]
  congr 1
  funext x
  cases x <;> simp [liftSubst, term_subst_relabel, Term.subst]

@[simp] theorem instantiate_relabel (φ : L.BoundedFormula α 1) (t : L.Term α)
    (f : α → β) :
    (instantiate φ t).relabel f =
      instantiate (φ.subst (fun x => .var (f x))) (t.relabel f) := by
  rw [← formula_subst_vars, instantiate_subst, term_subst_vars]

@[simp] theorem formula_subst_equal (s t : L.Term α) (σ : α → L.Term β) :
    (s.equal t).subst σ = (s.subst σ).equal (t.subst σ) := by
  simp only [Term.equal, Term.bdEqual, BoundedFormula.subst,
    BoundedFormula.mapTermRel]
  congr 1 <;> simp [term_subst_relabel, term_relabel_subst, Function.comp_def]

@[simp] theorem liftContext_subst (Γ : Finset (L.Formula α)) (σ : α → L.Term β) :
    (liftContext Γ).image (fun φ => φ.subst (liftSubst σ 1)) =
      liftContext (Γ.image (fun φ => φ.subst σ)) := by
  classical
  simp only [liftContext, Finset.image_image]
  congr 1
  funext φ
  simp only [Function.comp_apply, formula_relabel_subst, formula_subst_relabel]
  rfl

@[simp] theorem formula_relabel_id (φ : L.Formula α) : φ.relabel id = φ := by
  rw [← formula_subst_vars]
  exact formula_subst_var φ

@[simp] theorem toFormula_zero (φ : L.Formula α) :
    φ.toFormula = φ.relabel Sum.inl := by
  let p : α ⊕ Fin 0 → α := Sum.elim id Fin.elim0
  have hp : Sum.inl ∘ p = id := by
    funext x
    cases x with
    | inl x => rfl
    | inr i => exact Fin.elim0 i
  have h : Formula.relabel p φ.toFormula = φ := by
    have hr := relabel_toFormula φ
    simpa only [Formula.relabel, hp] using hr
  calc
    φ.toFormula = Formula.relabel Sum.inl (Formula.relabel p φ.toFormula) := by
      rw [formula_relabel_relabel, hp, formula_relabel_id]
    _ = φ.relabel Sum.inl := congrArg (Formula.relabel Sum.inl) h

/-- Capturing a selected free name and then opening it is ordinary substitution. -/
theorem instantiate_capture (φ : L.Formula γ) (f : γ → α ⊕ Fin 1) (t : L.Term α) :
    instantiate (BoundedFormula.relabel f φ) t =
      φ.subst (fun x => Sum.elim Term.var (fun _ => t) (f x)) := by
  simp only [instantiate, toFormula_relabel, toFormula_zero, formula_relabel_subst]
  congr 1
  funext x
  cases e : f x with
  | inl y => simp [BoundedFormula.relabelAux, e]
  | inr i =>
      simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl, e]
      rfl

/-- Substitutions agreeing on the names in a term have identical results. -/
theorem term_subst_agree_left {n : ℕ} (t : L.Term (α ⊕ Fin n))
    (σ τ : α → L.Term β) (h : ∀ x ∈ t.varFinsetLeft, σ x = τ x) :
    t.subst (liftSubst σ n) = t.subst (liftSubst τ n) := by
  revert h
  induction t with
  | var x =>
      intro h
      cases x with
      | inl x => simp only [Term.subst, liftSubst, Sum.elim_inl, h x (by simp)]
      | inr i => rfl
  | func f ts ih =>
      intro h
      simp only [Term.subst]
      congr 1
      funext i
      apply ih i
      intro x hx
      apply h x
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

/-- A formula depends syntactically only on its occurring free names. -/
theorem formula_subst_agree {n : ℕ} (φ : L.BoundedFormula α n)
    (σ τ : α → L.Term β) (h : ∀ x ∈ φ.freeVarFinset, σ x = τ x) :
    φ.subst σ = φ.subst τ := by
  revert h
  induction φ with
  | falsum => intro _; rfl
  | equal s t =>
      intro h
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel]
      congr 1
      · exact term_subst_agree_left s σ τ (fun x hx => h x (Finset.mem_union_left _ hx))
      · exact term_subst_agree_left t σ τ (fun x hx => h x (Finset.mem_union_right _ hx))
  | rel R ts =>
      intro h
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel]
      congr 1
      funext i
      apply term_subst_agree_left (ts i) σ τ
      intro x hx
      exact h x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  | imp φ ψ ihφ ihψ =>
      intro h
      exact congrArg₂ BoundedFormula.imp
        (ihφ (fun x hx => h x (Finset.mem_union_left _ hx)))
        (ihψ (fun x hx => h x (Finset.mem_union_right _ hx)))
  | all φ ih => intro h; exact congrArg BoundedFormula.all (ih h)

@[simp] theorem instantiate_lifted (φ : L.BoundedFormula α 1) :
    instantiate (φ.subst (fun x => .var (.inl x))) (.var (.inr 0)) = φ.toFormula := by
  simp only [instantiate, toFormula_subst, formula_subst_subst]
  have h : (fun x => (liftSubst (fun x : α => (Term.var (.inl x) : L.Term (α ⊕ Fin 1))) 1 x).subst
      (Sum.elim Term.var (fun _ => .var (.inr 0)))) = Term.var := by
    funext x
    cases x with
    | inl x => rfl
    | inr i => rw [Fin.eq_zero i]; rfl
  rw [h, formula_subst_var]

end
end Lemmatheca.MathematicalLogic.FirstOrderProofs
