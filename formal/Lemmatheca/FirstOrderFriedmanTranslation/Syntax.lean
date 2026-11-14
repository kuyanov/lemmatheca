import Lemmatheca.IntuitionisticFirstOrderDeduction.Structural

/-! Full scoped Friedman translation. A parameter is protected from every newly
bound slot, while scope substitutions act on both the source and the parameter. -/
namespace Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation

open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {β : Type b}

noncomputable section
local instance friedmanSyntaxFormulaEq {δ : Type*} : DecidableEq (Formula L δ) :=
  Classical.decEq _

/-- Add one available slot without making it accessible to the parameter. -/
def protect {n} (R : BoundedFormula L α n) : BoundedFormula L α (n+1) :=
  R.map (fun x => .var (scopeInclusion n x))

/-- Full native translation, with the parameter inserted whole. -/
def formula : ∀ {n}, BoundedFormula L α n → BoundedFormula L α n → BoundedFormula L α n
  | _, R, .falsum => R
  | _, R, .equal s t => .disj (.equal s t) R
  | _, R, .rel P ts => .disj (.rel P ts) R
  | _, R, .neg A => .impl (formula R A) R
  | _, R, .conj A B => .conj (formula R A) (formula R B)
  | _, R, .disj A B => .disj (formula R A) (formula R B)
  | _, R, .impl A B => .impl (formula R A) (formula R B)
  | _, R, .all B => .all (formula (protect R) B)
  | _, R, .ex B => .ex (formula (protect R) B)

/-- The translated one-slot body belonging to a complete ambient parameter. -/
def body (R : Formula L α) (B : BoundedFormula L α 1) : BoundedFormula L α 1 :=
  formula (protect R) B

def context (R : Formula L α) (Γ : NaturalDeduction.Context L α) :
    NaturalDeduction.Context L α := Γ.image (formula R)

def theory (R : Formula L α) (T : Set (Formula L α)) : Set (Formula L α) :=
  formula R '' T

theorem protect_map {n m} (R : BoundedFormula L α n) (σ : ScopeSubst L α β n m) :
    (protect R).map (liftScope σ) = protect (R.map σ) := by
  unfold protect
  rw [BoundedFormula.map_comp, BoundedFormula.map_comp]
  congr 1
  funext x
  simp only [Term.subst, liftScope_inclusion, term_subst_vars]

theorem formula_map {n m} (R A : BoundedFormula L α n) (σ : ScopeSubst L α β n m) :
    (formula R A).map σ = formula (R.map σ) (A.map σ) := by
  induction A generalizing m with
  | falsum => rfl
  | equal s t => rfl
  | rel P ts => rfl
  | neg A ih => simp only [formula, BoundedFormula.map, ih]
  | conj A B ihA ihB => simp only [formula, BoundedFormula.map, ihA, ihB]
  | disj A B ihA ihB => simp only [formula, BoundedFormula.map, ihA, ihB]
  | impl A B ihA ihB => simp only [formula, BoundedFormula.map, ihA, ihB]
  | all B ih => simp only [formula, BoundedFormula.map, ih, protect_map]
  | ex B ih => simp only [formula, BoundedFormula.map, ih, protect_map]

theorem formula_subst {n} (R A : BoundedFormula L α n) (σ : α → L.Term β) :
    (formula R A).subst σ = formula (R.subst σ) (A.subst σ) := by
  exact formula_map R A _

theorem formula_rename {n} (R A : BoundedFormula L α n) (f : α → β) :
    (formula R A).rename f = formula (R.rename f) (A.rename f) := by
  exact formula_subst R A _

theorem formula_open {n} (R A : BoundedFormula L α n) :
    (formula R A).toFormula = formula R.toFormula A.toFormula := by
  exact formula_map R A _

theorem formula_instantiateSlots {n} (R A : BoundedFormula L α n) (ts : Fin n → L.Term α) :
    (formula R A).instantiateSlots ts =
      formula (R.instantiateSlots ts) (A.instantiateSlots ts) := by
  exact formula_map R A _

theorem formula_instantiate (R A : BoundedFormula L α 1) (t : L.Term α) :
    (formula R A).instantiate t = formula (R.instantiate t) (A.instantiate t) := by
  exact formula_instantiateSlots R A _

theorem protect_open (R : Formula L α) :
    (protect R).toFormula = R.rename (Sum.inl : α → α ⊕ Fin 1) := by
  unfold protect BoundedFormula.toFormula BoundedFormula.rename BoundedFormula.subst
  rw [BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i => exact Fin.elim0 i

theorem protect_instantiate (R : Formula L α) (t : L.Term α) :
    (protect R).instantiate t = R := by
  unfold protect BoundedFormula.instantiate BoundedFormula.instantiateSlots
  rw [BoundedFormula.map_comp]
  convert R.map_id using 1
  congr 1
  funext x
  cases x with
  | inl a => rfl
  | inr i => exact Fin.elim0 i

theorem body_open (R : Formula L α) (B : BoundedFormula L α 1) :
    (body R B).toFormula = formula (R.rename Sum.inl) B.toFormula := by
  simp only [body, formula_open, protect_open]

theorem body_instantiate (R : Formula L α) (B : BoundedFormula L α 1) (t : L.Term α) :
    (body R B).instantiate t = formula R (B.instantiate t) := by
  simp only [body, formula_instantiate, protect_instantiate]

theorem context_insert (R C : Formula L α) (Γ : NaturalDeduction.Context L α) :
    context R (insert C Γ) = insert (formula R C) (context R Γ) := by
  simp only [context, Finset.image_insert]

theorem context_union (R : Formula L α) (Γ Δ : NaturalDeduction.Context L α) :
    context R (Γ ∪ Δ) = context R Γ ∪ context R Δ := by
  simp only [context, Finset.image_union]

theorem context_rename (R : Formula L α) (Γ : NaturalDeduction.Context L α) (f : α → β) :
    context (R.rename f) (Γ.image (fun C => C.rename f)) =
      (context R Γ).image (fun C => C.rename f) := by
  simp only [context, Finset.image_image, Function.comp_def, ← formula_rename]

theorem context_lift (R : Formula L α) (Γ : NaturalDeduction.Context L α) :
    context (R.rename Sum.inl) (NaturalDeduction.liftContext Γ) =
      NaturalDeduction.liftContext (context R Γ) := by
  exact context_rename R Γ (Sum.inl : α → α ⊕ Fin 1)

end
end Lemmatheca.ProofTheory.FirstOrder.FriedmanTranslation
