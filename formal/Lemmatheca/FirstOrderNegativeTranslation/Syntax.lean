import Lemmatheca.IntuitionisticFirstOrderDeduction.Structural

namespace Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v a b
variable {L : Language.{u,v}} {α : Type a} {e : Bool}
noncomputable section
local instance negativeSyntaxFormulaEq {β : Type*} : DecidableEq (Formula L β) := Classical.decEq _

/-- Gödel–Gentzen translation of every full native constructor at its original scope. -/
def negative : ∀ {n}, BoundedFormula L α n → BoundedFormula L α n
  | _, .falsum => .falsum
  | _, .equal s t => .neg (.neg (.equal s t))
  | _, .rel R ts => .neg (.neg (.rel R ts))
  | _, .neg A => .neg (negative A)
  | _, .conj A B => .conj (negative A) (negative B)
  | _, .disj A B => .neg (.neg (.disj (negative A) (negative B)))
  | _, .impl A B => .impl (negative A) (negative B)
  | _, .all A => .all (negative A)
  | _, .ex A => .neg (.neg (.ex (negative A)))

/-- Existence of an actual raw tree, without adding the public reserve. -/
def RawDerives (c e : Bool) (Γ : NaturalDeduction.Context L α) (A : Formula L α) : Prop :=
  Nonempty (NaturalDeduction.Derivation c e L Γ A)

/-- The finite image of the original allowed assumptions. -/
def context (Γ : NaturalDeduction.Context L α) : NaturalDeduction.Context L α := Γ.image negative

/-- The image of an arbitrary premise set. -/
def theory (T : Set (Formula L α)) : Set (Formula L α) := negative '' T

theorem negative_map {β : Type b} {n m} (A : BoundedFormula L α n)
    (σ : ScopeSubst L α β n m) : negative (A.map σ) = (negative A).map σ := by
  induction A generalizing m with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | neg A ih => simp only [negative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, ih]
  | conj A B ihA ihB => simp only [negative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, ihA, ihB]
  | disj A B ihA ihB => simp only [negative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, ihA, ihB]
  | impl A B ihA ihB => simp only [negative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, ihA, ihB]
  | all A ih => simp only [negative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, ih]
  | ex A ih => simp only [negative, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map, ih]

theorem negative_subst {β : Type b} {n} (A : BoundedFormula L α n) (σ : α → L.Term β) :
    negative (A.subst σ) = (negative A).subst σ := by
  exact negative_map A _

theorem negative_rename {β : Type b} {n} (A : BoundedFormula L α n) (f : α → β) :
    negative (A.rename f) = (negative A).rename f := by
  exact negative_subst A _

theorem negative_open {n} (A : BoundedFormula L α n) :
    negative A.toFormula = (negative A).toFormula := by
  exact negative_map A _

theorem negative_instantiateSlots {n} (A : BoundedFormula L α n) (ts : Fin n → L.Term α) :
    negative (A.instantiateSlots ts) = (negative A).instantiateSlots ts := by
  exact negative_map A _

theorem negative_instantiate (A : BoundedFormula L α 1) (t : L.Term α) :
    negative (A.instantiate t) = (negative A).instantiate t := by
  exact negative_instantiateSlots A _

theorem negative_support [DecidableEq α] {n} (A : BoundedFormula L α n) :
    (negative A).freeVarFinset = A.freeVarFinset := by
  induction A with
  | falsum => rfl
  | equal s t => rfl
  | rel R ts => rfl
  | neg A ih => exact ih
  | conj A B ihA ihB => exact congrArg₂ (fun s t : Finset α => s ∪ t) ihA ihB
  | disj A B ihA ihB => exact congrArg₂ (fun s t : Finset α => s ∪ t) ihA ihB
  | impl A B ihA ihB => exact congrArg₂ (fun s t : Finset α => s ∪ t) ihA ihB
  | all A ih => exact ih
  | ex A ih => exact ih

theorem context_insert (Γ : NaturalDeduction.Context L α) (A : Formula L α) :
    context (insert A Γ) = insert (negative A) (context Γ) := by
  simp only [context, Finset.image_insert]

theorem context_union (Γ Δ : NaturalDeduction.Context L α) :
    context (Γ ∪ Δ) = context Γ ∪ context Δ := by
  simp only [context, Finset.image_union]

theorem context_rename {β : Type b} (Γ : NaturalDeduction.Context L α) (f : α → β) :
    context (Γ.image (fun A => A.rename f)) = (context Γ).image (fun A => A.rename f) := by
  simp only [context, Finset.image_image, Function.comp_def, negative_rename]

theorem context_lift (Γ : NaturalDeduction.Context L α) :
    context (NaturalDeduction.liftContext Γ) = NaturalDeduction.liftContext (context Γ) := by
  exact context_rename Γ (Sum.inl : α → α ⊕ Fin 1)

end
end Lemmatheca.ProofTheory.FirstOrder.NegativeTranslation
