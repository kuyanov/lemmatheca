import Lemmatheca.IntuitionisticFirstOrderDeduction.Structural
import Lemmatheca.FirstOrderProofs.FirstOrderProofs

/-! The literal inclusion and context identities used by classical proof
translations. Full and small formulas share the actual terms and slot indices. -/
namespace Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
open _root_.FirstOrder _root_.FirstOrder.Language
abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula
universe u v w w' w''
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}
noncomputable section
local instance syntaxFullFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (Formula K δ) := Classical.decEq _
local instance syntaxSmallFormulaEq {K : Language.{u,v}} {δ : Type*} :
    DecidableEq (K.Formula δ) := Classical.decEq _

/-- Expand each member of the finite full context. -/
def expandContext (Γ : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α) : Finset (L.Formula α) :=
  Γ.image Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical
/-- Include each member of the finite small context. -/
def includeContext (Γ : Finset (L.Formula α)) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context L α :=
  Γ.image Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical
/-- Expand a full tree and then include its exact small tree again. -/
def expanded {n} (A : BF L α n) : BF L α n := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical A.toClassical

@[simp] theorem ofClassical_map {n m} (D : L.BoundedFormula α n)
    (σ : ScopeSubst L α β n m) :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical (classicalMap D σ) = (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).map σ := by
  induction D generalizing m <;> simp_all [classicalMap, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map]
@[simp] theorem ofClassical_subst {n} (D : L.BoundedFormula α n) (σ : α → L.Term β) :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical (D.subst σ) = (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).subst σ := by
  rw [← classicalMap_freeScope D σ, ofClassical_map]
  rfl
@[simp] theorem ofClassical_rename (D : L.Formula α) (f : α → β) :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical (D.relabel f) = (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).rename f := by
  rw [← Lemmatheca.MathematicalLogic.FirstOrderProofs.formula_subst_vars, ofClassical_subst]
  rfl
@[simp] theorem ofClassical_toFormula {n} (D : L.BoundedFormula α n) :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D.toFormula = (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).toFormula := by
  rw [← classicalMap_toFormula D, ofClassical_map]
  rfl
@[simp] theorem ofClassical_instantiate (D : L.BoundedFormula α 1) (t : L.Term α) :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical (Lemmatheca.MathematicalLogic.FirstOrderProofs.instantiate D t) = (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).instantiate t := by
  unfold Lemmatheca.MathematicalLogic.FirstOrderProofs.instantiate
  rw [ofClassical_subst, ofClassical_toFormula]
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x <;> rfl
@[simp] theorem ofClassical_support [DecidableEq α] {n} (D : L.BoundedFormula α n) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).freeVarFinset = D.freeVarFinset := by
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_ofClassical] using
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_freeVarFinset (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)).symm
@[simp] theorem ofClassical_equalityFree {n} (D : L.BoundedFormula α n) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).EqualityFree ↔ classicalEqualityFree D := by
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_ofClassical] using
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_equalityFree (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)).symm
@[simp] theorem ofClassical_quantifierFree {n} (D : L.BoundedFormula α n) :
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D).QuantifierFree ↔ D.IsQF := by
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_ofClassical] using
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_quantifierFree (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ofClassical D)).symm

@[simp] theorem expanded_map {n m} (A : BF L α n) (σ : ScopeSubst L α β n m) :
    expanded (A.map σ) = (expanded A).map σ := by
  unfold expanded
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_map, ofClassical_map]
@[simp] theorem expanded_support [DecidableEq α] {n} (A : BF L α n) :
    (expanded A).freeVarFinset = A.freeVarFinset := by
  simp only [expanded, ofClassical_support, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_freeVarFinset]
@[simp] theorem expanded_equalityFree {n} (A : BF L α n) :
    (expanded A).EqualityFree ↔ A.EqualityFree := by
  simp only [expanded, ofClassical_equalityFree, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_equalityFree]
@[simp] theorem expanded_quantifierFree {n} (A : BF L α n) :
    (expanded A).QuantifierFree ↔ A.QuantifierFree := by
  simp only [expanded, ofClassical_quantifierFree, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical_quantifierFree]

end
end Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation
