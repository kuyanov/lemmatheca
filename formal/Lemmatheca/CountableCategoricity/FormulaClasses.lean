import Lemmatheca.IsolatedTypes.IsolatedTypes
import Mathlib.ModelTheory.Equivalence

/-! Shared-syntax formula classes and their exact complete-type truth profiles. -/
namespace Lemmatheca.ModelTheory.CountableCategoricity

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types

universe u v w z
variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {β : Type z}

/-- The actual quotient of shared formulas by semantic equivalence over T. -/
abbrev FormulaClass (T : L.Theory) (α : Type w) :=
  Quotient (Theory.iffSetoid (α := α) (n := 0) T)

/-- The class of the specified shared-language formula. -/
def classOf (T : L.Theory) (φ : L.Formula α) : FormulaClass T α :=
  Quotient.mk _ φ

/-- Equivalent formulas have the same membership in every actual complete type. -/
theorem equivalent_membership (φ ψ : L.Formula α) (h : T.Iff φ ψ)
    (p : T.CompleteType α) : φ ∈ formulas p ↔ ψ ∈ formulas p := by
  obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in p
  rw [← ha]
  exact Theory.CompleteType.formula_mem_typeOf.trans
    (h.realize_iff.trans Theory.CompleteType.formula_mem_typeOf.symm)

/-- Send a formula class to precisely the complete types containing a representative. -/
def typeTruthSet (T : L.Theory) : FormulaClass T α → Set (T.CompleteType α) :=
  Quotient.lift (fun φ => {p | φ ∈ formulas p})
    (fun φ ψ h => Set.ext fun p => equivalent_membership φ ψ h p)

/-- The truth-set map retains exactly membership of the displayed formula. -/
theorem typeTruthSet_classOf (φ : L.Formula α) :
    typeTruthSet T (classOf T φ) = {p | φ ∈ formulas p} := by
  rfl

/-- Tuple types detect every failure of formula equivalence in a model. -/
theorem typeTruthSet_injective : Function.Injective (typeTruthSet (α := α) T) := by
  intro c d h
  induction c using Quotient.inductionOn with | h φ =>
    induction d using Quotient.inductionOn with | h ψ =>
      apply Quotient.sound
      apply Theory.models_formula_iff.mpr
      intro N a
      apply Formula.realize_iff.mpr
      have hp := Set.ext_iff.mp h (T.typeOf a)
      change φ ∈ formulas (T.typeOf a) ↔ ψ ∈ formulas (T.typeOf a) at hp
      exact Theory.CompleteType.formula_mem_typeOf.symm.trans
        (hp.trans Theory.CompleteType.formula_mem_typeOf)

/-- The Boolean profile of a type records its membership in every formula class. -/
def typeProfile (p : T.CompleteType α) : Set (FormulaClass T α) :=
  {c | p ∈ typeTruthSet T c}

/-- Different complete types give different sets of formula classes. -/
theorem typeProfile_injective : Function.Injective (typeProfile (T := T) (α := α)) := by
  intro p q h
  apply SetLike.ext
  intro γ
  change γ ∈ p.toTheory ↔ γ ∈ q.toTheory
  have hc := Set.ext_iff.mp h (classOf T (Formula.equivSentence.symm γ))
  change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ p.toTheory ↔
    Formula.equivSentence (Formula.equivSentence.symm γ) ∈ q.toTheory at hc
  simpa only [Equiv.apply_symm_apply] using hc

/-- Both directions use the actual truth-set and type-profile injections into power sets. -/
theorem finite_types_iff_formulaClasses :
    Finite (T.CompleteType α) ↔ Finite (FormulaClass T α) := by
  constructor
  · intro h
    let := h
    exact Finite.of_injective _ typeTruthSet_injective
  · intro h
    let := h
    exact Finite.of_injective _ typeProfile_injective

/-- Renaming free names gives an equivalence of these same formula quotients. -/
theorem context_equiv (e : α ≃ β) :
    ∃ E : FormulaClass T α ≃ FormulaClass T β,
      ∀ φ : L.Formula α, E (classOf T φ) = classOf T (Formula.relabel e φ) := by
  have hf (φ ψ : L.Formula α) (h : T.Iff φ ψ) :
      T.Iff (Formula.relabel e φ) (Formula.relabel e ψ) := by
    apply Theory.models_formula_iff.mpr
    intro N a
    exact Formula.realize_iff.mpr (by
      simpa only [Formula.realize_relabel] using (h.realize_iff (v := a ∘ e)))
  have hg (φ ψ : L.Formula β) (h : T.Iff φ ψ) :
      T.Iff (Formula.relabel e.symm φ) (Formula.relabel e.symm ψ) := by
    apply Theory.models_formula_iff.mpr
    intro N a
    exact Formula.realize_iff.mpr (by
      simpa only [Formula.realize_relabel] using (h.realize_iff (v := a ∘ e.symm)))
  let f : FormulaClass T α → FormulaClass T β :=
    Quotient.lift (fun φ => classOf T (Formula.relabel e φ))
      (fun φ ψ h => Quotient.sound (hf φ ψ h))
  let g : FormulaClass T β → FormulaClass T α :=
    Quotient.lift (fun φ => classOf T (Formula.relabel e.symm φ))
      (fun φ ψ h => Quotient.sound (hg φ ψ h))
  have hgf : Function.LeftInverse g f := by
    intro c
    induction c using Quotient.inductionOn with | h φ =>
      apply Quotient.sound
      apply Theory.models_formula_iff.mpr
      intro N a
      apply Formula.realize_iff.mpr
      simp only [Formula.realize_relabel]
      have heq : (a ∘ e.symm) ∘ e = a := by ext i; simp
      rw [heq]
  have hfg : Function.RightInverse g f := by
    intro c
    induction c using Quotient.inductionOn with | h φ =>
      apply Quotient.sound
      apply Theory.models_formula_iff.mpr
      intro N a
      apply Formula.realize_iff.mpr
      simp only [Formula.realize_relabel]
      have heq : (a ∘ e) ∘ e.symm = a := by ext i; simp
      rw [heq]
  exact ⟨⟨f, g, hgf, hfg⟩, fun _ => rfl⟩

/-- Finite numbered contexts suffice for every finite free-name context. -/
theorem finite_classes_context (hF : ∀ n, Finite (FormulaClass T (Fin n))) [Finite α] :
    Finite (FormulaClass T α) := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨E, _⟩ := context_equiv (T := T) (Fintype.equivFin α)
  let := hF (Fintype.card α)
  exact Finite.of_injective E E.injective

end Lemmatheca.ModelTheory.CountableCategoricity
