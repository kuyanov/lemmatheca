import Lemmatheca.OmittingTypes.OmittingTypes
import Lemmatheca.MonadicLogic.Syntax
import Lemmatheca.TypesAndRealization.Examples

/-! Exact counterexamples separating principal partial conditions and complete extensions. -/
namespace Lemmatheca.Entry.OmittingPartialTypes

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.OmittingTypes
open Lemmatheca.ModelTheory.ArithmeticTheories
open Lemmatheca.MathematicalLogic

abbrev UnaryLanguage := MonadicLogic.lang 1

def unaryCondition : UnaryLanguage.Formula (Fin 1) :=
  .rel (MonadicLogic.predicate 1 0) (fun _ => .var (.inl 0))

def unaryPartialType : Set (UnaryLanguage.Formula (Fin 1)) := {unaryCondition}

instance emptyPredicateStructure : UnaryLanguage.Structure Unit :=
  MonadicLogic.structureOfPredicates fun _ _ => False

theorem principal_but_omitted :
    IsPartial (∅ : UnaryLanguage.Theory) unaryPartialType ∧
      Principal (∅ : UnaryLanguage.Theory) unaryPartialType ∧
      Omits Unit unaryPartialType ∧ ¬ (∅ : UnaryLanguage.Theory).IsComplete := by
  let : UnaryLanguage.Structure Bool := MonadicLogic.structureOfPredicates fun _ _ => True
  have hreal : Realizes unaryPartialType (fun _ : Fin 1 => true) := by
    intro φ hφ
    obtain rfl := Set.mem_singleton_iff.mp hφ
    change True
    trivial
  have hpartial : IsPartial (∅ : UnaryLanguage.Theory) unaryPartialType := by
    exact (partial_iff_model _ _).mpr
      ⟨Theory.ModelType.of (∅ : UnaryLanguage.Theory) Bool, fun _ => true, hreal⟩
  refine ⟨hpartial, ⟨unaryCondition, hpartial, ?_⟩, ?_, ?_⟩
  · intro φ hφ
    obtain rfl := Set.mem_singleton_iff.mp hφ
    exact Theory.models_formula_iff.mpr (fun _ _ => id)
  · rintro ⟨a, ha⟩
    have h := ha unaryCondition (Set.mem_singleton _)
    change False at h
    exact h
  · intro hc
    let σ := Lemmatheca.ModelTheory.IsolatedTypes.existentialSentence unaryCondition
    have ht : Bool ⊨ σ :=
      (Lemmatheca.ModelTheory.IsolatedTypes.existentialSentence_realize unaryCondition).mpr
        ⟨fun _ => true, hreal _ (Set.mem_singleton _)⟩
    have hf : ¬ Unit ⊨ σ := by
      intro h
      obtain ⟨a, ha⟩ := (Lemmatheca.ModelTheory.IsolatedTypes.existentialSentence_realize unaryCondition).mp h
      exact ha
    rcases hc.2 σ with h | h
    · exact hf (h.realize_sentence Unit)
    · exact (Sentence.realize_not Bool).mp (h.realize_sentence Bool) ht

def tautologicalConditions : Set (language.Formula (Fin 1)) :=
  {(Term.var (0 : Fin 1)).equal (.var 0)}

theorem tautological_realizes {M : Type*} [language.Structure M] (a : Fin 1 → M) :
    Realizes tautologicalConditions a := by
  intro φ hφ
  obtain rfl := Set.mem_singleton_iff.mp hφ
  exact Formula.realize_equal.mpr rfl

theorem omitted_completion_realized_partial :
    ∃ q : trueArithmetic.CompleteType (Fin 1),
      Lemmatheca.Entry.TypesAndRealization.nonstandardConditions ⊆ formulas q ∧
      tautologicalConditions ⊆ formulas q ∧ Omits ℕ (formulas q) ∧
      ¬ Omits ℕ tautologicalConditions := by
  obtain ⟨q, hq⟩ := exists_complete_extension
    Lemmatheca.Entry.TypesAndRealization.nonstandardConditions
    Lemmatheca.Entry.TypesAndRealization.nonstandard_partial
  have htaut : tautologicalConditions ⊆ formulas q := by
    obtain ⟨N, a, ha⟩ := trueArithmetic.exists_modelType_is_realized_in q
    intro φ hφ
    rw [← ha]
    exact Theory.CompleteType.formula_mem_typeOf.mpr (tautological_realizes a φ hφ)
  refine ⟨q, hq, htaut, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    exact Lemmatheca.Entry.TypesAndRealization.nonstandard_omitted
      ⟨a, fun φ hφ => ha φ (hq hφ)⟩
  · intro h
    exact h ⟨fun _ => 0, tautological_realizes (fun _ => 0)⟩

end Lemmatheca.Entry.OmittingPartialTypes
