import Lemmatheca.StronglyMinimalTypes.Bounds
import Lemmatheca.StronglyMinimalSets.Examples
import Lemmatheca.OrderPatternsAndStability.Equality

/-! Equality and a single language constant distinguish genericity from newness and from names. -/
namespace Lemmatheca.Entry.StronglyMinimalTypes
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open StronglyMinimalSets StronglyMinimalTypes Closures OrderPatternsAndStability
universe w
noncomputable section

section Equality
variable {M : Type w} [Language.empty.Structure M] [Infinite M]

/-- The generic constructed from cofinite formulas is the earlier equality fresh-point type. -/
theorem equality_generic_eq_fresh (A : Set M) (hM : Minimal Language.empty M) :
    genericType A hM = Equality.freshType A := by
  obtain ⟨choice, he⟩ := (Equality.typeFromChoice_bijective.{w,w} A).2 (genericType A hM)
  cases choice with
  | inl a =>
    change (Language.empty[[A]].completeTheory M).typeOf (fun _ => a.val) = genericType A hM at he
    exfalso
    apply generic_nonalgebraic A hM
    rw [← he, algebraic_typeOf_iff]
    exact dcl_subset_acl A (subset_dcl A a.property)
  | inr _ =>
    exact he.symm

/-- With no parameters, every old point realizes the pure equality generic type. -/
theorem equality_empty_generic (hM : Minimal Language.empty M) (b : M) :
    (Language.empty[[(∅ : Set M)]].completeTheory M).typeOf (fun _ => b) =
      genericType (∅ : Set M) hM := by
  apply (generic_old_realization (∅ : Set M) hM b).mpr
  rw [(Lemmatheca.Entry.DefinableAndAlgebraicClosure.infinite_equality_closures (∅ : Set M)).2]
  exact Set.notMem_empty b

end Equality

section NamedPoint
open Lemmatheca.Entry.StronglyMinimalSets
variable {M : Type w} [pointLanguage.Structure M] [infiniteM : Infinite M]

/-- The original language already contains c, even though the added parameter set is empty. -/
def namedPointEquation : pointLanguage[[(∅ : Set M)]].Formula (Fin 1) :=
  (pointLanguage.lhomWithConstants (∅ : Set M)).onFormula
    ((Term.var (0 : Fin 1)).equal (Constants.term (Language.empty.con ())))

/-- The displayed named-point equation has exactly the indicated singleton of solutions. -/
theorem namedPointEquation_solutions :
    solutions (∅ : Set M) (namedPointEquation (M := M)) = {pointValue M} := by
  rcases infiniteM with ⟨_infiniteCarrier⟩
  ext b
  change ((pointLanguage.lhomWithConstants (∅ : Set M)).onFormula
    ((Term.var (0 : Fin 1)).equal (Constants.term (Language.empty.con ())))).Realize
      (fun _ => b) ↔ b = pointValue M
  rw [LHom.realize_onFormula]
  simp only [Formula.realize_equal, Term.realize_var, Term.realize_constants, pointValue]

/-- The language constant supplies an algebraic complete type over the empty parameter set. -/
theorem named_point_algebraic :
    Algebraic (∅ : Set M)
      ((pointLanguage[[(∅ : Set M)]].completeTheory M).typeOf (fun _ => pointValue M)) := by
  refine ⟨namedPointEquation (M := M), Theory.CompleteType.formula_mem_typeOf.mpr ?_, ?_⟩
  · change pointValue M ∈ solutions (∅ : Set M) (namedPointEquation (M := M))
    rw [namedPointEquation_solutions]
    exact Set.mem_singleton _
  · rw [namedPointEquation_solutions]
    exact Set.finite_singleton _

/-- The generic excludes c, while the point type includes it, so the two completions differ. -/
theorem named_point_generic_excludes (hM : Minimal pointLanguage M) :
    (namedPointEquation (M := M)).not ∈ Types.formulas (genericType (∅ : Set M) hM) ∧
      ((pointLanguage[[(∅ : Set M)]].completeTheory M).typeOf (fun _ => pointValue M)) ≠
        genericType (∅ : Set M) hM := by
  refine ⟨?_, ?_⟩
  · rw [genericType_formulas]
    change (solutions (∅ : Set M) (namedPointEquation (M := M)).not)ᶜ.Finite
    have he : (solutions (∅ : Set M) (namedPointEquation (M := M)).not)ᶜ =
        solutions (∅ : Set M) (namedPointEquation (M := M)) := by
      ext b
      change (¬ (namedPointEquation (M := M)).not.Realize (fun _ => b)) ↔
        (namedPointEquation (M := M)).Realize (fun _ => b)
      simp only [Formula.realize_not, not_not]
    rw [he, namedPointEquation_solutions]
    exact Set.finite_singleton _
  · intro he
    exact generic_nonalgebraic (∅ : Set M) hM (he ▸ named_point_algebraic (M := M))

/-- The empty list of added-name exclusions does not decide x=c. -/
theorem named_empty_conditions_not_complete :
    ¬ Types.IsCompletePartial (pointLanguage[[(∅ : Set M)]].completeTheory M)
      (∅ : Set (pointLanguage[[(∅ : Set M)]].Formula (Fin 1))) := by
  rcases infiniteM with ⟨_infiniteCarrier⟩
  intro h
  have hd := (Types.complete_iff_decides _ _).mp h
  have hx := hd.2 (namedPointEquation (M := M))
  simp at hx

/-- In this example the single original-language inequality already determines the generic type. -/
theorem named_generic_determined (hM : Minimal pointLanguage M)
    (q : TypesOver (L := pointLanguage) (∅ : Set M) 1)
    (hq : (namedPointEquation (M := M)).not ∈ Types.formulas q) :
    q = genericType (∅ : Set M) hM := by
  apply unique_nonalgebraic (∅ : Set M) hM q
  intro ha
  obtain ⟨b, hb, he⟩ := algebraic_realized (∅ : Set M) q ha
  rw [point_closure] at hb
  have hbc : b = pointValue M := by simpa using hb
  subst b
  have hmem : (namedPointEquation (M := M)).not ∈ Types.formulas
      ((pointLanguage[[(∅ : Set M)]].completeTheory M).typeOf (fun _ => pointValue M)) :=
    he ▸ hq
  have hn := Formula.realize_not.mp (Theory.CompleteType.formula_mem_typeOf.mp hmem)
  apply hn
  change pointValue M ∈ solutions (∅ : Set M) (namedPointEquation (M := M))
  rw [namedPointEquation_solutions]
  exact Set.mem_singleton _

end NamedPoint
end
end Lemmatheca.Entry.StronglyMinimalTypes
