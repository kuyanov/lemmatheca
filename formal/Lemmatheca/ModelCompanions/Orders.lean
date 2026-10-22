import Lemmatheca.ModelCompanions.ModelCompanions
import Mathlib.Data.Prod.Lex

/-! Dense linear orders complete the actual strict-linear-order theory. -/
namespace Lemmatheca.ModelTheory.ModelCompanions

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.QuantifierElimination
open Lemmatheca.ModelTheory.QuantifierElimination.Shared

universe w

/-- The three order axioms are exactly the corresponding axioms of strictDloTheory. -/
def strictLinearOrderTheory : binaryRelLanguage.Theory :=
  {strictIrreflexive, strictTransitive, strictTotal}

/-- The axiom set describes strict linear orders for the actual interpreted binary relation. -/
theorem model_strictLinearOrderTheory_iff {M : Type*} [binaryRelLanguage.Structure M] :
    M ⊨ strictLinearOrderTheory ↔ IsStrictTotalOrder M (relation (o := true) (M := M)) := by
  have hirr : (M ⊨ strictIrreflexive) ↔ ∀ a : M, ¬ relation (o := true) a a := by
    simp [strictIrreflexive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_not, ltAtom_realize, Fin.snoc]
  have htrans : (M ⊨ strictTransitive) ↔ ∀ a b c : M,
      relation (o := true) a b → relation (o := true) b c → relation (o := true) a c := by
    simp [strictTransitive, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_imp, BoundedFormula.realize_inf,
      ltAtom_realize, Fin.snoc]
  have htotal : (M ⊨ strictTotal) ↔ ∀ a b : M,
      relation (o := true) a b ∨ a = b ∨ relation (o := true) b a := by
    simp [strictTotal, Sentence.Realize, FirstOrder.Language.Formula.Realize,
      BoundedFormula.realize_all, BoundedFormula.realize_sup, ltAtom_realize,
      eqAtom, BoundedFormula.Realize, Term.realize, or_assoc, Fin.snoc]
  simp only [strictLinearOrderTheory, Theory.model_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, hirr, htrans, htotal]
  constructor
  · rintro ⟨hi, ht, htot⟩
    exact
      { irrefl := hi
        trans := ht
        trichotomous := fun a b hab hba => ((htot a b).resolve_left hab).resolve_right hba }
  · intro h
    let := h
    exact ⟨irrefl_of _, fun _ _ _ => trans_of _, trichotomous_of _⟩

theorem strictLinearOrder_subset_dlo : strictLinearOrderTheory ⊆ strictDloTheory := by
  intro σ hσ
  rcases hσ with rfl | rfl | rfl <;> simp [strictDloTheory]

@[instance_reducible] private noncomputable def orderOfStrictAxioms {M : Type*} [binaryRelLanguage.Structure M]
    (hM : M ⊨ strictLinearOrderTheory) : LinearOrder M := by
  classical
  let := (model_strictLinearOrderTheory_iff).mp hM
  exact linearOrderOfSTO (relation (o := true) (M := M))

/-- Replace each point by a copy of the rational order, with lexicographic comparison. -/
noncomputable def lexExtension
    (M : Theory.ModelType.{0, 0, w} strictLinearOrderTheory) :
    Theory.ModelType.{0, 0, w} strictDloTheory := by
  let := orderOfStrictAxioms M.is_model
  let := binaryRelStructure (M ×ₗ ℚ) (fun a b => a < b)
  let : (M ×ₗ ℚ) ⊨ strictDloTheory := model_strictDloTheory
  exact Theory.ModelType.of strictDloTheory (M ×ₗ ℚ)

/-- The exact lexicographic map specified in the human construction. -/
def lexMap (M : Theory.ModelType.{0, 0, w} strictLinearOrderTheory) :
    M → lexExtension M := fun a => toLex (a, 0)

/-- The relation on the extension is the displayed disjunction, for the original relation. -/
theorem lexExtension_relation (M : Theory.ModelType.{0, 0, w} strictLinearOrderTheory)
    (a b : M) (q r : ℚ) :
    relation (o := true) (M := lexExtension M) (toLex (a, q)) (toLex (b, r)) ↔
      relation (o := true) (M := M) a b ∨ (a = b ∧ q < r) := by
  let := orderOfStrictAxioms M.is_model
  change (toLex (a, q) : M ×ₗ ℚ) < toLex (b, r) ↔ a < b ∨ (a = b ∧ q < r)
  exact Prod.Lex.toLex_lt_toLex

/-- The given map itself is an embedding, not merely some map between the two models. -/
theorem lexMap_embedding (M : Theory.ModelType.{0, 0, w} strictLinearOrderTheory) :
    ∃ e : M ↪[binaryRelLanguage] lexExtension M,
      (e : M → lexExtension M) = lexMap M := by
  refine ⟨{ toFun := lexMap M, inj' := ?_, map_fun' := ?_, map_rel' := ?_ }, rfl⟩
  · intro a b h
    exact congrArg (fun x : lexExtension M => (ofLex x).1) h
  · intro n f
    exact f.elim
  · intro n R x
    cases R
    have hx : x = ![x 0, x 1] := by
      funext i
      fin_cases i <;> rfl
    have hy : lexMap M ∘ x = ![lexMap M (x 0), lexMap M (x 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [hy, hx]
    change relation (o := true) (M := lexExtension M) (toLex (x 0, 0)) (toLex (x 1, 0)) ↔
      relation (o := true) (M := M) (x 0) (x 1)
    rw [lexExtension_relation]
    simp

/-- Dense linear orders give a model completion of strict linear orders. -/
theorem strictDlo_modelCompletion :
    ModelCompletion.{0, 0, w} strictLinearOrderTheory strictDloTheory := by
  apply qe_completion_criterion strictLinearOrder_subset_dlo ?_ strictDlo_hasQuantifierElimination
  intro M
  obtain ⟨e, _he⟩ := lexMap_embedding M
  exact ⟨lexExtension M, ⟨e⟩⟩

end Lemmatheca.ModelTheory.ModelCompanions
