import Lemmatheca.ExistentiallyClosedExtensions.Companions
import Lemmatheca.ModelCompanions.Orders
import Mathlib.Order.WithBot

/-! Actual strict orders show why a single original-parameter pass is insufficient. -/
namespace Lemmatheca.Entry.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory
open ModelCompleteness ModelCompanions InductiveTheories
open Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open QuantifierElimination QuantifierElimination.Shared
universe w

theorem strictLinearOrder_inductive : IsInductive.{0, 0, w} strictLinearOrderTheory := by
  have h : IsUniversalExistentialTheory strictLinearOrderTheory := by
    intro σ hσ
    rcases hσ with rfl | rfl | rfl
    · exact universal_isUniversalExistential (.all (.of_isQF (BoundedFormula.IsAtomic.rel _ _).isQF.not))
    · exact universal_isUniversalExistential (.all (.all (.all (.of_isQF
        (((BoundedFormula.IsAtomic.rel _ _).isQF.inf (BoundedFormula.IsAtomic.rel _ _).isQF).imp
          (BoundedFormula.IsAtomic.rel _ _).isQF)))))
    · exact universal_isUniversalExistential (.all (.all (.of_isQF
        (((BoundedFormula.IsAtomic.rel _ _).isQF.sup (BoundedFormula.IsAtomic.equal _ _).isQF).sup
          (BoundedFormula.IsAtomic.rel _ _).isQF))))
  exact directed_implies_inductive _ (axiomatization_implies_directed _ ⟨_,h,rfl⟩)

/-- The full model class agrees, including the original strict-order model condition. -/
theorem strictLinearOrder_isEC_iff
    (M : Theory.ModelType.{0, 0, w} (∅ : binaryRelLanguage.Theory)) :
    IsEC.{0, 0, w} strictLinearOrderTheory M ↔ M ⊨ strictDloTheory := by
  exact ((modelCompanion_iff_axiomatizesEC strictLinearOrderTheory strictDloTheory
    strictLinearOrder_inductive).mp (modelCompletion_modelCompanion strictDlo_modelCompletion) M).symm

@[instance_reducible]
noncomputable def rationalModel : Theory.ModelType.{0, 0, 0} strictLinearOrderTheory := by
  let := binaryRelStructure ℚ (fun a b => a < b)
  let : ℚ ⊨ strictLinearOrderTheory := model_strictLinearOrderTheory_iff.mpr (by
    change IsStrictTotalOrder _ (fun a b => a < b)
    infer_instance)
  exact Theory.ModelType.of strictLinearOrderTheory ℚ

@[instance_reducible]
noncomputable def lastModel : Theory.ModelType.{0, 0, 0} strictLinearOrderTheory := by
  let := binaryRelStructure (WithTop ℚ) (fun a b => a < b)
  let : WithTop ℚ ⊨ strictLinearOrderTheory := model_strictLinearOrderTheory_iff.mpr (by
    change IsStrictTotalOrder _ (fun a b => a < b)
    infer_instance)
  exact Theory.ModelType.of strictLinearOrderTheory (WithTop ℚ)

@[instance_reducible]
noncomputable def twoLastModel : Theory.ModelType.{0, 0, 0} strictLinearOrderTheory := by
  let := binaryRelStructure (WithTop (WithTop ℚ)) (fun a b => a < b)
  let : WithTop (WithTop ℚ) ⊨ strictLinearOrderTheory :=
    model_strictLinearOrderTheory_iff.mpr (by
    change IsStrictTotalOrder _ (fun a b => a < b)
    infer_instance)
  exact Theory.ModelType.of strictLinearOrderTheory (WithTop (WithTop ℚ))

/-- The exact inclusion of the original rational points. -/
noncomputable def intoLast : rationalModel ↪[binaryRelLanguage] lastModel where
  toFun := fun q => ((show ℚ from q) : WithTop ℚ)
  inj' := WithTop.coe_injective
  map_fun' := by
    intro n f
    exact f.elim
  map_rel' := by
    intro n R x
    cases R
    exact WithTop.coe_lt_coe

/-- The next extension keeps the old greatest point and appends a fresh greatest point. -/
noncomputable def intoTwoLast : lastModel ↪[binaryRelLanguage] twoLastModel where
  toFun := fun q => ((show WithTop ℚ from q) : WithTop (WithTop ℚ))
  inj' := WithTop.coe_injective
  map_fun' := by
    intro n f
    exact f.elim
  map_rel' := by
    intro n R x
    cases R
    exact WithTop.coe_lt_coe

/-- The original rational structure already realizes every possible order witness. -/
theorem rationals_isEC :
    ExistentiallyClosedModel.{0, 0, 0} strictLinearOrderTheory rationalModel := by
  apply (isEC_iff_existing strictLinearOrderTheory rationalModel).mp
  apply (strictLinearOrder_isEC_iff (Theory.ModelType.of ∅ rationalModel)).mpr
  exact model_strictDloTheory (M := ℚ)

/-- This claim concerns only original rational parameters. -/
theorem rational_to_last_completed : IsCompletedPass strictLinearOrderTheory intoLast := by
  rintro r ⟨P,g,hP⟩
  have hr := rationals_isEC P (g.comp intoLast) r.arity r.formula r.existential r.parameters hP
  have hp := r.existential.realize_embedding intoLast hr
  have he : intoLast ∘ (default : Fin 0 → rationalModel) = (default : Fin 0 → lastModel) :=
    Subsingleton.elim _ _
  simpa only [Request.Realized,FirstOrder.Language.Formula.Realize,he] using hp

/-- The new greatest point introduces a request that this completed pass did not handle. -/
def aboveParameter : binaryRelLanguage.Formula (Fin 1) :=
  (Relations.boundedFormula₂ BinaryRelationSymbol.rel
    (.var (.inl 0)) (.var (.inr 0))).ex

theorem aboveParameter_existential : aboveParameter.IsExistential := by
  exact .ex (.of_isQF (BoundedFormula.IsAtomic.rel _ _).isQF)

theorem last_has_no_larger : ¬ aboveParameter.Realize (M := lastModel) (fun _ => (⊤ : WithTop ℚ)) := by
  intro h
  obtain ⟨x,hx⟩ := FirstOrder.Language.BoundedFormula.realize_ex.mp h
  change (⊤ : WithTop ℚ) < x at hx
  exact not_top_lt hx

theorem old_last_has_larger :
    aboveParameter.Realize (M := twoLastModel) (fun _ => intoTwoLast (⊤ : WithTop ℚ)) := by
  simp only [aboveParameter, FirstOrder.Language.Formula.Realize, BoundedFormula.realize_ex]
  refine ⟨(⊤ : WithTop (WithTop ℚ)), ?_⟩
  change (↑(⊤ : WithTop ℚ) : WithTop (WithTop ℚ)) < ⊤
  exact WithTop.coe_lt_top _

/-- The actual extension and supplied map witness the failed existential reflection. -/
theorem last_not_isEC :
    ¬ ExistentiallyClosedModel.{0, 0, 0} strictLinearOrderTheory lastModel := by
  intro h
  exact last_has_no_larger (h twoLastModel intoTwoLast 1 aboveParameter
    aboveParameter_existential (fun _ => (⊤ : WithTop ℚ)) old_last_has_larger)

end Lemmatheca.Entry.ExistentiallyClosedExtensions
