import Lemmatheca.OrderPatternsAndStability.Equality
import Lemmatheca.OrderPatternsAndStability.CountableModels
import Lemmatheca.NamedRationalOrder.TypeBounds

/-! Rational order patterns and their actual real-point realizations over all rational parameters. -/
namespace Lemmatheca.Entry.OrderPatternsAndStability
open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.ModelTheory
open Lemmatheca.ModelTheory.OrderPatternsAndStability
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

instance rationalOrderStructure : binaryRelLanguage.Structure ℚ :=
  binaryRelStructure ℚ (· < ·)
instance realOrderStructure : binaryRelLanguage.Structure ℝ :=
  binaryRelStructure ℝ (· < ·)

def orderFormula : binaryRelLanguage.Formula (Fin (1+1)) :=
  Relations.formula₂ (L := binaryRelLanguage) BinaryRelationSymbol.rel (.var 0) (.var 1)

def rationalTuple (q : ℚ) : Fin 1 → ℚ := fun _ => q

theorem rational_order_pattern : OrderPattern orderFormula rationalTuple rationalTuple := by
  intro i j
  rfl

theorem dense_order_property :
    HasOrderProperty QuantifierElimination.Shared.strictDloTheory orderFormula := by
  let : ℚ ⊨ QuantifierElimination.Shared.strictDloTheory :=
    QuantifierElimination.Shared.model_strictDloTheory
  intro k hk
  apply hasFinitePattern_of_model _ orderFormula k
    (fun i _ => (i.val : ℚ)) (fun i _ => (i.val : ℚ))
  intro i j
  change (i.val : ℚ) < (j.val : ℚ) ↔ i < j
  exact_mod_cast (Iff.rfl : i.val < j.val ↔ i.val < j.val)

private def rationalRealEmbedding : ℚ ↪ₑ[binaryRelLanguage] ℝ := by
  let : ℚ ⊨ QuantifierElimination.Shared.strictDloTheory :=
    QuantifierElimination.Shared.model_strictDloTheory
  let : ℝ ⊨ QuantifierElimination.Shared.strictDloTheory :=
    QuantifierElimination.Shared.model_strictDloTheory
  exact QuantifierElimination.Shared.strictDlo_elementaryEmbedding
    { toFun := fun q => (q : ℝ)
      inj' := Rat.cast_injective
      map_fun' := by intro n f; exact Empty.elim f
      map_rel' := by
        intro n r a
        cases r
        change ((a 0 : ℝ) < (a 1 : ℝ)) ↔ a 0 < a 1
        exact Rat.cast_lt }

theorem rational_real_inclusion :
    ∃ f : ℚ ↪ₑ[binaryRelLanguage] ℝ, ∀ q : ℚ, f q = (q : ℝ) := by
  exact ⟨rationalRealEmbedding,fun _ => rfl⟩

abbrev rationalParameters : Set ℚ := parameterSet rationalTuple

theorem rationalParameters_univ : rationalParameters = Set.univ := by
  ext q
  constructor
  · intro _; trivial
  · intro _; exact ⟨(q,0),rfl⟩

/-- The very same rational parameter label has its actual rational value in the real order. -/
@[instance_reducible]
def realParameterStructure : binaryRelLanguage[[rationalParameters]].Structure ℝ :=
  Diagrams.namedExpansion (L := binaryRelLanguage) (fun a : rationalParameters => (a.val : ℝ))

theorem realParameter_model :
    letI := realParameterStructure
    ℝ ⊨ (binaryRelLanguage[[rationalParameters]].completeTheory ℚ) := by
  exact (rationalRealEmbedding.liftWithConstants rationalParameters).theory_model_iff
    (binaryRelLanguage[[rationalParameters]].completeTheory ℚ) |>.mp inferInstance

noncomputable def realCutType (r : ℝ) :
    TypesOver (L := binaryRelLanguage) (M := ℚ) rationalParameters 1 :=
  letI := realParameterStructure
  letI : ℝ ⊨ (binaryRelLanguage[[rationalParameters]].completeTheory ℚ) := realParameter_model
  (binaryRelLanguage[[rationalParameters]].completeTheory ℚ).typeOf (M := ℝ) (fun _ => r)

theorem real_satisfies_cut (r : ℝ) :
    letI := realParameterStructure
    Types.Realizes (cutConditions orderFormula rationalTuple r) (fun _ : Fin 1 => r) := by
  let := realParameterStructure
  classical
  intro φ hφ
  obtain ⟨q,hq⟩ := hφ
  dsimp only at hq
  by_cases hqr : (q : ℝ) ≤ r
  · rw [ite_eq_left hqr] at hq
    rw [← hq]
    change ¬r < (q : ℝ)
    exact not_lt_of_ge hqr
  · rw [ite_eq_right hqr] at hq
    rw [← hq]
    change r < (q : ℝ)
    exact lt_of_not_ge hqr

theorem realCutType_contains (r : ℝ) :
    cutConditions orderFormula rationalTuple r ⊆ Types.formulas (realCutType r) := by
  let := realParameterStructure
  let : ℝ ⊨ (binaryRelLanguage[[rationalParameters]].completeTheory ℚ) := realParameter_model
  intro φ hφ
  exact Theory.CompleteType.formula_mem_typeOf.mpr (real_satisfies_cut r φ hφ)

theorem realCutType_injective : Function.Injective realCutType := by
  let := realParameterStructure
  let : ℝ ⊨ (binaryRelLanguage[[rationalParameters]].completeTheory ℚ) := realParameter_model
  have hle (r s : ℝ) (h : realCutType r = realCutType s) : s ≤ r := by
    by_contra hn
    obtain ⟨q,hrq,hqs⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have hr : rationalTest orderFormula rationalTuple q ∈ Types.formulas (realCutType r) :=
      Theory.CompleteType.formula_mem_typeOf.mpr (show r < (q : ℝ) from hrq)
    have hmem : rationalTest orderFormula rationalTuple q ∈ Types.formulas (realCutType s) := h ▸ hr
    have hs : s < (q : ℝ) := Theory.CompleteType.formula_mem_typeOf.mp hmem
    exact lt_asymm hqs hs
  intro r s h
  exact le_antisymm (hle s r h.symm) (hle r s h)

theorem rational_type_cardinality :
    #(TypesOver (L := binaryRelLanguage) (M := ℚ) rationalParameters 1) =
      2 ^ Cardinal.aleph0 := by
  have : Subsingleton binaryRelLanguage.Symbols := by
    constructor
    rintro (⟨n,f⟩ | ⟨n,r⟩) (⟨m,g⟩ | ⟨m,t⟩)
    · exact Empty.elim f
    · exact Empty.elim f
    · exact Empty.elim g
    · cases r; cases t; rfl
  let : Countable binaryRelLanguage.Symbols := inferInstance
  apply le_antisymm
  · exact NamedRationalOrder.complete_types_cardinal_le_continuum _ 1
  · rw [Cardinal.two_power_aleph0, ← Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective realCutType_injective

theorem rational_realCutType (q : ℚ) :
    realCutType (q : ℝ) =
      (binaryRelLanguage[[rationalParameters]].completeTheory ℚ).typeOf
        (fun _ : Fin 1 => q) := by
  let := realParameterStructure
  let : ℝ ⊨ (binaryRelLanguage[[rationalParameters]].completeTheory ℚ) := realParameter_model
  apply ((Types.realizes_complete_iff _ (fun _ : Fin 1 => (q : ℝ))).mp ?_).symm
  intro φ hφ
  exact (rationalRealEmbedding.liftWithConstants rationalParameters).map_formula φ
    (fun _ : Fin 1 => q) |>.mpr (Theory.CompleteType.formula_mem_typeOf.mp hφ)

theorem irrational_type_omitted (r : ℝ) (hr : ∀ q : ℚ, (q : ℝ) ≠ r) :
    ∀ a : Fin 1 → ℚ, ¬Types.Realizes (Types.formulas (realCutType r)) a := by
  intro a ha
  have h : realCutType r =
      (binaryRelLanguage[[rationalParameters]].completeTheory ℚ).typeOf a :=
    (Types.realizes_complete_iff _ a).mp ha
  have he : a = fun _ : Fin 1 => a 0 := by funext i; fin_cases i; rfl
  rw [he, ← rational_realCutType (a 0)] at h
  exact hr (a 0) (realCutType_injective h).symm

end Lemmatheca.Entry.OrderPatternsAndStability
