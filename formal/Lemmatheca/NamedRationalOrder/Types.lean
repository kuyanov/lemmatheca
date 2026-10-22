import Lemmatheca.NamedRationalOrder.Structures
import Lemmatheca.NamedRationalOrder.TypeBounds

/-! Actual complete types of the named rational order and their cardinalities. -/
namespace Lemmatheca.ModelTheory.NamedRationalOrder

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Types IsolatedTypes

noncomputable def realType (r : ℝ) : theory.CompleteType (Fin 1) :=
  theory.typeOf (M := realModel) (fun _ : Fin 1 => r)

def belowName (q : ℚ) : rationalLanguage.Formula (Fin 1) :=
  Relations.formula (Sum.inl BinaryRelationSymbol.rel)
    ![Term.var 0, Constants.term (binaryRelLanguage.con q)]

theorem belowName_realize (q : ℚ) (r : ℝ) :
    (belowName q).Realize (M := realModel) (fun _ : Fin 1 => r) ↔ r < (q : ℝ) := by
  rfl

theorem realType_injective : Function.Injective realType := by
  have hle (r s : ℝ) (h : realType r = realType s) : s ≤ r := by
    by_contra hn
    obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have hr : belowName q ∈ formulas (realType r) :=
      Theory.CompleteType.formula_mem_typeOf.mpr ((belowName_realize q r).mpr hrq)
    have hs : s < (q : ℝ) := (belowName_realize q s).mp
      (Theory.CompleteType.formula_mem_typeOf.mp (h ▸ hr))
    exact lt_asymm hqs hs
  intro r s h
  exact le_antisymm (hle s r h.symm) (hle r s h)

theorem types_cardinality :
    Cardinal.mk (theory.CompleteType (Fin 1)) = 2 ^ Cardinal.aleph0 := by
  apply (complete_types_cardinal_le_continuum theory 1).antisymm
  rw [Cardinal.two_power_aleph0, ← Cardinal.mk_real]
  exact Cardinal.mk_le_of_injective realType_injective

theorem isolated_types_cardinality :
    Cardinal.mk {p : theory.CompleteType (Fin 1) // Isolated theory p} = Cardinal.aleph0 := by
  let f : ℚ → {p : theory.CompleteType (Fin 1) // Isolated theory p} :=
    fun q => ⟨pointType q, (isolated_iff_named _).mpr ⟨q, rfl⟩⟩
  have hi : Function.Injective f := by
    intro p q h
    exact pointType_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨q, hq⟩ := (isolated_iff_named p.val).mp p.property
    exact ⟨q, Subtype.ext hq.symm⟩
  calc
    Cardinal.mk {p : theory.CompleteType (Fin 1) // Isolated theory p} = Cardinal.mk ℚ :=
      (Cardinal.mk_congr (Equiv.ofBijective f ⟨hi, hs⟩)).symm
    _ = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 ℚ

theorem theory_not_small : ¬ CountableSaturatedModels.Small theory := by
  intro h
  let := h 1
  have hc : Cardinal.mk (theory.CompleteType (Fin 1)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0
  rw [types_cardinality, Cardinal.two_power_aleph0] at hc
  exact not_le_of_gt Cardinal.aleph0_lt_continuum hc

theorem no_countable_saturated : ¬ ∃ M : theory.ModelType.{0, 0, 0},
    Countable M ∧ Saturation.OmegaSaturated rationalLanguage M := by
  rintro ⟨M, hc, hs⟩
  let := hc
  exact theory_not_small (CountableSaturatedModels.small_of_saturated theory_complete hs)

theorem no_countable_universal : ¬ ∃ M : theory.ModelType.{0, 0, 0},
    CountableSaturatedModels.CountableUniversal theory M := by
  rintro ⟨M, hM⟩
  exact theory_not_small (CountableSaturatedModels.small_of_universal hM)

theorem realType_isolated_iff (r : ℝ) :
    Isolated theory (realType r) ↔ ∃ q : ℚ, (q : ℝ) = r := by
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := (isolated_iff_named _).mp hp
    let φ : rationalLanguage.Formula (Fin 1) :=
      (Term.var 0).equal (Constants.term (binaryRelLanguage.con q))
    have hf : φ ∈ formulas (pointType q) :=
      Theory.CompleteType.formula_mem_typeOf.mpr (by change q = q; rfl)
    have hr := Theory.CompleteType.formula_mem_typeOf.mp (hq.symm ▸ hf)
    change r = (q : ℝ) at hr
    exact ⟨q, hr.symm⟩
  · rintro ⟨q, rfl⟩
    have he : realType (q : ℝ) = pointType q := by
      have hr : Realizes (formulas (pointType q))
          (fun _ : Fin 1 => (show realModel from (q : ℝ))) := by
        intro φ hφ
        exact (realInclusion.map_formula φ (fun _ : Fin 1 => (q : rationalModel))).mpr
          (Theory.CompleteType.formula_mem_typeOf.mp hφ)
      exact ((realizes_complete_iff (pointType q)
        (fun _ : Fin 1 => (show realModel from (q : ℝ)))).mp hr).symm
    exact (isolated_iff_named _).mpr ⟨q, he⟩

end Lemmatheca.ModelTheory.NamedRationalOrder
