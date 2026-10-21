import Lemmatheca.BackAndForth.BackAndForth
import Lemmatheca.FirstOrderStructures.BasicStructures
import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.Order.Interval.Set.Infinite

open Lemmatheca.MathematicalLogic

/-! The actual strict-order theory and the finite-map back-and-forth construction. -/
namespace Lemmatheca.ModelTheory.BackAndForth

open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.QuantifierElimination

universe u v

/-- The relation extracted from the shared language determines its whole structure. -/
private theorem canonical_structure_eq {M : Type u} (S : binaryRelLanguage.Structure M) :
    binaryRelStructure M (@Shared.relation true M S) = S := by
  apply Structure.ext
  · funext n f
    exact Empty.elim f
  · funext n r
    cases r
    funext a
    change @Structure.RelMap binaryRelLanguage M S 2 .rel ![a 0, a 1] =
      @Structure.RelMap binaryRelLanguage M S 2 .rel a
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Every nonempty model of the actual strict dense-order sentences is infinite. -/
theorem strictDlo_models_infinite (M : Type u) [binaryRelLanguage.Structure M]
    [Nonempty M] [M ⊨ Shared.strictDloTheory] : Infinite M := by
  classical
  have h := Shared.model_strictDloTheory_iff.mp (inferInstance : M ⊨ Shared.strictDloTheory)
  let r := Shared.relation (o := true) (M := M)
  let : IsStrictTotalOrder M r :=
    { irrefl := h.irrefl, trans := h.trans,
      trichotomous := fun a b hab hba => ((h.total a b).resolve_left hab).resolve_right hba }
  let : LinearOrder M := linearOrderOfSTO r
  let : NoMaxOrder M := ⟨h.noMax⟩
  infer_instance

/-- The rational strict-order structure is a countably infinite model. -/
theorem strictDlo_rational_model :
    let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (fun a b => a < b)
    ℚ ⊨ Shared.strictDloTheory ∧ #ℚ = ℵ₀ := by
  let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (fun a b => a < b)
  refine ⟨Shared.model_strictDloTheory_iff.mpr ?_, Cardinal.mk_eq_aleph0 ℚ⟩
  exact dlo_axioms_of_order

/-- Countable models of the strict-order theory are isomorphic via the actual
finite atomic-map back-and-forth system. -/
theorem strictDlo_countable_models_isomorphic
    (M : Type u) (N : Type v) [SM : binaryRelLanguage.Structure M]
    [SN : binaryRelLanguage.Structure N] [Nonempty M] [Nonempty N]
    [Countable M] [Countable N]
    [M ⊨ Shared.strictDloTheory] [N ⊨ Shared.strictDloTheory] :
    Nonempty (M ≃[binaryRelLanguage] N) := by
  classical
  have hM := Shared.model_strictDloTheory_iff.mp (inferInstance : M ⊨ Shared.strictDloTheory)
  have hN := Shared.model_strictDloTheory_iff.mp (inferInstance : N ⊨ Shared.strictDloTheory)
  let r := Shared.relation (o := true) (M := M)
  let s := Shared.relation (o := true) (M := N)
  let : IsStrictTotalOrder M r :=
    { irrefl := hM.irrefl, trans := hM.trans,
      trichotomous := fun a b hab hba => ((hM.total a b).resolve_left hab).resolve_right hba }
  let : IsStrictTotalOrder N s :=
    { irrefl := hN.irrefl, trans := hN.trans,
      trichotomous := fun a b hab hba => ((hN.total a b).resolve_left hab).resolve_right hba }
  let : LinearOrder M := linearOrderOfSTO r
  let : LinearOrder N := linearOrderOfSTO s
  let : DenselyOrdered M := ⟨hM.dense⟩
  let : DenselyOrdered N := ⟨hN.dense⟩
  let : NoMinOrder M := ⟨hM.noMin⟩
  let : NoMinOrder N := ⟨hN.noMin⟩
  let : NoMaxOrder M := ⟨hM.noMax⟩
  let : NoMaxOrder N := ⟨hN.noMax⟩
  obtain ⟨e, _⟩ := strict_countable_isomorphism
    (A := M) (B := N) (emptyStrictPartialIso (A := M) (B := N))
  have hc : @Nonempty (@FirstOrder.Language.Equiv binaryRelLanguage M N
      (binaryRelStructure M r) (binaryRelStructure N s)) := ⟨e⟩
  have hSM : binaryRelStructure M r = SM := canonical_structure_eq SM
  have hSN : binaryRelStructure N s = SN := canonical_structure_eq SN
  rw [hSM, hSN] at hc
  exact hc

/-- Countable categoricity for the same actual strict-order theory used by the
quantifier-elimination entry. -/
theorem strictDlo_countably_categorical : (ℵ₀).Categorical Shared.strictDloTheory := by
  intro M N hM hN
  let : Countable M := Cardinal.mk_le_aleph0_iff.mp hM.le
  let : Countable N := Cardinal.mk_le_aleph0_iff.mp hN.le
  exact strictDlo_countable_models_isomorphic M N

/-- Apply the general cardinal test at countable infinity to the strict theory. -/
theorem strictDlo_complete : Shared.strictDloTheory.IsComplete := by
  apply Cardinal.Categorical.isComplete.{0, 0, 0} ℵ₀ Shared.strictDloTheory
    strictDlo_countably_categorical le_rfl
  · simpa only [Cardinal.lift_id, FirstOrder.Language.card] using
      (Cardinal.mk_le_aleph0_iff.mpr (inferInstance : Countable binaryRelLanguage.Symbols))
  · let : binaryRelLanguage.Structure ℚ := binaryRelStructure ℚ (fun a b => a < b)
    let : ℚ ⊨ Shared.strictDloTheory := strictDlo_rational_model.1
    exact Theory.Model.isSatisfiable ℚ
  · intro M
    exact strictDlo_models_infinite M

end Lemmatheca.ModelTheory.BackAndForth
