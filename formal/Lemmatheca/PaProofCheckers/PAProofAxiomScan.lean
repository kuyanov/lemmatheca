import Lemmatheca.PaProofCheckers.PAProofCheckerOperations

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def axiomCondition (E : Program 2) (a w : M) : M :=
  mulValue M (isSentence.value ![a]) (E.value ![a, w])

theorem axiomScan_zero_value (E : Program 2) (gamma ws : M) :
    (axiomScan E).value ![gamma, ws, zeroValue M] = numeralValue M 1 := by
  have hv : Fin.snoc (![gamma, ws] : Fin 2 → M) (zeroValue M) =
      ![gamma, ws, zeroValue M] := by ext i; fin_cases i <;> rfl
  simpa only [axiomScan, hv, constant_value] using
    Program.value_rec_zero (constant 1 : Program 2) (axiomScanStep E) ![gamma, ws]

theorem axiomScan_successor_value (E : Program 2) (gamma ws k : M) :
    (axiomScan E).value ![gamma, ws, succValue M k] =
      mulValue M ((axiomScan E).value ![gamma, ws, k])
        (axiomCondition E (listEntry.value ![gamma, k]) (listEntry.value ![ws, k])) := by
  have hv (a : M) : Fin.snoc (![gamma, ws] : Fin 2 → M) a = ![gamma, ws, a] := by
    ext i; fin_cases i <;> rfl
  have he := Program.value_rec_succ (constant 1 : Program 2) (axiomScanStep E) ![gamma, ws] k
  simp only [axiomScanStep, conjunction_cons_value, conjunction_nil_value,
    binary_value, unary_value, Program.value_proj, mul_numeral_one_model, hv] at he
  exact he

theorem axiomScan_cons_prefix_value (E : Program 2) (a gamma w ws k : M) :
    (axiomScan E).value ![listCons.value ![a, gamma], listCons.value ![w, ws], succValue M k] =
      mulValue M (axiomCondition E a w) ((axiomScan E).value ![gamma, ws, k]) := by
  apply definable_induction
    (fun k => (axiomScan E).value
      ![listCons.value ![a, gamma], listCons.value ![w, ws], succValue M k] =
        mulValue M (axiomCondition E a w) ((axiomScan E).value ![gamma, ws, k]))
  · change DPred (fun v : Fin 1 → M => (axiomScan E).value
      ![listCons.value ![a, gamma], listCons.value ![w, ws], succValue M (v 0)] =
        mulValue M (axiomCondition E a w) ((axiomScan E).value ![gamma, ws, v 0]))
    unfold axiomCondition
    pa_definable
  · rw [axiomScan_successor_value, axiomScan_zero_value, axiomScan_zero_value,
      listEntry_cons_zero_value, listEntry_cons_zero_value,
      numeral_one_mul_model, mul_numeral_one_model]
  · intro k ih
    rw [axiomScan_successor_value E _ _ (succValue M k),
      listEntry_cons_successor_value, listEntry_cons_successor_value, ih,
      axiomScan_successor_value]
    exact mul_assoc_value _ _ _

def axiomListValue (E : Program 2) (gamma ws : M) : M :=
  (axiomScan E).value ![gamma, ws, listLength.value ![gamma] ]

theorem axiomList_zero_value (E : Program 2) (ws : M) :
    axiomListValue E (zeroValue M) ws = numeralValue M 1 := by
  rw [axiomListValue, listLength_zero_value, axiomScan_zero_value]

theorem axiomList_cons_value (E : Program 2) (a gamma w ws : M) :
    axiomListValue E (listCons.value ![a, gamma]) (listCons.value ![w, ws]) =
      mulValue M (axiomCondition E a w) (axiomListValue E gamma ws) := by
  rw [axiomListValue, listLength_cons_value, axiomScan_cons_prefix_value]
  rfl

theorem axiomList_append_value (E : Program 2) (gamma ws delta vs : M)
    (hlen : listLength.value ![gamma] = listLength.value ![ws]) :
    axiomListValue E (listAppend.value ![gamma, delta]) (listAppend.value ![ws, vs]) =
      mulValue M (axiomListValue E gamma ws) (axiomListValue E delta vs) := by
  have hall : ∀ gamma : M, ∀ ws delta vs,
      listLength.value ![gamma] = listLength.value ![ws] →
      axiomListValue E (listAppend.value ![gamma, delta]) (listAppend.value ![ws, vs]) =
        mulValue M (axiomListValue E gamma ws) (axiomListValue E delta vs) := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ ws delta vs,
        listLength.value ![v 0] = listLength.value ![ws] →
        axiomListValue E (listAppend.value ![v 0, delta]) (listAppend.value ![ws, vs]) =
          mulValue M (axiomListValue E (v 0) ws) (axiomListValue E delta vs))
      unfold axiomListValue
      pa_definable
    · intro ws delta vs hw
      rw [listLength_zero_value] at hw
      have hz := (listLength_zero_iff_value ws).mp hw.symm
      subst ws
      rw [listAppend_zero_value, listAppend_zero_value, axiomList_zero_value,
        numeral_one_mul_model]
    · intro a gamma ih ws delta vs hw
      have hws : ws ≠ zeroValue M := by
        intro hz
        rw [hz, listLength_cons_value, listLength_zero_value] at hw
        exact successor_ne_zero _ hw
      let w := listHead.value ![ws]
      let tail := listTail.value ![ws]
      have hd : listCons.value ![w, tail] = ws := cons_head_tail_value ws hws
      have ht : listLength.value ![gamma] = listLength.value ![tail] := by
        rw [← hd, listLength_cons_value, listLength_cons_value] at hw
        exact successor_injective hw
      rw [← hd, listAppend_cons_value, listAppend_cons_value,
        axiomList_cons_value, axiomList_cons_value, ih tail delta vs ht]
      exact (mul_assoc_value _ _ _).symm
  exact hall gamma ws delta vs hlen

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
