import Lemmatheca.PaListsAndSyntax.PANativeNoAux
import Lemmatheca.PaProofCheckers.PAProofAxiomScan

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Accepted PA certificates retain contexts consisting of original-language
sentences. All auxiliary names are therefore fresh for those contexts. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem axiomList_contextFresh (E : Program 2) (j gamma ws : M)
    (hlen : listLength.value ![gamma] = listLength.value ![ws])
    (hcheck : axiomListValue E gamma ws = numeralValue M 1) :
    contextFresh.value ![j, gamma] = numeralValue M 1 := by
  have hall : ∀ gamma : M, ∀ ws : M,
      listLength.value ![gamma] = listLength.value ![ws] →
      axiomListValue E gamma ws = numeralValue M 1 →
      contextFresh.value ![j, gamma] = numeralValue M 1 := by
    apply list_code_induction
    · change DPred (fun v : Fin 1 → M => ∀ ws : M,
        listLength.value ![v 0] = listLength.value ![ws] →
        axiomListValue E (v 0) ws = numeralValue M 1 →
        contextFresh.value ![j, v 0] = numeralValue M 1)
      unfold axiomListValue
      pa_definable
    · intro ws _ _
      exact contextFresh_zero_value j
    · intro a gamma ih ws hlen hcheck
      have hws : ws ≠ zeroValue M := by
        intro hz
        rw [hz, listLength_cons_value, listLength_zero_value] at hlen
        exact successor_ne_zero _ hlen
      let w := listHead.value ![ws]
      let tail := listTail.value ![ws]
      have hd : listCons.value ![w, tail] = ws := cons_head_tail_value ws hws
      have ht : listLength.value ![gamma] = listLength.value ![tail] := by
        rw [← hd, listLength_cons_value, listLength_cons_value] at hlen
        exact successor_injective hlen
      rw [← hd, axiomList_cons_value, mul_eq_one_model] at hcheck
      have hsent : isSentence.value ![a] = numeralValue M 1 :=
        ((mul_eq_one_model _ _).mp hcheck.1).1
      apply (contextFresh_cons_one_iff j a gamma).mpr
      exact ⟨isSentence_occursAux_zero j a hsent, ih tail ht hcheck.2⟩
  exact hall gamma ws hlen hcheck

theorem certified_contextFresh (E : Program 2) (j p a : M) (hp : Certified E p a) :
    contextFresh.value ![j, contextValue (rootValue p)] = numeralValue M 1 := by
  obtain ⟨_, _, _, _, hlen, hcheck⟩ := (certified_iff E p a).mp hp
  exact axiomList_contextFresh E j _ _ hlen hcheck

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
