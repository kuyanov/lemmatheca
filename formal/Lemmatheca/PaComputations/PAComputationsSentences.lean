import Lemmatheca.PaComputations.PAProgramValues
import Lemmatheca.PaInductionAndHistories.PALeastWitnessSentences
import Lemmatheca.PaInductionAndHistories.PAInduction

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Closed arithmetic theorems accompanying the internal-model arguments. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

/-- Modelwise equality of the specified programs gives a PA proof of their graph equivalence. -/
theorem Program.equivalent_of_values {n : ℕ} (p q : Program n)
    (h : ∀ (M : Theory.ModelType.{0,0,0} PA) (x : Fin n → M), p.value x = q.value x) :
    PAEquivalent p.graph q.graph := by
  apply derives_allClose_of_models
  intro M v
  rw [Formula.realize_iff]
  let x : Fin n → M := fun i => v (.inl i)
  have hv : extend x (v (.inr ())) = v := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => cases j; rfl
  rw [← hv, p.value_iff, q.value_iff, h M x]

theorem Program.sigmaGraph_numeralwise {n : ℕ} (p : Program n) (x : Fin n → ℕ) :
    Derives PA (outputIdentity p.sigmaGraph x (p.eval x)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  let : M ⊨ Q := PA_models_Q M
  change ((((specializeInputs p.sigmaGraph x).iff
    ((Term.var ()).equal (numeralTerm (p.eval x)))).relabel
    (Sum.inr : Unit → Empty ⊕ Unit)).iAlls Unit).Realize _
  simp only [Formula.realize_iAlls, Formula.realize_relabel,
    Formula.realize_iff, Formula.realize_equal, Term.realize_var,
    realize_numeralTerm, Function.comp_def, Sum.elim_inr, realize_specializeInputs]
  intro y
  have he := (realize_allClose _).mp
    (derives_sound p.sigmaGraph_equivalent default
      (fun B hB => Theory.realize_sentence_of_mem PA hB))
    (extend (fun j => numeralValue M (x j)) (y ()))
  exact (Formula.realize_iff.mp he).symm.trans
    (stronglyRepresents_modelwise p.graph_numeralwise x (y ()))

theorem Program.sigmaGraph_composition {m n : ℕ} (f : Program m) (g : Fin m → Program n) :
    PAEquivalent (Program.comp f g).sigmaGraph
      (compositionGraph f.sigmaGraph (fun i => (g i).sigmaGraph)) := by
  apply derives_allClose_of_models
  intro M v
  rw [Formula.realize_iff]
  have equiv {k : ℕ} (p : Program k) (w : Fin k ⊕ Unit → M) :
      p.sigmaGraph.Realize w ↔ p.graph.Realize w := by
    exact (Formula.realize_iff.mp ((realize_allClose _).mp
      (derives_sound p.sigmaGraph_equivalent default
        (fun B hB => Theory.realize_sentence_of_mem PA hB)) w)).symm
  rw [equiv]
  let x : Fin n → M := fun i => v (.inl i)
  have hv : extend x (v (.inr ())) = v := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => cases j; rfl
  rw [← hv]
  change (compositionGraph f.graph (fun i => (g i).graph)).Realize _ ↔ _
  simp only [realize_compositionGraph, equiv]

end
end Lemmatheca.ProofTheory.PAComputations
