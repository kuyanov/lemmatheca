import Lemmatheca.MathematicalLogic.PAComputationsCoding
import Lemmatheca.MathematicalLogic.PAInduction

/-! Closed arithmetic theorems accompanying the internal-model arguments. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

theorem derives_allClose_of_models {α : Type} [Fintype α]
    (φ : language.Formula α)
    (h : ∀ (M : Theory.ModelType.{0,0,0} PA) (v : α → M), φ.Realize v) :
    Derives PA (allClose φ) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  exact (realize_allClose _).mpr (h M)

def leastWitnessSentence {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) : language.Sentence :=
  let smaller : language.Formula ((Fin k ⊕ Unit) ⊕ Unit) :=
    (ltFormula (.var (.inr ())) (.var (.inl (.inr ())))).imp
      (φ.relabel (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr ()))).not
  allClose ((φ.iExs Unit).imp ((φ ⊓ smaller.iAlls Unit).iExs Unit))

theorem least_witness_derives {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) :
    Derives PA (leastWitnessSentence φ) := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_not, Formula.realize_relabel,
    ltFormula, realize_leFormula, realize_succTerm, Term.realize_var,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  rintro ⟨a, ha⟩
  obtain ⟨y, hy, hmin⟩ := least_witness_model φ v ⟨a (), ha⟩
  refine ⟨fun _ => y, hy, ?_⟩
  intro z hz
  have he : (fun x => Sum.elim (Sum.elim v (fun _ : Unit => y)) z
      (Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ()) x)) =
      extend v (z ()) := by
    funext i
    cases i <;> rfl
  simpa only [he] using hmin (z ()) hz

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
end Lemmatheca.MathematicalLogic.PAComputations
