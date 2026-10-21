import Lemmatheca.PaComputations.PAComputationsSentences
import Lemmatheca.PaInductionAndHistories.PAFormulaDefinability

open Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory Lemmatheca.ProofTheory

namespace Lemmatheca.Entry.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability PAComputations
noncomputable section
universe u

def doubling : Program 1 :=
  .prec .zero (.comp .succ (fun _ => .comp .succ (fun _ => .proj 1)))

theorem doubling_model {M : Type u} [language.Structure M] [M ⊨ PA] (n y : M) :
    doubling.graph.Realize (extend ![n] y) ↔ y = addValue M n n := by
  have hvec (a : M) : Fin.snoc (Fin.elim0 : Fin 0 → M) a = ![a] := by
    funext i
    fin_cases i
    rfl
  have hv : ∀ n : M, doubling.value ![n] = addValue M n n := by
    apply definable_induction
    · change DPred (fun v : Fin 1 → M =>
        doubling.value ![v 0] = addValue M (v 0) (v 0))
      apply dp_eq
      · apply (Program.value_definable doubling).comp
        intro i
        fin_cases i
        exact df_proj 0
      · exact df_add _ _ (df_proj 0) (df_proj 0)
    · have h := Program.value_rec_zero Program.zero
        (Program.comp Program.succ (fun _ => Program.comp Program.succ
          (fun _ => Program.proj (1 : Fin 2)))) (Fin.elim0 : Fin 0 → M)
      simpa [hvec, doubling, Program.value_zero, add_zero_value] using h
    · intro k ih
      have h := Program.value_rec_succ Program.zero
        (Program.comp Program.succ (fun _ => Program.comp Program.succ
          (fun _ => Program.proj (1 : Fin 2)))) (Fin.elim0 : Fin 0 → M) k
      have hrec : doubling.value ![succValue M k] =
          succValue M (succValue M (doubling.value ![k])) := by
        simpa [hvec, doubling, Program.value_comp, Program.value_succ,
          Program.value_proj, Fin.snoc] using h
      rw [hrec, ih, add_successor_value, successor_add_value]
  rw [← hv n]
  exact doubling.value_iff ![n] y

/-- The displayed doubling identity is an actual PA theorem for the chosen
normalized graph, including its nonstandard inputs. -/
theorem doubling_derives : PAEquivalent doubling.sigmaGraph
    (termGraph (addTerm (.var (0 : Fin 1)) (.var 0))) := by
  apply derives_allClose_of_models
  intro M v
  rw [Formula.realize_iff]
  have he := Formula.realize_iff.mp ((realize_allClose _).mp
    (FirstOrderProofs.derives_sound doubling.sigmaGraph_equivalent default
      (fun B hB => Theory.realize_sentence_of_mem PA hB)) v)
  have hv : extend ![v (.inl 0)] (v (.inr ())) = v := by
    funext j
    cases j with
    | inl j => fin_cases j; rfl
    | inr j => cases j; rfl
  rw [← hv] at he ⊢
  rw [← he, doubling_model]
  simp only [termGraph, Formula.realize_equal, realize_addTerm,
    Term.realize_var, Term.realize_relabel, Function.comp_def,
    extend, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero]

end
end Lemmatheca.Entry.PAComputations
