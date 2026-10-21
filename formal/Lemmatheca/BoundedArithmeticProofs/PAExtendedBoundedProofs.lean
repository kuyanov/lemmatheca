import Lemmatheca.BoundedArithmeticProofs.PAProofConstruction
import Lemmatheca.PaComputations.PABoundedNormalization
import Lemmatheca.PaProofCheckers.PAFixedProofSpecialization

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Proof construction for the full bounded grammar. A fixed PA equivalence
between a formula and its inclusive-bound normal form is specialized at internal
numerals using the actual native checker. This retains the original formula code.
-/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open PAComputations ProofPrograms ProofPrograms.SyntaxPrograms ProofPrograms.FixedSyntaxPrograms
open ProofPrograms.CheckerPrograms
noncomputable section

def mapFixedProof {r : ℕ} (A B : language.Formula (Fin r))
    (h : Derives PA (close (A.imp B))) (p : Program r) : Program r :=
  ternary modusPonensCertificate (specializeFixed (A.imp B) h) p (substitution B)

theorem substitution_imp_value {r : ℕ} (A B : language.Formula (Fin r))
    {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M) :
    (substitution (A.imp B)).value x = implication.value
      ![(substitution A).value x, (substitution B).value x] := by
  rw [substitution_model_value, substitution_model_value, substitution_model_value,
    implication_value]
  rfl

theorem certified_mapFixedProof {r : ℕ} (A B : language.Formula (Fin r))
    (h : Derives PA (close (A.imp B))) (p : Program r)
    {M : Type} [language.Structure M] [M ⊨ PA] (x : Fin r → M)
    (hp : Certified axiomVerifier (p.value x) ((substitution A).value x)) :
    Certified axiomVerifier ((mapFixedProof A B h p).value x) ((substitution B).value x) := by
  have hf := certified_specializeFixed (A.imp B) h x
  rw [substitution_imp_value] at hf
  rw [mapFixedProof, ternary_value]
  exact certified_modusPonens axiomVerifier _ _ _ _ hf hp
    (substitution_pure B x).sentence

theorem normalForm_forward {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (close (D.imp hD.normalForm)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  exact Formula.realize_imp.mpr (hD.normalForm_realize M x).mp

theorem normalForm_backward {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (close (hD.normalForm.imp D)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  exact Formula.realize_imp.mpr (hD.normalForm_realize M x).mpr

theorem normalForm_negative_backward {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (close (hD.normalForm.not.imp D.not)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  simp only [Formula.realize_imp, Formula.realize_not]
  exact fun hn hd => hn ((hD.normalForm_realize M x).mp hd)

def boundedPositive {r : ℕ} (D : language.Formula (Fin r)) (hD : BoundedArithmetic D) :
    Program r :=
  mapFixedProof hD.normalForm D (normalForm_backward D hD)
    (construction.positive hD.normalForm hD.normalForm_deltaZero)

def boundedNegative {r : ℕ} (D : language.Formula (Fin r)) (hD : BoundedArithmetic D) :
    Program r :=
  mapFixedProof hD.normalForm.not D.not (normalForm_negative_backward D hD)
    (construction.negative hD.normalForm hD.normalForm_deltaZero)

def boundedTruth {r : ℕ} (D : language.Formula (Fin r)) (hD : BoundedArithmetic D) :
    Program r :=
  ProofPrograms.CheckerPrograms.BoundedTruthPrograms.formulaTest
    hD.normalForm hD.normalForm_deltaZero

theorem bounded_truth_internal_full {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (close
      ((testAt (boundedTruth D hD) Term.var).iff D)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  have hc := (realize_close M _).mp
    (pa_sound (bounded_truth_internal hD.normalForm hD.normalForm_deltaZero) M) x
  apply Formula.realize_iff.mpr
  exact (Formula.realize_iff.mp hc).trans (hD.normalForm_realize M x).symm

theorem bounded_truth_boolean_full {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (booleanOutputs (boundedTruth D hD)) :=
  bounded_truth_boolean hD.normalForm hD.normalForm_deltaZero

theorem bounded_positive_internal_full {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (close (D.imp
      (builderAccepted proofFormula (boundedPositive D hD) (substitution D)))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  apply Formula.realize_imp.mpr
  intro hd
  apply (realize_builderAccepted_value _ _ M x).mpr
  apply certified_mapFixedProof
  have hh := construction_internal.bounded_positive hD.normalForm hD.normalForm_deltaZero
  have hm := (realize_close M _).mp (pa_sound hh M) x
  have hc := (Formula.realize_imp.mp hm) ((hD.normalForm_realize M x).mp hd)
  exact (realize_builderAccepted_value _ _ M x).mp hc

theorem bounded_negative_internal_full {r : ℕ} (D : language.Formula (Fin r))
    (hD : BoundedArithmetic D) : Derives PA (close (D.not.imp
      (builderAccepted proofFormula (boundedNegative D hD) (substitution D.not)))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  apply Formula.realize_imp.mpr
  intro hd
  apply (realize_builderAccepted_value _ _ M x).mpr
  apply certified_mapFixedProof
  have hh := construction_internal.bounded_negative hD.normalForm hD.normalForm_deltaZero
  have hm := (realize_close M _).mp (pa_sound hh M) x
  have hn : hD.normalForm.not.Realize x := by
    apply Formula.realize_not.mpr
    exact fun he => (Formula.realize_not.mp hd) ((hD.normalForm_realize M x).mpr he)
  exact (realize_builderAccepted_value _ _ M x).mp (Formula.realize_imp.mp hm hn)

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
