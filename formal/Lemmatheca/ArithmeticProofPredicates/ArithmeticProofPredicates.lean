import Lemmatheca.BoundedArithmeticProofs.PAProofConstruction
import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesPA
import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesLogic
import Lemmatheca.PaComputations.PAComputations
import Lemmatheca.PaComputations.PAFormulaComplexity
import Lemmatheca.PaListsAndSyntax.PAProofPrograms
import Lemmatheca.BoundedArithmeticProofs.PAInitialSegmentSyntax
import Lemmatheca.PaProofCheckers.PAProofCheckerCorrectness
import Lemmatheca.PaProofCheckers.PAProofModusPonens
import Lemmatheca.BoundedArithmeticProofs.PATermEvaluationProofs
import Lemmatheca.BoundedArithmeticProofs.PAInitialSegmentCertificates
import Lemmatheca.BoundedArithmeticProofs.PABoundedTruthPrograms
import Lemmatheca.PaProofCheckers.PAExistentialBuilders
import Lemmatheca.BoundedArithmeticProofs.PASignedBoundedProofs

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! A concrete PA proof predicate, with actual internal proof constructors.

Numerical normalization, finite initial segments, signed bounded proofs and
existential assembly use their specified native programs. Their correctness in
all PA models is converted into derivability in the shared calculus by deductive
completeness. Only arithmetically definable induction is used in those models.
-/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open CodingFormalProofs PAComputations
noncomputable section

theorem existential_append_internal {r k : ℕ}
    (D : language.Formula (Fin r ⊕ Fin k)) (hD : DeltaZero D) :
    Derives PA (close ((D.relabel finSumFinEquiv).imp
      (builderAccepted proofFormula (construction.existentialBuilder D hD)
        (construction.existentialCode D)))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x hx
  have hp := (realize_close M _).mp
    (pa_sound (bounded_positive_internal (D.relabel finSumFinEquiv)
      (hD.relabel finSumFinEquiv)) M) x hx
  have hp' := (realize_builderAccepted_value _ _ M x).mp hp
  apply (realize_builderAccepted_value _ _ M x).mpr
  exact ProofPrograms.CheckerPrograms.certified_existentialBuilder
    ProofPrograms.CheckerPrograms.axiomVerifier D
    (construction.positive (D.relabel finSumFinEquiv) (hD.relabel finSumFinEquiv)) x hp'

theorem formalized_completeness {r k : ℕ}
    (D : language.Formula (Fin r ⊕ Fin k)) (hD : DeltaZero D) :
    ParameterizedCompleteness proofFormula (D.iExs (Fin k))
      (substitutionGraph (D.iExs (Fin k))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x hA
  obtain ⟨y, hy⟩ := Formula.realize_iExs.mp hA
  let v : Fin (r + k) → M := fun i => Sum.elim x y (finSumFinEquiv.symm i)
  have hD' : (D.relabel finSumFinEquiv).Realize v := by
    rw [Formula.realize_relabel]
    convert hy using 1
    funext i
    simp [v]
  have hc := ((realize_close M _).mp
    (pa_sound (existential_append_internal D hD) M)) v hD'
  obtain ⟨p, a, _, ha, hP⟩ := (realize_builderAccepted _ _ _ M v).mp hc
  apply (realize_boxWithGraph _ _ x).mpr
  refine ⟨a, ?_, p, hP⟩
  obtain ⟨u, hu, hsub⟩ := (program_sigma_comp _ _ M v a).mp ha
  have hux : u = x := by
    funext i
    have hi := (program_sigma_proj (i.castAdd k) M v (u i)).mp (hu i)
    simpa [v] using hi
  simpa only [hux, substitutionGraph, ConstructionPrograms.substitution] using hsub

theorem closed_formalized_completeness : ClosedSigmaOneCompleteness proofFormula := by
  intro A hA
  obtain ⟨k, D, hD, rfl⟩ := hA
  let rename : Empty ⊕ Fin k → Fin 0 ⊕ Fin k := Sum.map Empty.elim id
  let D₀ : language.Formula (Fin 0 ⊕ Fin k) := D.relabel rename
  let A₀ : language.Formula (Fin 0) := D₀.iExs (Fin k)
  have hD₀ : DeltaZero D₀ := hD.relabel rename
  have hcode : numeralInstance A₀ (Fin.elim0 : Fin 0 → ℕ) = D.iExs (Fin k) := by
    dsimp only [A₀, D₀, numeralInstance]
    rw [subst_iExs, formula_relabel_subst]
    have hrename : underSubst (fun i : Fin 0 => numeral (Fin.elim0 i)) ∘ rename =
        (Term.var : Empty ⊕ Fin k → language.Term (Empty ⊕ Fin k)) := by
      funext i
      cases i with
      | inl i => exact i.elim
      | inr i => rfl
    simp only [Function.comp_def] at hrename
    rw [hrename, formula_subst_var]
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [Sentence.realize_imp]
  intro hA
  have hA₀ : A₀.Realize (Fin.elim0 : Fin 0 → M) := by
    have hi : M ⊨ numeralInstance A₀ (Fin.elim0 : Fin 0 → ℕ) := hcode.symm ▸ hA
    have hh := (realize_numeralInstance A₀ (Fin.elim0 : Fin 0 → ℕ)).mp hi
    convert hh using 1
  have hc := (realize_close M _).mp
    (pa_sound (formalized_completeness D₀ hD₀) M) Fin.elim0 hA₀
  obtain ⟨a, hsub, p, hproof⟩ := (realize_boxWithGraph _ _ Fin.elim0).mp hc
  have hsub' : a = numeralValue M ((construction.substitution A₀).eval Fin.elim0) := by
    apply (program_sigma_numerals _ M Fin.elim0 a).mp
    have hx : (fun i : Fin 0 => numeralValue M ((Fin.elim0 : Fin 0 → ℕ) i)) =
        (Fin.elim0 : Fin 0 → M) := by
      funext i
      exact i.elim0
    rw [hx]
    exact hsub
  rw [construction.substitution_eval, hcode] at hsub'
  apply (realize_box _ _ M).mpr
  exact ⟨p, hsub' ▸ hproof⟩

theorem derivability_one (A : language.Sentence) (hA : Derives PA A) :
    Derives PA (box A) := by
  obtain ⟨p, hp⟩ := (pa_proof_checker_correct A).mpr hA
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [box, realize_box]
  refine ⟨numeralValue M p, ?_⟩
  rw [proofFormula, checkerFormula, realize_graphAt]
  simp only [Term.realize_var, realize_numeralTerm]
  have htuple : (![numeralValue M p,
      numeralValue M (sentenceCode arithmeticSignature A)] : Fin 2 → M) =
      fun i => numeralValue M (![p, sentenceCode arithmeticSignature A] i) := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, program_sigma_numerals, checkerProgram, ProofPrograms.CheckerPrograms.native_checker_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hp, ↓reduceIte]

theorem derivability_two (A B : language.Sentence) :
    Derives PA ((box (A.imp B)).imp ((box A).imp (box B))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  simp only [Sentence.realize_imp]
  intro hAB hA
  obtain ⟨p, hp⟩ := (realize_box _ _ M).mp hAB
  obtain ⟨q, hq⟩ := (realize_box _ _ M).mp hA
  let a := sentenceCode arithmeticSignature A
  let b := sentenceCode arithmeticSignature B
  let na := numeralValue M a
  let nb := numeralValue M b
  let v : Fin 4 → M := ![p, q, na, nb]
  have hsa : isSentence arithmeticSignature a = true :=
    (sentence_recognition_iff _ _).mpr ⟨A, rfl⟩
  have hsb : isSentence arithmeticSignature b = true :=
    (sentence_recognition_iff _ _).mpr ⟨B, rfl⟩
  have htesta : sentenceProgram.sigmaGraph.Realize
      (extend ![na] (numeralValue M 1)) := by
    have hx : (fun i : Fin 1 => numeralValue M (![a] i)) = ![na] := by
      funext i
      fin_cases i
      rfl
    rw [← hx, program_sigma_numerals, sentenceProgram, ProofPrograms.CheckerPrograms.isSentence_eval]
    simp [hsa]
  have htestb : sentenceProgram.sigmaGraph.Realize
      (extend ![nb] (numeralValue M 1)) := by
    have hx : (fun i : Fin 1 => numeralValue M (![b] i)) = ![nb] := by
      funext i
      fin_cases i
      rfl
    rw [← hx, program_sigma_numerals, sentenceProgram, ProofPrograms.CheckerPrograms.isSentence_eval]
    simp [hsb]
  have himp : ProofPrograms.implication.sigmaGraph.Realize
      (extend ![na, nb] (numeralValue M (sentenceCode arithmeticSignature (A.imp B)))) := by
    have hx : (fun i : Fin 2 => numeralValue M (![a, b] i)) = ![na, nb] := by
      funext i
      fin_cases i <;> rfl
    rw [← hx, program_sigma_numerals, ProofPrograms.implication_eval]
    rfl
  have hm := (realize_close M _).mp (pa_sound modus_ponens_internal M) v
  simp only [modusPonensFormula, Formula.realize_imp,
    Formula.realize_inf] at hm
  have hta : (testAt sentenceProgram
      ![(Term.var (2 : Fin 4))]).Realize v := by
    rw [testAt, realize_graphAt, realize_numeralTerm]
    have hx : (fun i : Fin 1 =>
        ((![Term.var 2] : Fin 1 → language.Term (Fin 4)) i).realize v) = ![na] := by
      funext i
      fin_cases i
      rfl
    rw [hx]
    exact htesta
  have htb : (testAt sentenceProgram
      ![(Term.var (3 : Fin 4))]).Realize v := by
    rw [testAt, realize_graphAt, realize_numeralTerm]
    have hx : (fun i : Fin 1 =>
        ((![Term.var 3] : Fin 1 → language.Term (Fin 4)) i).realize v) = ![nb] := by
      funext i
      fin_cases i
      rfl
    rw [hx]
    exact htestb
  have hci : (computedConclusion proofFormula ProofPrograms.implication
      ![(Term.var (2 : Fin 4)), .var 3] (.var 0)).Realize v := by
    apply (realize_computedConclusion _ _ _ _ M v).mpr
    refine ⟨numeralValue M (sentenceCode arithmeticSignature (A.imp B)), ?_, ?_⟩
    · have hx : (fun i : Fin 2 =>
          ((![Term.var 2, Term.var 3] : Fin 2 → language.Term (Fin 4)) i).realize v) =
            ![na, nb] := by
        funext i
        fin_cases i <;> rfl
      rw [hx]
      exact himp
    · simpa [v] using hp
  have hqa : (proofAt proofFormula (.var (1 : Fin 4)) (.var 2)).Realize v := by
    simpa [realize_proofAt, v, na, a] using hq
  have hc := hm ⟨hta, htb, hci, hqa⟩
  obtain ⟨m, _, hproof⟩ := (realize_constructedProof _ _ _ _ M v).mp hc
  apply (realize_box _ _ M).mpr
  refine ⟨m, ?_⟩
  simpa [v, nb, b, proofFormula] using hproof

theorem derivability_three (A : language.Sentence) :
    Derives PA ((box A).imp (box (box A))) := by
  exact derivabilityThree_of_closedCompleteness proofFormula
    closed_formalized_completeness box_sigmaOne A

theorem consistency_standard : ℕ ⊨ consistency ↔ Consistent PA := by
  change (ℕ ⊨ (box ⊥).not) ↔ Consistent PA
  rw [Sentence.realize_not, box_standard]
  rfl

/-- The complete internal package, including the independently verified native
operations. This summary preserves the scope of the construction statement. -/
structure CompleteConstruction (c : ConstructionPrograms) : Prop extends InternalConstruction c where
  bounded_test_boolean : ∀ {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D),
    Derives PA (booleanOutputs (c.truthTest D hD))
  bounded_test : ∀ {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D),
    Derives PA (close ((testAt (c.truthTest D hD) Term.var).iff D))
  initial_segment : Derives PA (close
    (builderAccepted c.proofFormula c.initialSegmentBuilder c.initialSegmentCode))
  numerical_equations : ∀ {r : ℕ} (t : language.Term (Fin r)),
    Derives PA (close (builderAccepted c.proofFormula (c.termBuilder t) (c.termCode t)))
  modus_ponens : Derives PA (close c.modusPonensFormula)
  existential_append : ∀ {r k : ℕ} (D : language.Formula (Fin r ⊕ Fin k))
      (hD : DeltaZero D),
    Derives PA (close ((D.relabel finSumFinEquiv).imp
      (builderAccepted c.proofFormula (c.existentialBuilder D hD) (c.existentialCode D))))

theorem completeConstruction_exists : ∃ c : ConstructionPrograms, CompleteConstruction c := by
  refine ⟨construction, ?_⟩
  exact {
    toInternalConstruction := construction_internal
    bounded_test_boolean := bounded_truth_boolean
    bounded_test := bounded_truth_internal
    initial_segment := initial_segment_internal
    numerical_equations := numerical_equations_internal
    modus_ponens := modus_ponens_internal
    existential_append := existential_append_internal
  }



end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
