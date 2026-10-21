import Lemmatheca.PaProofCheckers.PAProofPredicateDefinitions
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

/-! Numerical, initial-segment and bounded-formula proof builders for the fixed PA predicate. -/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open CodingFormalProofs PAComputations
noncomputable section

/-- The remaining signed bounded proof builders. All other construction
operations below are explicit programs with independent correctness proofs. -/
structure ConstructionPrograms where
  positive : {r : ℕ} → (D : language.Formula (Fin r)) → DeltaZero D → Program r
  negative : {r : ℕ} → (D : language.Formula (Fin r)) → DeltaZero D → Program r

def ConstructionPrograms.substitution (_c : ConstructionPrograms) {r : ℕ}
    (A : language.Formula (Fin r)) : Program r := ProofPrograms.FixedSyntaxPrograms.substitution A

theorem ConstructionPrograms.substitution_eval (c : ConstructionPrograms) {r : ℕ}
    (A : language.Formula (Fin r)) (x : Fin r → ℕ) :
    (c.substitution A).eval x = sentenceCode arithmeticSignature (numeralInstance A x) :=
  ProofPrograms.FixedSyntaxPrograms.substitution_eval A x

def ConstructionPrograms.initialSegmentBuilder (_c : ConstructionPrograms) : Program 1 :=
  ProofPrograms.InitialSegmentPrograms.initialSegmentProof

def ConstructionPrograms.initialSegmentCode (_c : ConstructionPrograms) : Program 1 :=
  ProofPrograms.InitialSegmentPrograms.initialSegmentCode

theorem ConstructionPrograms.initialSegmentCode_eval (c : ConstructionPrograms) (x : Fin 1 → ℕ) :
    c.initialSegmentCode.eval x = sentenceCode arithmeticSignature (initialSegmentSentence (x 0)) :=
  ProofPrograms.InitialSegmentPrograms.initialSegmentCode_eval_inputs x

def ConstructionPrograms.termBuilder (_c : ConstructionPrograms) {r : ℕ}
    (t : language.Term (Fin r)) : Program r := ProofPrograms.CheckerPrograms.NumericalProofs.termBuilder t

def ConstructionPrograms.termCode (_c : ConstructionPrograms) {r : ℕ}
    (t : language.Term (Fin r)) : Program r := ProofPrograms.FixedSyntaxPrograms.termEquationCode t

theorem ConstructionPrograms.termCode_eval (c : ConstructionPrograms) {r : ℕ}
    (t : language.Term (Fin r)) (x : Fin r → ℕ) :
    (c.termCode t).eval x = sentenceCode arithmeticSignature (termEvaluationSentence t x) :=
  ProofPrograms.FixedSyntaxPrograms.termEquationCode_eval t x

def ConstructionPrograms.truthTest (_c : ConstructionPrograms) {r : ℕ}
    (D : language.Formula (Fin r)) (hD : DeltaZero D) : Program r :=
  ProofPrograms.CheckerPrograms.BoundedTruthPrograms.formulaTest D hD

def ConstructionPrograms.existentialBuilder (c : ConstructionPrograms) {r k : ℕ}
    (D : language.Formula (Fin r ⊕ Fin k)) (hD : DeltaZero D) : Program (r + k) :=
  ProofPrograms.CheckerPrograms.existentialBuilder D
    (c.positive (D.relabel finSumFinEquiv) (hD.relabel finSumFinEquiv))

def ConstructionPrograms.checker (_c : ConstructionPrograms) : Program 2 := checkerProgram

theorem ConstructionPrograms.checker_eval (c : ConstructionPrograms) (x : Fin 2 → ℕ) :
    c.checker.eval x = checkerValue x := ProofPrograms.CheckerPrograms.native_checker_eval x

def ConstructionPrograms.sentenceTest (_c : ConstructionPrograms) : Program 1 := sentenceProgram

theorem ConstructionPrograms.sentenceTest_eval (c : ConstructionPrograms) (x : Fin 1 → ℕ) :
    c.sentenceTest.eval x = if isSentence arithmeticSignature (x 0) then 1 else 0 :=
  ProofPrograms.CheckerPrograms.isSentence_eval x

def ConstructionPrograms.modusPonens (_c : ConstructionPrograms) : Program 3 := modusPonensProgram

/-- The explicit square-pair implication constructor. -/
def ConstructionPrograms.implication (_c : ConstructionPrograms) : Program 2 :=
  ProofPrograms.implication

theorem ConstructionPrograms.implication_eval (c : ConstructionPrograms) (x : Fin 2 → ℕ) :
    c.implication.eval x = impCode (x 0) (x 1) := ProofPrograms.implication_eval x

def ConstructionPrograms.proofFormula (_c : ConstructionPrograms) :
    language.Formula (Fin 2) :=
  _root_.Lemmatheca.ProofTheory.ArithmeticProofPredicates.proofFormula

/-- Ignore the witness coordinates when computing the closed existential's code. -/
def ConstructionPrograms.existentialCode (c : ConstructionPrograms) {r k : ℕ}
    (D : language.Formula (Fin r ⊕ Fin k)) : Program (r + k) :=
  .comp (c.substitution (D.iExs (Fin k))) (fun i => .proj (i.castAdd k))

def ConstructionPrograms.modusPonensFormula (_c : ConstructionPrograms) :
    language.Formula (Fin 4) :=
  _root_.Lemmatheca.ProofTheory.ArithmeticProofPredicates.modusPonensFormula

/-- Internal obligations about the actual PA checker, not external correctness
assumptions attached to an arbitrary representative. The existence theorem must
prove every field by the structural program construction. -/
structure InternalConstruction (c : ConstructionPrograms) : Prop where
  bounded_positive : ∀ {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D),
    Derives PA (close (D.imp
      (builderAccepted c.proofFormula (c.positive D hD) (c.substitution D))))
  bounded_negative : ∀ {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D),
    Derives PA (close (D.not.imp
      (builderAccepted c.proofFormula (c.negative D hD) (c.substitution D.not))))
theorem bounded_truth_internal {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D) :
    Derives PA (close ((testAt (ProofPrograms.CheckerPrograms.BoundedTruthPrograms.formulaTest D hD)
      Term.var).iff D)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  rw [Formula.realize_iff, testAt, realize_graphAt]
  simp only [Term.realize_var, realize_numeralTerm]
  rw [program_sigma_value, ProofPrograms.CheckerPrograms.BoundedTruthPrograms.formulaTest_value]
  rw [eq_comm, ProofPrograms.SyntaxPrograms.truthValue_eq_one_iff (M := M)]

theorem bounded_truth_boolean {r : ℕ} (D : language.Formula (Fin r)) (hD : DeltaZero D) :
    Derives PA (booleanOutputs (ProofPrograms.CheckerPrograms.BoundedTruthPrograms.formulaTest D hD)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [booleanOutputs, realize_allClose]
  intro v
  simp only [Formula.realize_imp, Formula.realize_sup, Formula.realize_equal,
    Term.realize_var, realize_zeroTerm, realize_numeralTerm]
  intro h
  let x : Fin r → M := fun i => v (.inl i)
  have hv : v = extend x (v (.inr ())) := by
    ext i
    cases i <;> rfl
  rw [hv, program_sigma_value,
    ProofPrograms.CheckerPrograms.BoundedTruthPrograms.formulaTest_value] at h
  by_cases hd : D.Realize x
  · exact Or.inr (by simpa only [ProofPrograms.SyntaxPrograms.truthValue, hd, ↓reduceIte] using h)
  · exact Or.inl (by simpa only [ProofPrograms.SyntaxPrograms.truthValue, hd, ↓reduceIte] using h)

/-- Construct the signed bounded proof builders for the specified actual PA
checker. The independently verified operations above then assemble arbitrary
finite existential prefixes. Derivability conditions and formalized completeness
are conclusions, never hypotheses of this construction. -/
theorem checkerConstruction_exists :
    ∃ c : ConstructionPrograms, InternalConstruction c := by
  let c : ConstructionPrograms := {
    positive := fun D hD => (ProofPrograms.CheckerPrograms.SignedProofs.compiled D hD).positive
    negative := fun D hD => (ProofPrograms.CheckerPrograms.SignedProofs.compiled D hD).negative
  }
  refine ⟨c, ?_⟩
  constructor
  · intro r D hD
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [realize_close]
    intro x
    apply Formula.realize_imp.mpr
    intro hx
    apply (realize_builderAccepted_value _ _ M x).mpr
    exact ProofPrograms.CheckerPrograms.SignedProofs.compiled_positive_correct D hD x hx
  · intro r D hD
    apply HenkinCompleteness.deductive_completeness
    apply Theory.models_sentence_iff.mpr
    intro M
    rw [realize_close]
    intro x
    apply Formula.realize_imp.mpr
    intro hx
    apply (realize_builderAccepted_value _ _ M x).mpr
    have hn : (ProofPrograms.FixedSyntaxPrograms.substitution D.not).value x =
        ProofPrograms.CheckerPrograms.negValue
          ((ProofPrograms.FixedSyntaxPrograms.substitution D).value x) := by
      rw [← ProofPrograms.CheckerPrograms.SignedProofs.projection_namedFormula,
        ProofPrograms.CheckerPrograms.BoundedSyntaxPrograms.namedFormula_not,
        ProofPrograms.CheckerPrograms.SignedProofs.projection_namedFormula]
    change ProofPrograms.CheckerPrograms.Certified ProofPrograms.CheckerPrograms.axiomVerifier
      ((ProofPrograms.CheckerPrograms.SignedProofs.compiled D hD).negative.value x)
      ((ProofPrograms.FixedSyntaxPrograms.substitution D.not).value x)
    rw [hn]
    exact ProofPrograms.CheckerPrograms.SignedProofs.compiled_negative_correct D hD x
      (Formula.realize_not.mp hx)

/-- Fix the signed bounded builders together with their internal proofs. -/
def construction : ConstructionPrograms := Classical.choose checkerConstruction_exists

theorem construction_internal : InternalConstruction construction :=
  Classical.choose_spec checkerConstruction_exists

theorem bounded_positive_internal {r : ℕ} (D : language.Formula (Fin r))
    (hD : DeltaZero D) :
    Derives PA (close (D.imp (builderAccepted proofFormula
      (construction.positive D hD) (construction.substitution D)))) :=
  construction_internal.bounded_positive D hD

theorem bounded_negative_internal {r : ℕ} (D : language.Formula (Fin r))
    (hD : DeltaZero D) :
    Derives PA (close (D.not.imp (builderAccepted proofFormula
      (construction.negative D hD) (construction.substitution D.not)))) :=
  construction_internal.bounded_negative D hD

theorem initial_segment_internal : Derives PA (close
    (builderAccepted proofFormula ProofPrograms.InitialSegmentPrograms.initialSegmentProof
      ProofPrograms.InitialSegmentPrograms.initialSegmentCode)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  rw [realize_builderAccepted_value]
  have hx : x = ![x 0] := by ext i; fin_cases i; rfl
  rw [hx]
  exact ProofPrograms.InitialSegmentPrograms.initialSegmentProof_certified (x 0)

theorem numerical_equations_internal {r : ℕ} (t : language.Term (Fin r)) :
    Derives PA (close (builderAccepted proofFormula
      (ProofPrograms.CheckerPrograms.NumericalProofs.termBuilder t)
      (ProofPrograms.FixedSyntaxPrograms.termEquationCode t))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  rw [realize_builderAccepted_value]
  exact ProofPrograms.CheckerPrograms.NumericalProofs.certified_termBuilder t x

/-- The actual numeral comparison constructors, expressed as PA assertions about
both their output graphs and the specified checker. -/
def numeralComparisonCode (order negative : Bool) : Program 2 :=
  let atom := if order then
    ProofPrograms.CheckerPrograms.NumericalProofs.orderCode
      (ProofPrograms.CheckerPrograms.NumericalProofs.num (.proj 0))
      (ProofPrograms.CheckerPrograms.NumericalProofs.num (.proj 1))
    else ProofPrograms.CheckerPrograms.equalCode
      (ProofPrograms.CheckerPrograms.NumericalProofs.num (.proj 0))
      (ProofPrograms.CheckerPrograms.NumericalProofs.num (.proj 1))
  if negative then ProofPrograms.CheckerPrograms.negCode atom else atom

def numeralComparisonBuilder (order negative : Bool) : Program 2 :=
  if order then
    if negative then ProofPrograms.CheckerPrograms.NumericalProofs.numeralNotLeBuilder
    else ProofPrograms.CheckerPrograms.NumericalProofs.numeralLeBuilder
  else
    if negative then ProofPrograms.CheckerPrograms.NumericalProofs.numeralNotEqualBuilder
    else ProofPrograms.CheckerPrograms.NumericalProofs.numeralEqualBuilder

def numeralComparisonAntecedent (order negative : Bool) : language.Formula (Fin 2) :=
  let atom : language.Formula (Fin 2) :=
    if order then leFormula (.var 0) (.var 1) else (Term.var 0).equal (.var 1)
  if negative then atom.not else atom

def numeralComparisonFormula (order negative : Bool) : language.Formula (Fin 2) :=
  (numeralComparisonAntecedent order negative).imp
    (builderAccepted proofFormula (numeralComparisonBuilder order negative)
      (numeralComparisonCode order negative))

/-- One uniform PA correctness implication for each of the four numerical
comparison branches, using the actual native proof constructors. -/
theorem numeral_comparison_internal (order negative : Bool) :
    Derives PA (close (numeralComparisonFormula order negative)) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro x
  have hpair : (![x 0, x 1] : Fin 2 → M) = x := by
    funext i; fin_cases i <;> rfl
  apply Formula.realize_imp.mpr
  intro hx
  apply (realize_builderAccepted_value _ _ M x).mpr
  cases order <;> cases negative
  · have heq : x 0 = x 1 := by
      simpa only [numeralComparisonAntecedent, Bool.false_eq_true, ↓reduceIte,
        Formula.realize_equal, Term.realize_var] using hx
    simpa only [numeralComparisonBuilder, numeralComparisonCode, Bool.false_eq_true,
      ↓reduceIte, ProofPrograms.CheckerPrograms.equalCode_value,
      ProofPrograms.CheckerPrograms.NumericalProofs.num_model_value,
      Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one,
      ProofPrograms.CheckerPrograms.NumericalProofs.numeralSyntax, hpair] using
      ProofPrograms.CheckerPrograms.NumericalProofs.certified_numeralEqualBuilder
        (x 0) (x 1) heq
  · have hne : x 0 ≠ x 1 := by
      simpa only [numeralComparisonAntecedent, Bool.false_eq_true, ↓reduceIte,
        Formula.realize_not, Formula.realize_equal, Term.realize_var] using hx
    simpa only [numeralComparisonBuilder, numeralComparisonCode, Bool.false_eq_true,
      ↓reduceIte, ProofPrograms.CheckerPrograms.negCode_value,
      ProofPrograms.CheckerPrograms.equalCode_value,
      ProofPrograms.CheckerPrograms.NumericalProofs.num_model_value,
      Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one,
      ProofPrograms.CheckerPrograms.NumericalProofs.numeralSyntax, hpair] using
      ProofPrograms.CheckerPrograms.NumericalProofs.certified_numeralNotEqualBuilder
        (x 0) (x 1) hne
  · have hle : leValue M (x 0) (x 1) := by
      simpa only [numeralComparisonAntecedent, Bool.false_eq_true, ↓reduceIte,
        realize_leFormula, Term.realize_var] using hx
    simpa only [numeralComparisonBuilder, numeralComparisonCode, Bool.false_eq_true,
      ↓reduceIte, ProofPrograms.CheckerPrograms.NumericalProofs.orderCode_value,
      ProofPrograms.CheckerPrograms.NumericalProofs.num_model_value,
      Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one,
      ProofPrograms.CheckerPrograms.NumericalProofs.numeralSyntax, hpair] using
      ProofPrograms.CheckerPrograms.NumericalProofs.certified_numeralLeBuilder
        (x 0) (x 1) hle
  · have hnot : ¬leValue M (x 0) (x 1) := by
      simpa only [numeralComparisonAntecedent, ↓reduceIte,
        Formula.realize_not, realize_leFormula, Term.realize_var] using hx
    simpa only [numeralComparisonBuilder, numeralComparisonCode, ↓reduceIte,
      ProofPrograms.CheckerPrograms.negCode_value,
      ProofPrograms.CheckerPrograms.NumericalProofs.orderCode_value,
      ProofPrograms.CheckerPrograms.NumericalProofs.num_model_value,
      Program.value_proj, Matrix.cons_val_zero, Matrix.cons_val_one,
      ProofPrograms.CheckerPrograms.NumericalProofs.numeralSyntax, hpair] using
      ProofPrograms.CheckerPrograms.NumericalProofs.certified_numeralNotLeBuilder
        (x 0) (x 1) hnot

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
