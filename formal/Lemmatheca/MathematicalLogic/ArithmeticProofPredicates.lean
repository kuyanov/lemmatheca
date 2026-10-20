import Lemmatheca.MathematicalLogic.ArithmeticProofPredicatesPA
import Lemmatheca.MathematicalLogic.ArithmeticProofPredicatesLogic
import Lemmatheca.MathematicalLogic.PAComputations
import Lemmatheca.MathematicalLogic.PAFormulaComplexity
import Lemmatheca.MathematicalLogic.PAProofPrograms
import Lemmatheca.MathematicalLogic.PAInitialSegmentSyntax
import Lemmatheca.MathematicalLogic.PAProofCheckerCorrectness
import Lemmatheca.MathematicalLogic.PAProofModusPonens
import Lemmatheca.MathematicalLogic.PATermEvaluationProofs
import Lemmatheca.MathematicalLogic.PAInitialSegmentCertificates
import Lemmatheca.MathematicalLogic.PABoundedTruthPrograms
import Lemmatheca.MathematicalLogic.PAExistentialBuilders
import Lemmatheca.MathematicalLogic.PASignedBoundedProofs

/-! A concrete PA proof predicate, with actual internal proof constructors.

Numerical normalization, finite initial segments, signed bounded proofs and
existential assembly use their specified native programs. Their correctness in
all PA models is converted into derivability in the shared calculus by deductive
completeness. Only arithmetically definable induction is used in those models.
-/
namespace Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open CodingFormalProofs PAComputations
noncomputable section

def checkerProgram : Program 2 :=
  ProofPrograms.CheckerPrograms.certificateCheck ProofPrograms.CheckerPrograms.axiomVerifier

def sentenceProgram : Program 1 := ProofPrograms.CheckerPrograms.isSentence
def modusPonensProgram : Program 3 := ProofPrograms.CheckerPrograms.modusPonensCertificate

def checkerValue (x : Fin 2 → ℕ) : ℕ :=
  if certificateCheck arithmeticSignature paAxiomCertificate (x 0) (x 1) then 1 else 0

/-- The normalized graph of this particular checker presentation, with output 1. -/
def checkerFormula (p : Program 2) : language.Formula (Fin 2) :=
  graphAt p.sigmaGraph Term.var (numeralTerm 1)

def proofFormula : language.Formula (Fin 2) := checkerFormula checkerProgram

/-- A positive assertion about the output of a particular program. -/
def testAt {n : ℕ} {α : Type*} (p : Program n)
    (xs : Fin n → language.Term α) : language.Formula α :=
  graphAt p.sigmaGraph xs (numeralTerm 1)

def booleanOutputs {n : ℕ} (p : Program n) : language.Sentence :=
  allClose (p.sigmaGraph.imp
    (((Term.var (.inr ())).equal zeroTerm) ⊔
      ((Term.var (.inr ())).equal (numeralTerm 1))))

/-- A builder and a conclusion-code program have outputs accepted by the
specified actual proof formula. Both output graphs are retained explicitly. -/
def builderAccepted {r : ℕ} (P : language.Formula (Fin 2))
    (builder conclusion : Program r) : language.Formula (Fin r) :=
  ((graphAt builder.sigmaGraph (fun i => .var (.inl i)) (.var (.inr (0 : Fin 2)))) ⊓
    ((graphAt conclusion.sigmaGraph (fun i => .var (.inl i)) (.var (.inr (1 : Fin 2)))) ⊓
      proofAt P (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2))))).iExs (Fin 2)

def computedConclusion {n : ℕ} {α : Type*} (P : language.Formula (Fin 2))
    (code : Program n) (xs : Fin n → language.Term α) (p : language.Term α) :
    language.Formula α :=
  ((graphAt code.sigmaGraph (fun i => (xs i).relabel Sum.inl) (.var (.inr ()))) ⊓
    proofAt P (p.relabel Sum.inl) (.var (.inr ()))).iExs Unit

def constructedProof {n : ℕ} {α : Type*} (P : language.Formula (Fin 2))
    (builder : Program n) (xs : Fin n → language.Term α) (a : language.Term α) :
    language.Formula α :=
  ((graphAt builder.sigmaGraph (fun i => (xs i).relabel Sum.inl) (.var (.inr ()))) ⊓
    proofAt P (.var (.inr ())) (a.relabel Sum.inl)).iExs Unit

def termEvaluationSentence {r : ℕ} (t : language.Term (Fin r)) (x : Fin r → ℕ) :
    language.Sentence :=
  (t.subst (fun i => numeral (x i))).equal (numeral (t.realize x))

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
  _root_.Lemmatheca.MathematicalLogic.ArithmeticProofPredicates.proofFormula

/-- Ignore the witness coordinates when computing the closed existential's code. -/
def ConstructionPrograms.existentialCode (c : ConstructionPrograms) {r k : ℕ}
    (D : language.Formula (Fin r ⊕ Fin k)) : Program (r + k) :=
  .comp (c.substitution (D.iExs (Fin k))) (fun i => .proj (i.castAdd k))

def modusPonensFormula :
    language.Formula (Fin 4) :=
  let p : language.Term (Fin 4) := .var 0
  let q : language.Term (Fin 4) := .var 1
  let a : language.Term (Fin 4) := .var 2
  let b : language.Term (Fin 4) := .var 3
  ((testAt sentenceProgram ![a]) ⊓ ((testAt sentenceProgram ![b]) ⊓
    ((computedConclusion proofFormula ProofPrograms.implication ![a, b] p) ⊓
      proofAt proofFormula q a))).imp
    (constructedProof proofFormula modusPonensProgram ![p, q, b] b)

def ConstructionPrograms.modusPonensFormula (_c : ConstructionPrograms) :
    language.Formula (Fin 4) :=
  _root_.Lemmatheca.MathematicalLogic.ArithmeticProofPredicates.modusPonensFormula

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
def proofPredicate : language.Formula Unit := provabilityFormula proofFormula
def box (A : language.Sentence) : language.Sentence := provabilitySentence proofFormula A
def consistency : language.Sentence := consistencySentence proofFormula

def substitutionGraph {r : ℕ} (A : language.Formula (Fin r)) :
    language.Formula (Fin r ⊕ Unit) := (ProofPrograms.FixedSyntaxPrograms.substitution A).sigmaGraph

def formulaBox {r : ℕ} (A : language.Formula (Fin r)) : language.Formula (Fin r) :=
  boxWithGraph proofFormula (substitutionGraph A)

theorem pa_sound {A : language.Sentence} (h : Derives PA A)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ PA] : M ⊨ A :=
  derives_sound h default (fun _ hB => Theory.realize_sentence_of_mem PA hB)

private theorem program_sigma_model {n : ℕ} (p : Program n) (M : Type)
    [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin n → M) (y : M) :
    p.graph.Realize (extend x y) ↔ p.sigmaGraph.Realize (extend x y) := by
  have he := (realize_allClose _).mp (pa_sound p.sigmaGraph_equivalent M) (extend x y)
  exact Formula.realize_iff.mp he

theorem program_sigma_value {n : ℕ} (p : Program n) (M : Type)
    [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin n → M) (y : M) :
    p.sigmaGraph.Realize (extend x y) ↔ y = p.value x := by
  rw [← program_sigma_model]
  exact p.value_iff x y

theorem program_sigma_numerals {n : ℕ} (p : Program n) (M : Type)
    [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin n → ℕ) (y : M) :
    p.sigmaGraph.Realize (extend (fun i => numeralValue M (x i)) y) ↔
      y = numeralValue M (p.eval x) := by
  let : M ⊨ Q := PA_models_Q M
  rw [← program_sigma_model]
  exact stronglyRepresents_modelwise p.graph_numeralwise x y

private theorem program_sigma_comp {m n : ℕ} (f : Program m) (gs : Fin m → Program n)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin n → M) (y : M) :
    (Program.comp f gs).sigmaGraph.Realize (extend x y) ↔
      ∃ a : Fin m → M, (∀ i, (gs i).sigmaGraph.Realize (extend x (a i))) ∧
        f.sigmaGraph.Realize (extend a y) := by
  rw [← program_sigma_model, Program.graph, realize_compositionGraph]
  apply exists_congr
  intro a
  rw [program_sigma_model]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro i
  exact program_sigma_model _ M _ _

private theorem program_sigma_proj {n : ℕ} (i : Fin n) (M : Type)
    [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin n → M) (y : M) :
    (Program.proj i).sigmaGraph.Realize (extend x y) ↔ y = x i := by
  rw [← program_sigma_model]
  simp [Program.graph, termGraph, extend]

private theorem realize_builderAccepted {r : ℕ} (P : language.Formula (Fin 2))
    (builder conclusion : Program r) (M : Type) [language.Structure M] (x : Fin r → M) :
    (builderAccepted P builder conclusion).Realize x ↔
      ∃ p a : M, builder.sigmaGraph.Realize (extend x p) ∧
        conclusion.sigmaGraph.Realize (extend x a) ∧ P.Realize ![p, a] := by
  simp only [builderAccepted, Formula.realize_iExs, Formula.realize_inf,
    realize_graphAt, realize_proofAt, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  constructor
  · rintro ⟨v, hp, ha, hP⟩
    exact ⟨v 0, v 1, hp, ha, hP⟩
  · rintro ⟨p, a, hp, ha, hP⟩
    exact ⟨![p, a], hp, ha, hP⟩

theorem realize_proofFormula_value (M : Type)
    [language.Structure M] [Nonempty M] [M ⊨ PA] (p a : M) :
    proofFormula.Realize ![p, a] ↔
      ProofPrograms.CheckerPrograms.Certified ProofPrograms.CheckerPrograms.axiomVerifier p a := by
  rw [proofFormula, checkerFormula, realize_graphAt]
  simp only [Term.realize_var, realize_numeralTerm]
  rw [program_sigma_value]
  exact eq_comm

theorem realize_builderAccepted_value {r : ℕ} (builder conclusion : Program r)
    (M : Type) [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin r → M) :
    (builderAccepted proofFormula builder conclusion).Realize x ↔
      ProofPrograms.CheckerPrograms.Certified ProofPrograms.CheckerPrograms.axiomVerifier
        (builder.value x) (conclusion.value x) := by
  rw [realize_builderAccepted]
  constructor
  · rintro ⟨p, a, hp, ha, hP⟩
    rw [program_sigma_value] at hp ha
    subst p
    subst a
    exact (realize_proofFormula_value M _ _).mp hP
  · intro h
    exact ⟨builder.value x, conclusion.value x,
      (program_sigma_value _ M _ _).mpr rfl,
      (program_sigma_value _ M _ _).mpr rfl,
      (realize_proofFormula_value M _ _).mpr h⟩

private theorem realize_box (P : language.Formula (Fin 2)) (A : language.Sentence)
    (M : Type) [language.Structure M] :
    M ⊨ provabilitySentence P A ↔ ∃ p : M,
      P.Realize ![p, numeralValue M (sentenceCode arithmeticSignature A)] := by
  rw [provabilitySentence, realize_numeralInstance, realize_provabilityFormula]

private theorem realize_computedConclusion {n : ℕ} {α : Type*}
    (P : language.Formula (Fin 2)) (code : Program n)
    (xs : Fin n → language.Term α) (p : language.Term α)
    (M : Type) [language.Structure M] (v : α → M) :
    (computedConclusion P code xs p).Realize v ↔
      ∃ a : M, code.sigmaGraph.Realize (extend (fun i => (xs i).realize v) a) ∧
        P.Realize ![p.realize v, a] := by
  simp only [computedConclusion, Formula.realize_iExs, Formula.realize_inf,
    realize_graphAt, realize_proofAt, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inr, Sum.elim_inl]
  exact ⟨fun ⟨a, ha, hp⟩ => ⟨a (), ha, hp⟩,
    fun ⟨a, ha, hp⟩ => ⟨fun _ => a, ha, hp⟩⟩

private theorem realize_constructedProof {n : ℕ} {α : Type*}
    (P : language.Formula (Fin 2)) (builder : Program n)
    (xs : Fin n → language.Term α) (a : language.Term α)
    (M : Type) [language.Structure M] (v : α → M) :
    (constructedProof P builder xs a).Realize v ↔
      ∃ p : M, builder.sigmaGraph.Realize (extend (fun i => (xs i).realize v) p) ∧
        P.Realize ![p, a.realize v] := by
  simp only [constructedProof, Formula.realize_iExs, Formula.realize_inf,
    realize_graphAt, realize_proofAt, Term.realize_var, Term.realize_relabel,
    Function.comp_def, Sum.elim_inr, Sum.elim_inl]
  exact ⟨fun ⟨p, hp, ha⟩ => ⟨p (), hp, ha⟩,
    fun ⟨p, hp, ha⟩ => ⟨fun _ => p, hp, ha⟩⟩

theorem proofFormula_sigmaOne : SigmaOne proofFormula := by
  unfold proofFormula checkerFormula graphAt
  exact checkerProgram.sigmaGraph_isSigmaOne.subst _

theorem proofPredicate_sigmaOne : SigmaOne proofPredicate := by
  exact (proofFormula_sigmaOne.relabel _).iExs

theorem box_sigmaOne (A : language.Sentence) : SigmaOneSentence (box A) := by
  exact proofPredicate_sigmaOne.subst _

theorem proofFormula_standard (p a : ℕ) :
    proofFormula.Realize ![p, a] ↔
      certificateCheck arithmeticSignature paAxiomCertificate p a = true := by
  rw [proofFormula, checkerFormula, realize_graphAt]
  simp only [Term.realize_var, realize_numeralTerm, numeral_value_nat]
  rw [checkerProgram.uniform_sigmaOne.2.1, checkerProgram, ProofPrograms.CheckerPrograms.native_checker_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

theorem box_standard (A : language.Sentence) : ℕ ⊨ box A ↔ Derives PA A := by
  rw [box, realize_box]
  simp only [numeral_value_nat, proofFormula_standard]
  exact pa_proof_checker_correct A

theorem substitutionGraph_standard {r : ℕ} (A : language.Formula (Fin r))
    (x : Fin r → ℕ) (a : ℕ) :
    (substitutionGraph A).Realize (extend x a) ↔
      a = sentenceCode arithmeticSignature (numeralInstance A x) := by
  rw [substitutionGraph, (ProofPrograms.FixedSyntaxPrograms.substitution A).uniform_sigmaOne.2.1,
    ProofPrograms.FixedSyntaxPrograms.substitution_eval]

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

theorem modus_ponens_internal : Derives PA (close modusPonensFormula) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  rw [realize_close]
  intro v
  simp only [modusPonensFormula, Formula.realize_imp, Formula.realize_inf]
  intro h
  obtain ⟨_, hb, hc, hq⟩ := h
  rw [testAt, realize_graphAt, realize_numeralTerm] at hb
  obtain ⟨a, hia, hp⟩ := (realize_computedConclusion _ _ _ _ M v).mp hc
  have hsigma {n : ℕ} (p : Program n) (x : Fin n → M) (y : M) :
      p.sigmaGraph.Realize (extend x y) ↔ y = p.value x := by
    rw [← program_sigma_model]
    exact p.value_iff x y
  have hia' : a = ProofPrograms.implication.value ![v 2, v 3] := by
    apply (hsigma _ _ _).mp
    have hx : (fun i : Fin 2 =>
        ((![Term.var 2, Term.var 3] : Fin 2 → language.Term (Fin 4)) i).realize v) = ![v 2, v 3] := by
      ext i; fin_cases i <;> rfl
    rw [hx] at hia
    exact hia
  have hp' : ProofPrograms.CheckerPrograms.Certified
      ProofPrograms.CheckerPrograms.axiomVerifier (v 0)
      (ProofPrograms.implication.value ![v 2, v 3]) := by
    rw [proofFormula, checkerFormula, realize_graphAt] at hp
    simp only [Term.realize_var, realize_numeralTerm] at hp
    have hh := (hsigma checkerProgram ![v 0, a] (numeralValue M 1)).mp hp
    exact (hia' ▸ hh).symm
  have hq' : ProofPrograms.CheckerPrograms.Certified
      ProofPrograms.CheckerPrograms.axiomVerifier (v 1) (v 2) := by
    rw [realize_proofAt, proofFormula, checkerFormula, realize_graphAt] at hq
    simp only [Term.realize_var, realize_numeralTerm] at hq
    exact ((hsigma checkerProgram ![v 1, v 2] (numeralValue M 1)).mp hq).symm
  have hb' : sentenceProgram.value ![v 3] = numeralValue M 1 := by
    have hx : (fun i : Fin 1 =>
        ((![Term.var 3] : Fin 1 → language.Term (Fin 4)) i).realize v) = ![v 3] := by
      ext i; fin_cases i; rfl
    rw [hx] at hb
    exact ((hsigma sentenceProgram ![v 3] (numeralValue M 1)).mp hb).symm
  have hout := ProofPrograms.CheckerPrograms.certified_modusPonens
    ProofPrograms.CheckerPrograms.axiomVerifier (v 0) (v 1) (v 2) (v 3) hp' hq' hb'
  apply (realize_constructedProof _ _ _ _ M v).mpr
  refine ⟨modusPonensProgram.value ![v 0, v 1, v 3], ?_, ?_⟩
  · apply (hsigma _ _ _).mpr
    congr 1
    ext i; fin_cases i <;> rfl
  · rw [proofFormula, checkerFormula, realize_graphAt]
    simp only [Term.realize_var, realize_numeralTerm]
    exact (hsigma checkerProgram _ _).mpr hout.symm

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
end Lemmatheca.MathematicalLogic.ArithmeticProofPredicates
