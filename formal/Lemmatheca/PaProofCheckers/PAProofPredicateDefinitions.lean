import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesPA
import Lemmatheca.PaProofCheckers.ArithmeticProofPredicatesLogic
import Lemmatheca.PaComputations.PAProgramValues
import Lemmatheca.PaComputations.PAFormulaComplexity
import Lemmatheca.PaListsAndSyntax.PAProofPrograms
import Lemmatheca.PaListsAndSyntax.PAFixedSyntaxPrograms
import Lemmatheca.PaProofCheckers.PAProofCheckerCorrectness
import Lemmatheca.PaProofCheckers.PAProofModusPonens

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The specified actual PA checker, its arithmetic predicate and modus-ponens preservation. -/
namespace Lemmatheca.ProofTheory.ArithmeticProofPredicates
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
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

theorem program_sigma_model {n : ℕ} (p : Program n) (M : Type)
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

theorem program_sigma_comp {m n : ℕ} (f : Program m) (gs : Fin m → Program n)
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

theorem program_sigma_proj {n : ℕ} (i : Fin n) (M : Type)
    [language.Structure M] [Nonempty M] [M ⊨ PA] (x : Fin n → M) (y : M) :
    (Program.proj i).sigmaGraph.Realize (extend x y) ↔ y = x i := by
  rw [← program_sigma_model]
  simp [Program.graph, termGraph, extend]

theorem realize_builderAccepted {r : ℕ} (P : language.Formula (Fin 2))
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

theorem realize_box (P : language.Formula (Fin 2)) (A : language.Sentence)
    (M : Type) [language.Structure M] :
    M ⊨ provabilitySentence P A ↔ ∃ p : M,
      P.Realize ![p, numeralValue M (sentenceCode arithmeticSignature A)] := by
  rw [provabilitySentence, realize_numeralInstance, realize_provabilityFormula]

theorem realize_computedConclusion {n : ℕ} {α : Type*}
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

theorem realize_constructedProof {n : ℕ} {α : Type*}
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

end
end Lemmatheca.ProofTheory.ArithmeticProofPredicates
