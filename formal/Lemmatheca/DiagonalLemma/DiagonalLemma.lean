import Lemmatheca.DiagonalLemma.DiagonalCoding
import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Fixed points in the shared arithmetic language, using the actual numerical
syntax substitution from `DiagonalCoding`, and semantic undefinability of truth. -/
namespace Lemmatheca.ProofTheory.DiagonalLemma

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs CodingFormalProofs

noncomputable section
universe u

/-- A representative in Q of the concrete total self-substitution operation. -/
def diagonalGraph : language.Formula (Fin 1 ⊕ Unit) :=
  Classical.choose (unary_computable_representable diagonalCode diagonalCode_primrec.to_comp)

theorem diagonalGraph_represents :
    StronglyRepresents (fun x : Fin 1 → ℕ => diagonalCode (x 0)) diagonalGraph := by
  exact Classical.choose_spec
    (unary_computable_representable diagonalCode diagonalCode_primrec.to_comp)

/-- The auxiliary formula: its witness is the code of its own numeral instance. -/
def diagonalKernel (A : language.Formula Unit) : language.Formula Unit :=
  ((graphAt diagonalGraph (fun _ => .var (.inl ())) (.var (.inr ()))) ⊓
    A.relabel Sum.inr).iExs Unit

/-- The constructed sentence, not an extra symbol in the arithmetic language. -/
def fixedPoint (A : language.Formula Unit) : language.Sentence :=
  numeralSubstitution (diagonalKernel A) (unaryFormulaCode (diagonalKernel A))

/-- Substituting a numeral has the expected interpretation in every structure. -/
theorem realize_numeralSubstitution {M : Type u} [language.Structure M]
    (A : language.Formula Unit) (n : ℕ) :
    M ⊨ numeralSubstitution A n ↔ A.Realize (fun _ => numeralValue M n) := by
  have he : (default : Empty → M) = Empty.elim := Subsingleton.elim _ _
  simp only [numeralSubstitution, numeralInstance, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_subst, numeralValue, he]

/-- The kernel computes its semantic argument at every standard numeral input. -/
theorem realize_diagonalKernel {M : Type u} [language.Structure M]
    [Nonempty M] [M ⊨ Q] (A : language.Formula Unit) (n : ℕ) :
    (diagonalKernel A).Realize (fun _ => numeralValue M n) ↔
      A.Realize (fun _ => numeralValue M (diagonalCode n)) := by
  simp only [diagonalKernel, Formula.realize_iExs, Formula.realize_inf,
    realize_graphAt, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    Formula.realize_relabel, Function.comp_def]
  constructor
  · rintro ⟨y, hD, hA⟩
    have hy := (stronglyRepresents_modelwise diagonalGraph_represents
      (fun _ => n) (y ())).mp hD
    simpa only [hy] using hA
  · intro hA
    refine ⟨fun _ => numeralValue M (diagonalCode n), ?_, hA⟩
    exact (stronglyRepresents_modelwise diagonalGraph_represents (fun _ => n) _).mpr rfl

/-- The specified sentence satisfies the fixed-point equivalence in every Q model. -/
theorem fixedPoint_modelwise {M : Type u} [language.Structure M]
    [Nonempty M] [M ⊨ Q] (A : language.Formula Unit) :
    M ⊨ fixedPoint A ↔
      M ⊨ numeralSubstitution A (sentenceCode arithmeticSignature (fixedPoint A)) := by
  rw [fixedPoint, realize_numeralSubstitution, realize_diagonalKernel,
    diagonalCode_unaryFormulaCode]
  exact (realize_numeralSubstitution A _).symm

/-- The diagonal lemma is a derivation in the actual seven-axiom Robinson calculus. -/
theorem fixedPoint_equivalence (A : language.Formula Unit) :
    Derives Q ((fixedPoint A).iff
      (numeralSubstitution A (sentenceCode arithmeticSignature (fixedPoint A)))) := by
  apply HenkinCompleteness.deductive_completeness
  apply Theory.models_sentence_iff.mpr
  intro M
  exact (Sentence.realize_iff M).mpr (fixedPoint_modelwise A)

/-- The same constructed sentence works in every theory containing Q. -/
theorem fixedPoint_in_extension (A : language.Formula Unit) (T : language.Theory)
    (hT : Q ⊆ T) :
    Derives T ((fixedPoint A).iff
      (numeralSubstitution A (sentenceCode arithmeticSignature (fixedPoint A)))) := by
  exact derives_mono (fixedPoint_equivalence A) hT

/-- A candidate defines truth at every actual arithmetic sentence code. -/
def DefinesTruth (A : language.Formula Unit) : Prop :=
  ∀ σ : language.Sentence,
    A.Realize (fun _ => sentenceCode arithmeticSignature σ) ↔ ℕ ⊨ σ

/-- The internal truth schema demands a T-proof at every genuine sentence code. -/
def ProvesTruthSchema (T : language.Theory) (A : language.Formula Unit) : Prop :=
  ∀ σ : language.Sentence,
    Derives T ((numeralSubstitution A (sentenceCode arithmeticSignature σ)).iff σ)

/-- Consistency, rather than standard-model soundness, rules out the truth schema. -/
theorem truth_schema_impossible (T : language.Theory) (hT : Q ⊆ T)
    (hcon : Consistent T) (A : language.Formula Unit) : ¬ ProvesTruthSchema T A := by
  intro h
  obtain ⟨M, hM, hne, _, hmodel⟩ := HenkinCompleteness.countable_model_existence hcon
  let := hM
  let := hne
  let : M ⊨ Q := hmodel.mono hT
  let σ := fixedPoint A.not
  have hfix := fixedPoint_modelwise (M := M) A.not
  have htr : M ⊨ (numeralSubstitution A (sentenceCode arithmeticSignature σ)).iff σ :=
    derives_sound (h σ) default
      (fun B hB => hmodel.realize_of_mem B hB)
  rw [Sentence.realize_iff] at htr
  rw [realize_numeralSubstitution, Formula.realize_not] at hfix
  rw [realize_numeralSubstitution] at htr
  change (M ⊨ σ ↔ ¬ A.Realize
    (fun _ => numeralValue M (sentenceCode arithmeticSignature σ))) at hfix
  tauto

/-- Semantic truth cannot be defined by an arithmetic formula in the standard model. -/
theorem truth_undefinable (A : language.Formula Unit) : ¬ DefinesTruth A := by
  intro h
  let : ℕ ⊨ Q := nat_models_Q
  have hfix := fixedPoint_modelwise (M := ℕ) A.not
  rw [realize_numeralSubstitution, Formula.realize_not, numeral_value_nat] at hfix
  have htr := h (fixedPoint A.not)
  tauto

/-- Fixing any finite tuple of standard numerical parameters cannot define truth. -/
theorem truth_undefinable_parameters {n : ℕ}
    (A : language.Formula (Fin n ⊕ Unit)) (p : Fin n → ℕ) :
    ¬ ∀ σ : language.Sentence,
      A.Realize (extend p (sentenceCode arithmeticSignature σ)) ↔ ℕ ⊨ σ := by
  intro h
  apply truth_undefinable (specializeInputs A p)
  intro σ
  rw [realize_specializeInputs]
  simpa only [numeral_value_nat] using h σ

end
end Lemmatheca.ProofTheory.DiagonalLemma
