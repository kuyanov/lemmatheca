import Lemmatheca.PaProofCheckers.PAProofCheckerCorrectness
import Lemmatheca.PaProofCheckers.PAProofRulePrograms

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Reuse genuine finite PA proofs as constant native certificates.  Only the
fixed numerical acceptance instance is transported into an arbitrary PA model. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories FirstOrderProofs
open ArithmeticProofPredicates CodingFormalProofs
noncomputable section
universe u

private theorem fixedCertificate_exists (A : language.Sentence) (hA : Derives PA A) :
    ∃ p, CodingFormalProofs.certificateCheck arithmeticSignature paAxiomCertificate p
      (sentenceCode arithmeticSignature A) = true :=
  (pa_proof_checker_correct A).mpr hA

def fixedCertificate (A : language.Sentence) (hA : Derives PA A) : ℕ :=
  Classical.choose (fixedCertificate_exists A hA)

theorem fixedCertificate_correct (A : language.Sentence) (hA : Derives PA A) :
    CodingFormalProofs.certificateCheck arithmeticSignature paAxiomCertificate (fixedCertificate A hA)
      (sentenceCode arithmeticSignature A) = true :=
  Classical.choose_spec (fixedCertificate_exists A hA)

def fixedProof {n : ℕ} (A : language.Sentence) (hA : Derives PA A) : Program n :=
  constant (fixedCertificate A hA)

theorem fixedProof_certified {n : ℕ} (A : language.Sentence) (hA : Derives PA A)
    {M : Type u} [language.Structure M] [M ⊨ PA] (x : Fin n → M) :
    Certified axiomVerifier ((fixedProof A hA).value x)
      (numeralValue M (sentenceCode arithmeticSignature A)) := by
  rw [fixedProof, constant_value]
  unfold Certified
  have h := (certificateCheck axiomVerifier).value_numerals (M := M)
    ![fixedCertificate A hA, sentenceCode arithmeticSignature A]
  have hv : (fun i : Fin 2 => numeralValue M
      (![fixedCertificate A hA, sentenceCode arithmeticSignature A] i)) =
      ![numeralValue M (fixedCertificate A hA), numeralValue M (sentenceCode arithmeticSignature A)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, native_checker_eval] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fixedCertificate_correct,
    ↓reduceIte] at h
  exact h

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
