import Lemmatheca.MathematicalLogic.PAExistentialBuilders
import Lemmatheca.MathematicalLogic.PANumericalProofCorrectness

/-! Specialize a fixed genuine PA proof at arbitrary internally constructed
numerals. The program is a finite sequence of the actual universal-elimination
record constructors, not a program selected for agreement only on naturals. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs
noncomputable section
universe u

def specializePrefix {r : ℕ} (p : Program r) (j : ℕ) : ℕ → Program r
  | 0 => p
  | k + 1 => if hj : j < r then
      specializePrefix (specializeOne p (num (.proj ⟨j, hj⟩))) (j + 1) k else p

def specializeFixed {r : ℕ} (A : language.Formula (Fin r))
    (hA : Derives PA (close A)) : Program r :=
  specializePrefix (fixedProof (close A) hA) 0 r

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def modelAllPrefix : ℕ → M → M
  | 0, a => a
  | k + 1, a => modelAllPrefix k (modelNode 7 [a])

theorem modelAllPrefix_succ (k : ℕ) (a : M) :
    modelAllPrefix (k + 1) a = modelNode 7 [modelAllPrefix k a] := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => exact ih (modelNode 7 [a])

theorem modelFormulaCodeAt_alls {α : Type*} (name : α → M) (offset : ℕ)
    {k : ℕ} (A : language.BoundedFormula α k) :
    modelFormulaCodeAt name offset A.alls =
      modelAllPrefix k (modelFormulaCodeAt name offset A) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFormula.alls, ih]
    rfl

theorem modelAllPrefix_bound (k l : ℕ) (a : M) (ha : FormulaBound (k + l) a) :
    FormulaBound l (modelAllPrefix k a) := by
  induction k generalizing a with
  | zero => simpa only [Nat.zero_add, modelAllPrefix] using ha
  | succ k ih =>
    apply ih (modelNode 7 [a])
    apply FormulaBound.all
    simpa only [Nat.succ_add, Nat.add_succ] using ha

theorem rewrite_slot_modelAllPrefix (k : ℕ) (i t a : M) :
    rewrite.value ![numeralValue M 2, i, t, modelAllPrefix k a] =
      modelAllPrefix k (rewrite.value ![numeralValue M 2, i, t, a]) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => rw [modelAllPrefix, ih, rewrite_slot_all_value]; rfl

def universalStage {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → M) (j : ℕ) : M :=
  modelAllPrefix (r - j) (prefixMatrix
    (A.relabel (Sum.inr : Fin r → Fin 0 ⊕ Fin r)) Fin.elim0 x j)

theorem universalStage_bound {r : ℕ} (A : language.Formula (Fin r))
    (x : Fin r → M) (j : ℕ) (hj : j ≤ r) : FormulaBound 0 (universalStage A x j) := by
  apply modelAllPrefix_bound (r - j) 0
  simpa only [Nat.add_zero] using prefixMatrix_bound
    (A.relabel (Sum.inr : Fin r → Fin 0 ⊕ Fin r)) Fin.elim0 x j hj

theorem universalStage_last {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → M) :
    universalStage A x r = (substitution A).value x := by
  rw [universalStage, Nat.sub_self, modelAllPrefix, prefixMatrix_last,
    modelFormulaCodeAt_free_relabel, substitution_model_value]
  rfl

theorem close_code_model {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → M) :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature (close A)) =
      universalStage A x 0 := by
  rw [CodingFormalProofs.sentenceCode,
    ← modelFormulaCodeAt_zero_numerals (M := M) (Empty.elim : Empty → ℕ)]
  rw [close, modelFormulaCodeAt_alls, modelFormulaCodeAt_relabel]
  unfold universalStage prefixMatrix
  rw [modelFormulaCodeAt_free_relabel]
  simp only [Nat.sub_zero, Nat.zero_add]
  congr 2

theorem universalStage_step {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → M)
    (j k : ℕ) (hjk : j + (k + 1) = r) :
    ∃ b : M, universalStage A x j = modelNode 7 [b] ∧
      FormulaBound 1 b ∧
      instantiate.value ![b, ProofPrograms.numeral.value ![x ⟨j, by omega⟩] ] =
        universalStage A x (j + 1) := by
  let D := A.relabel (Sum.inr : Fin r → Fin 0 ⊕ Fin r)
  let b := modelAllPrefix k (prefixMatrix D Fin.elim0 x j)
  have hb : FormulaBound 1 b := by
    apply modelAllPrefix_bound k 1
    have hp := prefixMatrix_bound D Fin.elim0 x j (by omega)
    simpa only [show r - j = k + 1 by omega] using hp
  refine ⟨b, ?_, hb, ?_⟩
  · simp only [universalStage, show r - j = k + 1 by omega, modelAllPrefix_succ, b, D]
  · rw [instantiate_value_of_tests _ _ hb.namedForm (PureTerm.numeral _).namedTerm]
    rw [show b = modelAllPrefix k (prefixMatrix D Fin.elim0 x j) from rfl,
      rewrite_slot_modelAllPrefix, prefixMatrix_rewrite D Fin.elim0 x ⟨j, by omega⟩]
    simp only [universalStage, show r - (j + 1) = k by omega, D]

theorem certified_specializePrefix {r : ℕ} (A : language.Formula (Fin r))
    (x : Fin r → M) (p : Program r) (j k : ℕ) (hjk : j + k = r)
    (hp : Certified axiomVerifier (p.value x) (universalStage A x j)) :
    Certified axiomVerifier ((specializePrefix p j k).value x) ((substitution A).value x) := by
  induction k generalizing j p with
  | zero =>
    have hj : j = r := by omega
    subst j
    simpa only [specializePrefix, universalStage_last] using hp
  | succ k ih =>
    have hj : j < r := by omega
    obtain ⟨b, hstage, hb, hinst⟩ := universalStage_step A x j k hjk
    have hp' := hp
    rw [hstage] at hp'
    have hout : isSentence.value ![instantiate.value
        ![b, ProofPrograms.numeral.value ![x ⟨j, hj⟩] ] ] = numeralValue M 1 := by
      rw [hinst]
      exact (universalStage_bound A x (j + 1) (by omega)).pure.sentence
    have hnum : (num (Program.proj ⟨j, hj⟩)).value x =
        ProofPrograms.numeral.value ![x ⟨j, hj⟩] := by
      rw [num, unary_value, Program.value_proj]
    have hs := certified_specializeOne axiomVerifier p (num (.proj ⟨j, hj⟩)) x b hp'
      hb.namedForm (by rw [hnum]; exact (PureTerm.numeral _).namedTerm)
      (by simpa only [hnum] using hout)
    rw [hnum, hinst] at hs
    simpa only [specializePrefix, dite_eq_left hj] using ih _ _ (by omega) hs

theorem certified_specializeFixed {r : ℕ} (A : language.Formula (Fin r))
    (hA : Derives PA (close A)) (x : Fin r → M) :
    Certified axiomVerifier ((specializeFixed A hA).value x) ((substitution A).value x) := by
  apply certified_specializePrefix A x _ 0 r (by omega)
  rw [← close_code_model A x]
  exact fixedProof_certified (close A) hA x

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms
