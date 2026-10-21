import Lemmatheca.BoundedArithmeticProofs.PANumericalCongruence
import Lemmatheca.PaListsAndSyntax.PAModelSyntaxCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
variable {M : Type} [language.Structure M] [M ⊨ PA]

def zeroSyntax : M := modelNode 2 [zeroValue M]
def successorSyntax (a : M) : M := modelNode 2 [numeralValue M 1, a]
def additionSyntax (a b : M) : M := modelNode 2 [numeralValue M 2, a, b]
def multiplicationSyntax (a b : M) : M := modelNode 2 [numeralValue M 3, a, b]
def boundSyntax (n : ℕ) : M := modelNode 1 [numeralValue M n]
def numeralSyntax (n : M) : M := ProofPrograms.numeral.value ![n]

theorem close_one_code (A : language.Formula (Fin 1)) :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature (close A)) =
      modelNode 7 [modelFormulaCodeAt (fun _ : Fin 1 => boundSyntax (M := M) 0) 1 A] := by
  rw [CodingFormalProofs.sentenceCode,
    ← modelFormulaCodeAt_zero_numerals (M := M) (Empty.elim : Empty → ℕ)]
  change modelNode 7 [modelFormulaCodeAt _ 0
    (BoundedFormula.relabel (fun i => (Sum.inr i : Empty ⊕ Fin 1)) A)] = _
  rw [modelFormulaCodeAt_relabel]
  apply congrArg (fun name => modelNode 7 [modelFormulaCodeAt name 1 A])
  funext i
  simp only [Sum.elim_inr, Nat.zero_add, Fin.val_eq_zero i, boundSyntax]

theorem close_two_code (A : language.Formula (Fin 2)) :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature (close A)) =
      modelNode 7 [modelNode 7 [modelFormulaCodeAt (boundSyntax (M := M) ∘ Fin.val) 2 A] ] := by
  rw [CodingFormalProofs.sentenceCode,
    ← modelFormulaCodeAt_zero_numerals (M := M) (Empty.elim : Empty → ℕ)]
  change modelNode 7 [modelNode 7 [modelFormulaCodeAt _ 0
    (BoundedFormula.relabel (fun i => (Sum.inr i : Empty ⊕ Fin 2)) A)] ] = _
  rw [modelFormulaCodeAt_relabel]
  simp only [Sum.elim_inr, Nat.zero_add]
  rfl

theorem qAddZero_code_value :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature qAddZero) =
      modelNode 7 [modelNode 4 [additionSyntax (boundSyntax 0) zeroSyntax, boundSyntax 0] ] := by
  rw [qAddZero, close_one_code]
  change modelNode 7 [modelNode 4 [additionSyntax (boundSyntax 0)
    (modelNode 2 [numeralValue M 0]), boundSyntax 0] ] = _
  rw [numeral_value_zero]
  rfl

theorem qMulZero_code_value :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature qMulZero) =
      modelNode 7 [modelNode 4 [multiplicationSyntax (boundSyntax 0) zeroSyntax, zeroSyntax] ] := by
  rw [qMulZero, close_one_code]
  change modelNode 7 [modelNode 4 [multiplicationSyntax (boundSyntax 0)
    (modelNode 2 [numeralValue M 0]), modelNode 2 [numeralValue M 0] ] ] = _
  rw [numeral_value_zero]
  rfl

theorem qAddSucc_code_value :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature qAddSucc) =
      modelNode 7 [modelNode 7 [modelNode 4
        [additionSyntax (boundSyntax 0) (successorSyntax (boundSyntax 1)),
          successorSyntax (additionSyntax (boundSyntax 0) (boundSyntax 1))] ] ] := by
  rw [qAddSucc, close_two_code]
  rfl

theorem qMulSucc_code_value :
    numeralValue M (CodingFormalProofs.sentenceCode CodingFormalProofs.arithmeticSignature qMulSucc) =
      modelNode 7 [modelNode 7 [modelNode 4
        [multiplicationSyntax (boundSyntax 0) (successorSyntax (boundSyntax 1)),
          additionSyntax (multiplicationSyntax (boundSyntax 0) (boundSyntax 1)) (boundSyntax 0)] ] ] := by
  rw [qMulSucc, close_two_code]
  rfl

theorem boundSyntax_zero : boundSyntax (M := M) 0 = modelNode 1 [zeroValue M] := by
  rw [boundSyntax, numeral_value_zero]

theorem zeroSyntax_pure : PureTerm (zeroSyntax (M := M)) := PureTerm.zero

theorem zeroCode_model_value {r : ℕ} (x : Fin r → M) : zeroCode.value x = zeroSyntax := by
  simp only [zeroCode, syntaxNode_value, list_cons_value, list_nil_value, constant_value,
    numeral_value_zero, zeroSyntax, modelNode, modelList_cons, modelList_nil]

theorem num_model_value {r : ℕ} (a : Program r) (x : Fin r → M) :
    (num a).value x = numeralSyntax (a.value x) := unary_value _ _ _

theorem succCode_model_value {r : ℕ} (a : Program r) (x : Fin r → M) :
    (succCode a).value x = successorSyntax (a.value x) := by
  simp only [succCode, syntaxNode_value, list_cons_value, list_nil_value, constant_value,
    successorSyntax, modelNode, modelList_cons, modelList_nil]

theorem addCode_model_value {r : ℕ} (a b : Program r) (x : Fin r → M) :
    (addCode a b).value x = additionSyntax (a.value x) (b.value x) := by
  simp only [addCode, syntaxNode_value, list_cons_value, list_nil_value, constant_value,
    additionSyntax, modelNode, modelList_cons, modelList_nil]

theorem mulCode_model_value {r : ℕ} (a b : Program r) (x : Fin r → M) :
    (mulCode a b).value x = multiplicationSyntax (a.value x) (b.value x) := by
  simp only [mulCode, syntaxNode_value, list_cons_value, list_nil_value, constant_value,
    multiplicationSyntax, modelNode, modelList_cons, modelList_nil]

def instanceOne {r : ℕ} (A : language.Formula (Fin 1)) (hA : Derives PA (close A))
    (t : Program r) : Program r := specializeOne (fixedProof (close A) hA) t

theorem certified_instanceOne {r : ℕ} (A : language.Formula (Fin 1))
    (hA : Derives PA (close A)) (t : Program r) (x : Fin r → M)
    (ht : PureTerm (t.value x)) :
    Certified axiomVerifier ((instanceOne A hA t).value x)
      (modelFormulaCodeAt (fun _ : Fin 1 => t.value x) 0 A) := by
  let name : Fin 1 → M := fun _ => boundSyntax 0
  let body := modelFormulaCodeAt name 1 A
  have hname (i : Fin 1) : TermBound 1 (name i) := by
    simpa only [name, boundSyntax, Fin.val_zero] using TermBound.bound (M := M) 1 (0 : Fin 1)
  have hbody := (modelFormulaCodeAt_bound name 1 hname A).namedForm
  have hrew : rewrite.value ![numeralValue M 2, zeroValue M, t.value x, body] =
      modelFormulaCodeAt (fun _ : Fin 1 => t.value x) 0 A := by
    rw [rewrite_slot_modelFormulaCodeAt name _ _ 0 A]
    congr 1
    funext i
    change rewrite.value ![numeralValue M 2, zeroValue M, t.value x, boundSyntax 0] = t.value x
    rw [boundSyntax_zero, rewrite_slot_bound_zero_value]
  have hinst : instantiate.value ![body, t.value x] =
      modelFormulaCodeAt (fun _ : Fin 1 => t.value x) 0 A := by
    rw [instantiate_value_of_tests _ _ hbody ht.namedTerm, hrew]
  have hout : isSentence.value ![instantiate.value ![body, t.value x] ] = numeralValue M 1 := by
    rw [hinst]
    exact (modelFormulaCodeAt_bound (fun _ : Fin 1 => t.value x) 0
      (fun _ => ht.termBound 0) A).pure.sentence
  have hp := fixedProof_certified (close A) hA (M := M) x
  rw [close_one_code] at hp
  have h := certified_specializeOne axiomVerifier (fixedProof (close A) hA) t x body hp
    hbody ht.namedTerm hout
  simpa only [instanceOne, hinst] using h

def instanceTwo {r : ℕ} (A : language.Formula (Fin 2)) (hA : Derives PA (close A))
    (s t : Program r) : Program r :=
  specializeOne (specializeOne (fixedProof (close A) hA) s) t

theorem certified_instanceTwo {r : ℕ} (A : language.Formula (Fin 2))
    (hA : Derives PA (close A)) (s t : Program r) (x : Fin r → M)
    (hs : PureTerm (s.value x)) (ht : PureTerm (t.value x)) :
    Certified axiomVerifier ((instanceTwo A hA s t).value x)
      (modelFormulaCodeAt (fun i : Fin 2 => ![s.value x, t.value x] i) 0 A) := by
  let name : Fin 2 → M := boundSyntax ∘ Fin.val
  let name1 : Fin 2 → M := ![s.value x, boundSyntax 0]
  let name2 : Fin 2 → M := ![s.value x, t.value x]
  let body := modelFormulaCodeAt name 2 A
  let body1 := modelFormulaCodeAt name1 1 A
  let body2 := modelFormulaCodeAt name2 0 A
  have hn (i : Fin 2) : TermBound 2 (name i) := TermBound.bound 2 i
  have hn1 (i : Fin 2) : TermBound 1 (name1 i) := by
    fin_cases i
    · exact hs.termBound 1
    · exact TermBound.bound 1 (0 : Fin 1)
  have hfb := modelFormulaCodeAt_bound name 2 hn A
  have hfb1 := modelFormulaCodeAt_bound name1 1 hn1 A
  have hrew1 : rewrite.value ![numeralValue M 2, zeroValue M, s.value x, body] = body1 := by
    rw [rewrite_slot_modelFormulaCodeAt name _ _ 1 A]
    apply congrArg (fun name => modelFormulaCodeAt name 1 A)
    funext i
    fin_cases i
    · change rewrite.value ![numeralValue M 2, zeroValue M, s.value x, boundSyntax 0] = s.value x
      rw [boundSyntax_zero, rewrite_slot_bound_zero_value]
    · change rewrite.value ![numeralValue M 2, zeroValue M, s.value x, boundSyntax 1] = boundSyntax 0
      have h1 : numeralValue M 1 = succValue M (zeroValue M) := by
        rw [numeral_value_succ, numeral_value_zero]
      change rewrite.value ![numeralValue M 2, zeroValue M, s.value x,
        modelNode 1 [numeralValue M 1] ] = boundSyntax 0
      rw [h1, rewrite_slot_bound_successor_value]
      rw [boundSyntax_zero]
  have hrew2 : rewrite.value ![numeralValue M 2, zeroValue M, t.value x, body1] = body2 := by
    rw [rewrite_slot_modelFormulaCodeAt name1 _ _ 0 A]
    apply congrArg (fun name => modelFormulaCodeAt name 0 A)
    funext i
    fin_cases i
    · exact hs.2 _ _
    · change rewrite.value ![numeralValue M 2, zeroValue M, t.value x, boundSyntax 0] = t.value x
      rw [boundSyntax_zero, rewrite_slot_bound_zero_value]
  have hbody1 : namedForm.value ![numeralValue M 1, modelNode 7 [body] ] = numeralValue M 1 :=
    hfb.all.namedForm
  have hbody2 : namedForm.value ![numeralValue M 1, body1] = numeralValue M 1 := hfb1.namedForm
  have hinst1 : instantiate.value ![modelNode 7 [body], s.value x] = modelNode 7 [body1] := by
    rw [instantiate_value_of_tests _ _ hbody1 hs.namedTerm, rewrite_slot_all_value, hrew1]
  have hinst2 : instantiate.value ![body1, t.value x] = body2 := by
    rw [instantiate_value_of_tests _ _ hbody2 ht.namedTerm, hrew2]
  have hout1 : isSentence.value ![instantiate.value ![modelNode 7 [body], s.value x] ] = numeralValue M 1 := by
    rw [hinst1]
    exact hfb1.all.pure.sentence
  have hout2 : isSentence.value ![instantiate.value ![body1, t.value x] ] = numeralValue M 1 := by
    rw [hinst2]
    have hn2 : ∀ i : Fin 2, TermBound 0 (name2 i) := by
      intro i
      fin_cases i
      · exact hs.termBound 0
      · exact ht.termBound 0
    exact (modelFormulaCodeAt_bound name2 0 hn2 A).pure.sentence
  have hp := fixedProof_certified (close A) hA (M := M) x
  rw [close_two_code] at hp
  have hp1 := certified_specializeOne axiomVerifier (fixedProof (close A) hA) s x
    (modelNode 7 [body]) hp hbody1 hs.namedTerm hout1
  rw [hinst1] at hp1
  have hp2 := certified_specializeOne axiomVerifier (specializeOne (fixedProof (close A) hA) s) t x
    body1 hp1 hbody2 ht.namedTerm hout2
  simpa only [instanceTwo, hinst2] using hp2

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
