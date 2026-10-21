import Lemmatheca.PaProofCheckers.PAProofNaturalDeduction

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! A fixed natural-deduction scheme used by the finite initial-segment
compiler. Its inputs are checked proofs of a→(b∨c) and b→d. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms
noncomputable section
universe u

def finiteCasesRecord : Program 7 :=
  let gamma : Program 7 := .proj 0
  let a : Program 7 := .proj 1
  let b : Program 7 := .proj 2
  let c : Program 7 := .proj 3
  let d : Program 7 := .proj 4
  let s : Program 7 := .proj 5
  let r : Program 7 := .proj 6
  let out := orCode d c
  let ext := binary listCons a gamma
  let left := binary listCons b ext
  let right := binary listCons c ext
  let ass := syntaxNode 100 [ext, a]
  let dichotomy := syntaxNode 108 [ext, orCode b c, s, ass]
  let pass := syntaxNode 100 [left, b]
  let pd := syntaxNode 108 [left, d, r, pass]
  let dl := syntaxNode 104 [left, out, pd, c]
  let dass := syntaxNode 100 [right, c]
  let dr := syntaxNode 105 [right, out, dass, d]
  let cases := syntaxNode 106 [ext, out, dichotomy, dl, dr, b, c]
  syntaxNode 107 [gamma, impCode a out, cases, a]

section Internal
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def finiteCasesValue (gamma a b c d s r : M) : M :=
  let out := orValue d c
  let ext := listCons.value ![a, gamma]
  let left := listCons.value ![b, ext]
  let right := listCons.value ![c, ext]
  let ass := modelNode 100 [ext, a]
  let dichotomy := modelNode 108 [ext, orValue b c, s, ass]
  let pass := modelNode 100 [left, b]
  let pd := modelNode 108 [left, d, r, pass]
  let dl := modelNode 104 [left, out, pd, c]
  let dass := modelNode 100 [right, c]
  let dr := modelNode 105 [right, out, dass, d]
  let cases := modelNode 106 [ext, out, dichotomy, dl, dr, b, c]
  modelNode 107 [gamma, implication.value ![a, out], cases, a]

theorem finiteCasesRecord_model_value (gamma a b c d s r : M) :
    finiteCasesRecord.value ![gamma, a, b, c, d, s, r] =
      finiteCasesValue gamma a b c d s r := by
  simp only [finiteCasesRecord, syntaxNode_value, list_cons_value, list_nil_value,
    binary_value, Program.value_proj, orCode_value, impCode,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, finiteCasesValue, modelNode, modelList_cons, modelList_nil]
  rfl

theorem listMember_cons_one_iff (a b gamma : M) :
    listMember.value ![a, listCons.value ![b, gamma] ] = numeralValue M 1 ↔
      a = b ∨ listMember.value ![a, gamma] = numeralValue M 1 := by
  rw [listMember_cons_value]
  split_ifs with h
  · simp only [h, true_or]
  · simp only [h, false_or]

theorem formList_cons_one_iff (n a gamma : M) :
    formList.value ![n, listCons.value ![a, gamma] ] = numeralValue M 1 ↔
      namedForm.value ![zeroValue M, a] = numeralValue M 1 ∧
      formList.value ![n, gamma] = numeralValue M 1 := by
  have h := listAll_cons_one_iff (binary namedForm (constant 0) (.proj 1)) n a gamma
  simpa only [formList, binary_value, constant_value, numeral_value_zero,
    Program.value_proj, Matrix.cons_val_one, Matrix.cons_val_zero] using h

theorem contextIncluded_under_cons (gamma a : M) :
    contextIncluded.value ![gamma, listCons.value ![a, gamma] ] = numeralValue M 1 := by
  apply contextIncluded_of_members
  intro x hx
  rw [listMember_cons_one_iff]
  exact Or.inr hx

theorem checked_finiteCases (gamma a b c d s r : M)
    (hs : Checked s gamma (implication.value ![a, orValue b c]))
    (hr : Checked r gamma (implication.value ![b, d]))
    (ha : namedForm.value ![zeroValue M, a] = numeralValue M 1)
    (hb : namedForm.value ![zeroValue M, b] = numeralValue M 1)
    (hc : namedForm.value ![zeroValue M, c] = numeralValue M 1)
    (hd : namedForm.value ![zeroValue M, d] = numeralValue M 1)
    (hbc : namedForm.value ![zeroValue M, orValue b c] = numeralValue M 1)
    (hdc : namedForm.value ![zeroValue M, orValue d c] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, implication.value ![a, orValue d c] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (finiteCasesValue gamma a b c d s r) gamma
      (implication.value ![a, orValue d c]) := by
  let ext := listCons.value ![a, gamma]
  let left := listCons.value ![b, ext]
  let right := listCons.value ![c, ext]
  have hext : formList.value ![zeroValue M, ext] = numeralValue M 1 := by
    exact (formList_cons_one_iff _ _ _).mpr ⟨ha, hcontext⟩
  have hleft : formList.value ![zeroValue M, left] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨hb, hext⟩
  have hright : formList.value ![zeroValue M, right] = numeralValue M 1 :=
    (formList_cons_one_iff _ _ _).mpr ⟨hc, hext⟩
  have hass := checked_assumption ext a ha hext
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hsplit := checked_modusPonens_into s (modelNode 100 [ext, a]) gamma ext ext
    a (orValue b c) hs hass (contextIncluded_under_cons gamma a)
      (contextIncluded_refl_value ext) hbc hext
  have hpass := checked_assumption left b hb hleft
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hincl : contextIncluded.value ![gamma, left] = numeralValue M 1 :=
    contextIncluded_trans_value gamma ext left (contextIncluded_under_cons gamma a)
      (contextIncluded_under_cons ext b)
  have hpd := checked_modusPonens_into r (modelNode 100 [left, b]) gamma left left
    b d hr hpass hincl (contextIncluded_refl_value left) hd hleft
  have hdl := checked_orLeft _ left d c hpd hc hdc hleft
  have hrass := checked_assumption right c hc hright
    ((listMember_cons_one_iff _ _ _).mpr (Or.inl rfl))
  have hdr := checked_orRight _ right d c hrass hd hdc hright
  have hcases := checked_orElim _ _ _ ext (orValue d c) b c
    hsplit hdl hdr hb hc hdc hext
  exact checked_impIntro _ gamma a (orValue d c) hcases ha hout hcontext

/-- Merge two accepted axiom lists without asking the verifier any new
question. The new proof may use either old context. -/
theorem certified_merge_contexts (E : Program 2) (p q a b d c : M)
    (hp : Certified E p a) (hq : Certified E q b)
    (hd : Checked d (listAppend.value
      ![contextValue (rootValue p), contextValue (rootValue q)]) c)
    (hc : isSentence.value ![c] = numeralValue M 1) :
    Certified E (modelList [d, listAppend.value ![witnessesValue p, witnessesValue q] ]) c :=
  certified_merge_roots E p q a b d c hp hq hd hc

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
