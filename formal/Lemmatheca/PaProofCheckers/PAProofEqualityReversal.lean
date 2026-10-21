import Lemmatheca.PaProofCheckers.PAProofNaturalDeduction
import Lemmatheca.PaListsAndSyntax.PAFixedFormulaCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

def equalityReversalRecord : Program 4 :=
  let gamma : Program 4 := .proj 0
  let d : Program 4 := .proj 1
  let s : Program 4 := .proj 2
  let t : Program 4 := .proj 3
  let body := equalCode (syntaxNode 1 [constant 0]) s
  let reflexive := syntaxNode 117 [gamma, equalCode s s, s]
  syntaxNode 118 [gamma, equalCode t s, d, reflexive, body, s, t]

def equalityReversalValue (gamma d s t : M) : M :=
  modelNode 118 [gamma, modelNode 4 [t, s], d,
    modelNode 117 [gamma, modelNode 4 [s, s], s],
    modelNode 4 [modelNode 1 [zeroValue M], s], s, t]

def transportAlongEqualityRecord : Program 6 :=
  let gamma : Program 6 := .proj 0
  let d : Program 6 := .proj 1
  let e : Program 6 := .proj 2
  let body : Program 6 := .proj 3
  let s : Program 6 := .proj 4
  let t : Program 6 := .proj 5
  let reverse := Program.comp equalityReversalRecord ![gamma, d, s, t]
  syntaxNode 118 [gamma, binary instantiate body s, reverse, e, body, t, s]

def transportAlongEqualityValue (gamma d e body s t : M) : M :=
  modelNode 118 [gamma, instantiate.value ![body, s], equalityReversalValue gamma d s t,
    e, body, t, s]

theorem equalityReversalRecord_model_value (gamma d s t : M) :
    equalityReversalRecord.value ![gamma, d, s, t] = equalityReversalValue gamma d s t := by
  simp only [equalityReversalRecord, syntaxNode_value, list_cons_value, list_nil_value,
    equalCode_value, constant_value, numeral_value_zero, Program.value_proj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, equalityReversalValue, modelNode, modelList_cons, modelList_nil]

theorem value_comp_four {r : ℕ} (p : Program 4) (a b c d : Program r) (x : Fin r → M) :
    (Program.comp p ![a, b, c, d]).value x =
      p.value ![a.value x, b.value x, c.value x, d.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem value_comp_six {r : ℕ} (p : Program 6) (a b c d e f : Program r) (x : Fin r → M) :
    (Program.comp p ![a, b, c, d, e, f]).value x =
      p.value ![a.value x, b.value x, c.value x, d.value x, e.value x, f.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem transportAlongEqualityRecord_model_value (gamma d e body s t : M) :
    transportAlongEqualityRecord.value ![gamma, d, e, body, s, t] =
      transportAlongEqualityValue gamma d e body s t := by
  simp only [transportAlongEqualityRecord, syntaxNode_value, list_cons_value, list_nil_value,
    binary_value, Program.value_proj, value_comp_four, equalityReversalRecord_model_value,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, transportAlongEqualityValue, modelNode, modelList_cons, modelList_nil]
  rfl

theorem namedTerm_of_namedBound {s : M} (hs : NamedTermBound 0 s) :
    namedTerm.value ![s] = numeralValue M 1 := by
  obtain ⟨d, av, hd, hd', hstats⟩ := hs
  have heq : d = numeralValue M 1 := le_antisymm_value hd' hd
  rw [heq] at hstats
  exact namedTerm_of_stats s av hstats

theorem namedForm_of_namedBound_zero {a : M} (ha : NamedFormulaBound 0 a) :
    namedForm.value ![zeroValue M, a] = numeralValue M 1 := by
  simpa only [numeral_value_zero] using ha.namedForm

theorem checked_equalityReversal (gamma d s t : M)
    (hd : Checked d gamma (modelNode 4 [s, t]))
    (hs : NamedTermBound 0 s) (ht : NamedTermBound 0 t)
    (hfixed : ∀ u : M, rewrite.value ![numeralValue M 2, zeroValue M, u, s] = s)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (equalityReversalValue gamma d s t) gamma (modelNode 4 [t, s]) := by
  let body := modelNode 4 [modelNode 1 [zeroValue M], s]
  have hb : namedForm.value ![numeralValue M 1, body] = numeralValue M 1 := by
    have hzero := (TermBound.bound (M := M) 1 (0 : Fin 1)).named
    simpa only [Fin.val_zero, numeral_value_zero] using
      (NamedFormulaBound.equal hzero (hs.mono (by decide))).namedForm
  have his : instantiate.value ![body, s] = modelNode 4 [s, s] := by
    rw [instantiate_value_of_tests _ _ hb (namedTerm_of_namedBound hs)]
    rw [show body = modelNode 4 [modelNode 1 [zeroValue M], s] from rfl,
      rewrite_slot_equal_value, rewrite_slot_bound_zero_value, hfixed]
  have hit : instantiate.value ![body, t] = modelNode 4 [t, s] := by
    rw [instantiate_value_of_tests _ _ hb (namedTerm_of_namedBound ht)]
    rw [show body = modelNode 4 [modelNode 1 [zeroValue M], s] from rfl,
      rewrite_slot_equal_value, rewrite_slot_bound_zero_value, hfixed]
  have hr : Checked (modelNode 117 [gamma, modelNode 4 [s, s], s]) gamma (modelNode 4 [s, s]) := by
    apply checked_native_node 117 gamma _ [s]
      (namedForm_of_namedBound_zero (NamedFormulaBound.equal hs hs)) hcontext
    exact (localRule_eqRefl_one_iff _ _ _ _).mpr ⟨namedTerm_of_namedBound hs, rfl⟩
  have hr' : Checked (modelNode 117 [gamma, modelNode 4 [s, s], s]) gamma
      (instantiate.value ![body, s]) := by rw [his]; exact hr
  have h := checked_equalitySubstitution_into d _ gamma gamma gamma body s t hd hr'
    (contextIncluded_refl_value gamma) (contextIncluded_refl_value gamma) hb
    (namedTerm_of_namedBound hs) (namedTerm_of_namedBound ht)
    (by rw [hit]; exact namedForm_of_namedBound_zero (NamedFormulaBound.equal ht hs)) hcontext
  simpa only [hit, equalityReversalValue] using h

theorem checked_transportAlongEquality (gamma delta d e body s t : M)
    (hd : Checked d gamma (modelNode 4 [s, t]))
    (he : Checked e delta (instantiate.value ![body, t]))
    (hinc : contextIncluded.value ![delta, gamma] = numeralValue M 1)
    (hs : NamedTermBound 0 s) (ht : NamedTermBound 0 t)
    (hfixed : ∀ u : M, rewrite.value ![numeralValue M 2, zeroValue M, u, s] = s)
    (hb : namedForm.value ![numeralValue M 1, body] = numeralValue M 1)
    (hout : namedForm.value ![zeroValue M, instantiate.value ![body, s] ] = numeralValue M 1)
    (hcontext : formList.value ![zeroValue M, gamma] = numeralValue M 1) :
    Checked (transportAlongEqualityValue gamma d e body s t) gamma
      (instantiate.value ![body, s]) := by
  have hrev := checked_equalityReversal gamma d s t hd hs ht hfixed hcontext
  exact checked_equalitySubstitution_into _ e gamma delta gamma body t s hrev he
    (contextIncluded_refl_value gamma) hinc hb (namedTerm_of_namedBound ht)
    (namedTerm_of_namedBound hs) hout hcontext

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
