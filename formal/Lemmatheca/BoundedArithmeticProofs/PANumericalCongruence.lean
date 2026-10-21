import Lemmatheca.BoundedArithmeticProofs.PANumericalProofCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem succFrame_value (a : M) :
    succFrame.value ![a] = modelNode 2 [numeralValue M 1, a] := by
  simp only [succFrame, succCode, syntaxNode_value, list_cons_value, list_nil_value,
    constant_value, Program.value_proj, Matrix.cons_val_zero, modelNode, modelList_cons, modelList_nil]

theorem certified_succCongruence (E : Program 2) (p a b : M)
    (hp : Certified E p (modelNode 4 [a, b])) (ha : PureTerm a) (hb : PureTerm b) :
    Certified E ((unaryCongruence succFrame).value ![p, a, b])
      (modelNode 4 [modelNode 2 [numeralValue M 1, a], modelNode 2 [numeralValue M 1, b] ]) := by
  have hfa : PureTerm (succFrame.value ![a]) := by rw [succFrame_value]; exact ha.succ
  have hfb : PureTerm (succFrame.value ![b]) := by rw [succFrame_value]; exact hb.succ
  have hbody : namedForm.value ![numeralValue M 1,
      modelNode 4 [succFrame.value ![a], succFrame.value ![modelNode 1 [zeroValue M] ] ] ] =
        numeralValue M 1 := by
    rw [succFrame_value, succFrame_value]
    have hbound := (TermBound.bound (M := M) 1 (0 : Fin 1)).succ
    simpa only [Fin.val_zero, numeral_value_zero] using
      (FormulaBound.equal (ha.succ.termBound 1) hbound).namedForm
  have hr (t : M) : rewrite.value ![numeralValue M 2, zeroValue M, t,
      succFrame.value ![modelNode 1 [zeroValue M] ] ] = succFrame.value ![t] := by
    rw [succFrame_value, succFrame_value, rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    change modelNode 2 [numeralValue M 1,
      rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [zeroValue M] ] ] = _
    rw [rewrite_slot_bound_zero_value]
  simpa only [succFrame_value] using
    certified_unaryCongruence E succFrame p a b hp ha hb hfa hfb hbody (hr a) (hr b)

def binaryFrame (f : ℕ) (left : Bool) : Program 2 :=
  if left then syntaxNode 2 [constant f, .proj 1, .proj 0]
  else syntaxNode 2 [constant f, .proj 0, .proj 1]

theorem binaryFrame_value (f : ℕ) (left : Bool) (z a : M) :
    (binaryFrame f left).value ![z, a] =
      if left then modelNode 2 [numeralValue M f, a, z]
      else modelNode 2 [numeralValue M f, z, a] := by
  cases left <;>
    simp only [binaryFrame, Bool.false_eq_true, ↓reduceIte, syntaxNode_value,
      list_cons_value, list_nil_value, constant_value, Program.value_proj,
      Matrix.cons_val_zero, Matrix.cons_val_one, modelNode, modelList_cons, modelList_nil]

theorem binaryFrame_pure (f : ℕ) (hf : f = 2 ∨ f = 3) (left : Bool)
    {z a : M} (hz : PureTerm z) (ha : PureTerm a) :
    PureTerm ((binaryFrame f left).value ![z, a]) := by
  rw [binaryFrame_value]
  cases left
  · exact PureTerm.binary f hf hz ha
  · exact PureTerm.binary f hf ha hz

theorem certified_binaryCongruence (E : Program 2) (f : ℕ) (hf : f = 2 ∨ f = 3)
    (left : Bool) (p a b z : M) (hp : Certified E p (modelNode 4 [a, b]))
    (ha : PureTerm a) (hb : PureTerm b) (hz : PureTerm z) :
    Certified E ((parametricCongruence (binaryFrame f left)).value ![p, a, b, z])
      (modelNode 4 [(binaryFrame f left).value ![z, a], (binaryFrame f left).value ![z, b] ]) := by
  have hfa := binaryFrame_pure f hf left hz ha
  have hfb := binaryFrame_pure f hf left hz hb
  have hbound : TermBound 1 ((binaryFrame f left).value ![z, modelNode 1 [zeroValue M] ]) := by
    rw [binaryFrame_value]
    have ht : TermBound 1 (modelNode 1 [zeroValue M]) := by
      simpa only [Fin.val_zero, numeral_value_zero] using TermBound.bound (M := M) 1 (0 : Fin 1)
    cases left
    · exact TermBound.binary f hf (hz.termBound 1) ht
    · exact TermBound.binary f hf ht (hz.termBound 1)
  have hbody := (FormulaBound.equal (hfa.termBound 1) hbound).namedForm
  have hr (t : M) : rewrite.value ![numeralValue M 2, zeroValue M, t,
      (binaryFrame f left).value ![z, modelNode 1 [zeroValue M] ] ] =
        (binaryFrame f left).value ![z, t] := by
    rw [binaryFrame_value, binaryFrame_value]
    cases left <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [rewrite_slot_nonleaf_value 2 (by decide) (by decide) (by decide)]
    · change modelNode 2 [numeralValue M f,
        rewrite.value ![numeralValue M 2, zeroValue M, t, z],
        rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [zeroValue M] ] ] = _
      rw [hz.2, rewrite_slot_bound_zero_value]
    · change modelNode 2 [numeralValue M f,
        rewrite.value ![numeralValue M 2, zeroValue M, t, modelNode 1 [zeroValue M] ],
        rewrite.value ![numeralValue M 2, zeroValue M, t, z] ] = _
      rw [hz.2, rewrite_slot_bound_zero_value]
  exact certified_parametricCongruence E _ p a b z hp ha hb hfa hfb hbody (hr a) (hr b)

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
