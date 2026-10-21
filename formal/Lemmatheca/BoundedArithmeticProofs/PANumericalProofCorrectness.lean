import Lemmatheca.PaProofCheckers.PAProofSpecializationCorrectness
import Lemmatheca.BoundedArithmeticProofs.PANumericalProofPrograms
import Lemmatheca.PaListsAndSyntax.PAModelSyntax
import Lemmatheca.PaProofCheckers.PAProofReflexivity
import Lemmatheca.PaListsAndSyntax.PAFixedFormulaCorrectness

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u
variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem instantiate_equal_hole {a t : M} (ha : PureTerm a) (ht : PureTerm t)
    (hb : namedForm.value ![numeralValue M 1, modelNode 4 [a, modelNode 1 [zeroValue M] ] ] =
      numeralValue M 1) :
    instantiate.value ![modelNode 4 [a, modelNode 1 [zeroValue M] ], t] = modelNode 4 [a, t] := by
  rw [instantiate_value_of_tests _ _ hb ht.namedTerm,
    rewrite_slot_equal_value, ha.2, rewrite_slot_bound_zero_value]

theorem transitivity_model_value (p q a b c : M) :
    transitivity.value ![p, q, a, b, c] = equalitySubstitutionCertificate.value
      ![q, p, modelNode 4 [a, modelNode 1 [zeroValue M] ], b, c] := by
  rw [transitivity, Program.value_comp]
  congr 1
  funext i
  fin_cases i <;>
    simp [Program.value_proj, equalCode_value, boundZero, syntaxNode_value,
      list_cons_value, list_nil_value, constant_value, numeral_value_zero,
      modelNode, modelList_cons, modelList_nil]

theorem certified_transitivity (E : Program 2) (p q a b c : M)
    (hp : Certified E p (modelNode 4 [a, b]))
    (hq : Certified E q (modelNode 4 [b, c]))
    (ha : PureTerm a) (hb : PureTerm b) (hc : PureTerm c) :
    Certified E (transitivity.value ![p, q, a, b, c]) (modelNode 4 [a, c]) := by
  have hbody : namedForm.value ![numeralValue M 1,
      modelNode 4 [a, modelNode 1 [zeroValue M] ] ] = numeralValue M 1 := by
    simpa only [Fin.val_zero, numeral_value_zero] using
      (FormulaBound.equal (ha.termBound 1) (TermBound.bound 1 (0 : Fin 1))).namedForm
  rw [transitivity_model_value]
  have hbs := instantiate_equal_hole ha hb hbody
  have hct := instantiate_equal_hole ha hc hbody
  have hout : isSentence.value ![instantiate.value
      ![modelNode 4 [a, modelNode 1 [zeroValue M] ], c] ] = numeralValue M 1 := by
    rw [hct]
    exact ha.equal_sentence hc
  have hp' : Certified E p (instantiate.value
      ![modelNode 4 [a, modelNode 1 [zeroValue M] ], b]) := hbs.symm ▸ hp
  have h := certified_equalitySubstitution E q p
    (modelNode 4 [a, modelNode 1 [zeroValue M] ]) b c hq hp'
    hbody hb.namedTerm hc.namedTerm hout
  simpa only [hct] using h

theorem certified_frameCongruence (E : Program 2) (frame : M → M)
    (p a b : M) (hp : Certified E p (modelNode 4 [a, b]))
    (ha : PureTerm a) (hb : PureTerm b)
    (hfa : PureTerm (frame a)) (hfb : PureTerm (frame b))
    (hbody : namedForm.value ![numeralValue M 1,
      modelNode 4 [frame a, frame (modelNode 1 [zeroValue M]) ] ] = numeralValue M 1)
    (hra : rewrite.value ![numeralValue M 2, zeroValue M, a,
      frame (modelNode 1 [zeroValue M])] = frame a)
    (hrb : rewrite.value ![numeralValue M 2, zeroValue M, b,
      frame (modelNode 1 [zeroValue M])] = frame b) :
    Certified E (equalitySubstitutionCertificate.value
      ![p, equalityReflexivityCertificate.value ![frame a],
        modelNode 4 [frame a, frame (modelNode 1 [zeroValue M])], a, b])
      (modelNode 4 [frame a, frame b]) := by
  let body := modelNode 4 [frame a, frame (modelNode 1 [zeroValue M])]
  have hinst (t : M) (ht : PureTerm t)
      (hrt : rewrite.value ![numeralValue M 2, zeroValue M, t,
        frame (modelNode 1 [zeroValue M])] = frame t) :
      instantiate.value ![body, t] = modelNode 4 [frame a, frame t] := by
    rw [instantiate_value_of_tests _ _ hbody ht.namedTerm]
    rw [rewrite_slot_equal_value, hfa.2, hrt]
  have hia := hinst a ha hra
  have hib := hinst b hb hrb
  have hq := certified_equalityReflexivity E (frame a) hfa.namedTerm (hfa.equal_sentence hfa)
  have hq' : Certified E (equalityReflexivityCertificate.value ![frame a])
      (instantiate.value ![body, a]) := hia.symm ▸ hq
  have hout : isSentence.value ![instantiate.value ![body, b] ] = numeralValue M 1 := by
    rw [hib]
    exact hfa.equal_sentence hfb
  have h := certified_equalitySubstitution E p
    (equalityReflexivityCertificate.value ![frame a]) body a b hp hq'
    hbody ha.namedTerm hb.namedTerm hout
  simpa only [hib] using h

theorem certified_unaryCongruence (E : Program 2) (frame : Program 1)
    (p a b : M) (hp : Certified E p (modelNode 4 [a, b]))
    (ha : PureTerm a) (hb : PureTerm b)
    (hfa : PureTerm (frame.value ![a])) (hfb : PureTerm (frame.value ![b]))
    (hbody : namedForm.value ![numeralValue M 1,
      modelNode 4 [frame.value ![a], frame.value ![modelNode 1 [zeroValue M] ] ] ] = numeralValue M 1)
    (hra : rewrite.value ![numeralValue M 2, zeroValue M, a,
      frame.value ![modelNode 1 [zeroValue M] ] ] = frame.value ![a])
    (hrb : rewrite.value ![numeralValue M 2, zeroValue M, b,
      frame.value ![modelNode 1 [zeroValue M] ] ] = frame.value ![b]) :
    Certified E ((unaryCongruence frame).value ![p, a, b])
      (modelNode 4 [frame.value ![a], frame.value ![b] ]) := by
  let body := modelNode 4 [frame.value ![a], frame.value ![modelNode 1 [zeroValue M] ] ]
  have hv : (unaryCongruence frame).value ![p, a, b] =
      equalitySubstitutionCertificate.value
        ![p, equalityReflexivityCertificate.value ![frame.value ![a] ], body, a, b] := by
    rw [unaryCongruence, Program.value_comp]
    congr 1
    funext i
    fin_cases i <;>
      simp [Program.value_proj, unary_value, equalCode_value, boundZero, syntaxNode_value,
        list_cons_value, list_nil_value, constant_value, numeral_value_zero,
        body, modelNode, modelList_cons, modelList_nil]
  rw [hv]
  exact certified_frameCongruence E (fun a => frame.value ![a]) p a b hp ha hb
    hfa hfb hbody hra hrb

theorem certified_parametricCongruence (E : Program 2) (frame : Program 2)
    (p a b z : M) (hp : Certified E p (modelNode 4 [a, b]))
    (ha : PureTerm a) (hb : PureTerm b)
    (hfa : PureTerm (frame.value ![z, a])) (hfb : PureTerm (frame.value ![z, b]))
    (hbody : namedForm.value ![numeralValue M 1,
      modelNode 4 [frame.value ![z, a], frame.value ![z, modelNode 1 [zeroValue M] ] ] ] = numeralValue M 1)
    (hra : rewrite.value ![numeralValue M 2, zeroValue M, a,
      frame.value ![z, modelNode 1 [zeroValue M] ] ] = frame.value ![z, a])
    (hrb : rewrite.value ![numeralValue M 2, zeroValue M, b,
      frame.value ![z, modelNode 1 [zeroValue M] ] ] = frame.value ![z, b]) :
    Certified E ((parametricCongruence frame).value ![p, a, b, z])
      (modelNode 4 [frame.value ![z, a], frame.value ![z, b] ]) := by
  let body := modelNode 4 [frame.value ![z, a], frame.value ![z, modelNode 1 [zeroValue M] ] ]
  have hv : (parametricCongruence frame).value ![p, a, b, z] =
      equalitySubstitutionCertificate.value
        ![p, equalityReflexivityCertificate.value ![frame.value ![z, a] ], body, a, b] := by
    rw [parametricCongruence, Program.value_comp]
    congr 1
    funext i
    fin_cases i <;>
      simp [Program.value_proj, unary_value, binary_value, equalCode_value, boundZero,
        syntaxNode_value, list_cons_value, list_nil_value, constant_value, numeral_value_zero,
        body, modelNode, modelList_cons, modelList_nil]
  rw [hv]
  exact certified_frameCongruence E (fun a => frame.value ![z, a]) p a b hp ha hb
    hfa hfb hbody hra hrb

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
