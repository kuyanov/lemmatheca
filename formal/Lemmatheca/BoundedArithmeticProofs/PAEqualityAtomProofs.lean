import Lemmatheca.BoundedArithmeticProofs.PANumeralComparisonProofs
import Lemmatheca.BoundedArithmeticProofs.PABoundedTruthPrograms

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section

def namedTermCode {α : Type} {r : ℕ} (name : α → Program r) (t : language.Term α) : Program r :=
  termCode (fun a => num (name a)) t

def namedTermValue {α : Type} [Fintype α] {r : ℕ} (name : α → Program r) (t : language.Term α) : Program r :=
  BoundedTruthPrograms.termValueNamed name t

def namedTermBuilder {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (t : language.Term α) : Program r :=
  let e := Fintype.equivFin α
  .comp (termBuilder (t.relabel e)) (fun i => name (e.symm i))

def positiveEquality {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (s t : language.Term α) : Program r :=
  composeEquality (namedTermBuilder name s)
    (.comp symmetry ![namedTermBuilder name t, namedTermCode name t, num (namedTermValue name t)])
    (namedTermCode name s) (num (namedTermValue name s)) (namedTermCode name t)

def negativeEquality {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (s t : language.Term α) : Program r :=
  let a := namedTermCode name s
  let b := namedTermCode name t
  let m := num (namedTermValue name s)
  let n := num (namedTermValue name t)
  let ps := .comp symmetry ![namedTermBuilder name s, a, m]
  let pt := .comp symmetry ![namedTermBuilder name t, b, n]
  let q := binary numeralNotEqualBuilder (namedTermValue name s) (namedTermValue name t)
  let left := .comp notEqualLeftTransport ![ps, q, m, a, n]
  .comp notEqualRightTransport ![pt, left, a, n, b]

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem namedTermCode_value {α : Type} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → M) :
    (namedTermCode name t).value x = modelTermCode (fun a => numeralSyntax ((name a).value x)) t := by
  rw [namedTermCode, termCode_model_value]
  apply congrArg (fun name => modelTermCode name t)
  funext a
  exact num_model_value _ _

theorem namedTermValue_value {α : Type} [Fintype α] {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → M) :
    (namedTermValue name t).value x = t.realize (fun a => (name a).value x) :=
  BoundedTruthPrograms.termValueNamed_value name t x

theorem namedTermCode_pure {α : Type} {r : ℕ} (name : α → Program r)
    (t : language.Term α) (x : Fin r → M) : PureTerm ((namedTermCode name t).value x) :=
  termCode_pure (fun a => num (name a)) (fun _ _ => num_pure _ _) t x

theorem certified_namedTermBuilder {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (t : language.Term α) (x : Fin r → M) :
    Certified axiomVerifier ((namedTermBuilder name t).value x)
      (modelNode 4 [(namedTermCode name t).value x,
        numeralSyntax ((namedTermValue name t).value x)]) := by
  let e := Fintype.equivFin α
  let v : Fin (Fintype.card α) → M := fun i => (name (e.symm i)).value x
  have h := certified_termBuilder (t.relabel e) v
  rw [termEquationCode_model_value, termInstance_model_value, termValue_value,
    modelTermCode_relabel, Term.realize_relabel] at h
  have hv : (fun i => numeralSyntax (v i)) ∘ e =
      (fun a => numeralSyntax ((name a).value x)) := by
    funext a
    simp only [Function.comp_apply, v, Equiv.symm_apply_apply]
  have hv' : v ∘ e = fun a => (name a).value x := by
    funext a
    simp only [Function.comp_apply, v, Equiv.symm_apply_apply]
  rw [hv, hv'] at h
  rw [namedTermBuilder, Program.value_comp, namedTermCode_value, namedTermValue_value]
  exact h

theorem certified_positiveEquality {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (s t : language.Term α) (x : Fin r → M)
    (heq : s.realize (fun a => (name a).value x) = t.realize (fun a => (name a).value x)) :
    Certified axiomVerifier ((positiveEquality name s t).value x)
      (modelNode 4 [(namedTermCode name s).value x, (namedTermCode name t).value x]) := by
  let a := (namedTermCode name s).value x
  let b := (namedTermCode name t).value x
  let m := numeralSyntax ((namedTermValue name s).value x)
  let n := numeralSyntax ((namedTermValue name t).value x)
  have ha := namedTermCode_pure name s x
  have hb := namedTermCode_pure name t x
  have hm : PureTerm m := PureTerm.numeral _
  have hn : PureTerm n := PureTerm.numeral _
  have hmn : m = n := by rw [show m = numeralSyntax ((namedTermValue name s).value x) from rfl,
    show n = numeralSyntax ((namedTermValue name t).value x) from rfl,
    namedTermValue_value, namedTermValue_value, heq]
  have hs := certified_namedTermBuilder name s x
  have ht := certified_namedTermBuilder name t x
  have hsym := certified_symmetry axiomVerifier ((namedTermBuilder name t).value x) b n ht hb hn
  have hsym' : Certified axiomVerifier
      (symmetry.value ![(namedTermBuilder name t).value x, b, n]) (modelNode 4 [m, b]) := by
    simpa only [hmn] using hsym
  have h := certified_transitivity axiomVerifier ((namedTermBuilder name s).value x)
    (symmetry.value ![(namedTermBuilder name t).value x, b, n]) a m b hs hsym' ha hm hb
  simpa only [positiveEquality, composeEquality_model_value, Program.value_comp_three,
    num_model_value, a, b, m, n] using h

theorem compFive_model_value {r : ℕ} (p : Program 5)
    (a b c d e : Program r) (x : Fin r → M) :
    (Program.comp p ![a, b, c, d, e]).value x =
      p.value ![a.value x, b.value x, c.value x, d.value x, e.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> simp

theorem certified_negativeEquality {α : Type} [Fintype α] {r : ℕ}
    (name : α → Program r) (s t : language.Term α) (x : Fin r → M)
    (hne : s.realize (fun a => (name a).value x) ≠ t.realize (fun a => (name a).value x)) :
    Certified axiomVerifier ((negativeEquality name s t).value x)
      (negValue (modelNode 4 [(namedTermCode name s).value x, (namedTermCode name t).value x])) := by
  let a := (namedTermCode name s).value x
  let b := (namedTermCode name t).value x
  let m := numeralSyntax ((namedTermValue name s).value x)
  let n := numeralSyntax ((namedTermValue name t).value x)
  have ha := namedTermCode_pure name s x
  have hb := namedTermCode_pure name t x
  have hm : PureTerm m := PureTerm.numeral _
  have hn : PureTerm n := PureTerm.numeral _
  have hs := certified_namedTermBuilder name s x
  have ht := certified_namedTermBuilder name t x
  have hsi := certified_symmetry axiomVerifier ((namedTermBuilder name s).value x) a m hs ha hm
  have hti := certified_symmetry axiomVerifier ((namedTermBuilder name t).value x) b n ht hb hn
  have hne' : (namedTermValue name s).value x ≠ (namedTermValue name t).value x := by
    simpa only [namedTermValue_value] using hne
  have hq := certified_numeralNotEqualBuilder _ _ hne'
  have hleft := certified_notEqualLeftTransport axiomVerifier
    (symmetry.value ![(namedTermBuilder name s).value x, a, m])
    (numeralNotEqualBuilder.value ![(namedTermValue name s).value x, (namedTermValue name t).value x])
    m a n hsi hq hm ha hn
  have h := certified_notEqualRightTransport axiomVerifier
    (symmetry.value ![(namedTermBuilder name t).value x, b, n])
    (notEqualLeftTransport.value ![symmetry.value ![(namedTermBuilder name s).value x, a, m],
      numeralNotEqualBuilder.value ![(namedTermValue name s).value x, (namedTermValue name t).value x],
      m, a, n]) a n b hti hleft ha hn hb
  simpa only [negativeEquality, compFive_model_value, Program.value_comp_three,
    num_model_value, binary_value, a, b, m, n] using h

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
