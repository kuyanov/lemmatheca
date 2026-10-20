import Lemmatheca.MathematicalLogic.PAEqualityAtomProofs
import Lemmatheca.MathematicalLogic.PANativeOrderLogic

/-! Signed certificates for actual shared arithmetic order formulas. -/
namespace Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section

def numeralOrderBuilder (negative : Bool) : Program 2 :=
  if negative then numeralNotLeBuilder else numeralLeBuilder

def orderAtom {α : Type} [Fintype α] {r : ℕ} (negative : Bool)
    (name : α → Program r) (s t : language.Term α) : Program r :=
  let a := namedTermCode name s
  let b := namedTermCode name t
  let m := num (namedTermValue name s)
  let n := num (namedTermValue name t)
  let ps := .comp symmetry ![namedTermBuilder name s, a, m]
  let pt := .comp symmetry ![namedTermBuilder name t, b, n]
  let q := binary (numeralOrderBuilder negative) (namedTermValue name s) (namedTermValue name t)
  let left := .comp (orderTransport true negative) ![ps, q, m, a, n]
  .comp (orderTransport false negative) ![pt, left, a, n, b]

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem certified_numeralOrderBuilder (negative : Bool) (m n : M)
    (h : if negative then ¬leValue M m n else leValue M m n) :
    Certified axiomVerifier ((numeralOrderBuilder negative).value ![m, n])
      (signedOrder negative (numeralSyntax m) (numeralSyntax n)) := by
  cases negative
  · exact certified_numeralLeBuilder m n h
  · exact certified_numeralNotLeBuilder m n h

theorem certified_orderAtom {α : Type} [Fintype α] {r : ℕ} (negative : Bool)
    (name : α → Program r) (s t : language.Term α) (x : Fin r → M)
    (h : if negative then
      ¬leValue M (s.realize (fun a => (name a).value x)) (t.realize (fun a => (name a).value x))
      else leValue M (s.realize (fun a => (name a).value x)) (t.realize (fun a => (name a).value x))) :
    Certified axiomVerifier ((orderAtom negative name s t).value x)
      (signedOrder negative ((namedTermCode name s).value x) ((namedTermCode name t).value x)) := by
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
  have h' : if negative then
      ¬leValue M ((namedTermValue name s).value x) ((namedTermValue name t).value x)
      else leValue M ((namedTermValue name s).value x) ((namedTermValue name t).value x) := by
    simpa only [namedTermValue_value] using h
  have hq := certified_numeralOrderBuilder negative _ _ h'
  have hleft := certified_orderTransport axiomVerifier true negative
    (symmetry.value ![(namedTermBuilder name s).value x, a, m])
    ((numeralOrderBuilder negative).value ![(namedTermValue name s).value x, (namedTermValue name t).value x])
    m a n hsi hq hm ha hn
  have hout := certified_orderTransport axiomVerifier false negative
    (symmetry.value ![(namedTermBuilder name t).value x, b, n])
    ((orderTransport true negative).value ![symmetry.value ![(namedTermBuilder name s).value x, a, m],
      (numeralOrderBuilder negative).value ![(namedTermValue name s).value x, (namedTermValue name t).value x],
      m, a, n]) a n b hti hleft ha hn hb
  simpa only [orderAtom, compFive_model_value, Program.value_comp_three,
    num_model_value, binary_value, a, b, m, n, Bool.false_eq_true, ↓reduceIte] using hout

end Internal
end
end Lemmatheca.MathematicalLogic.PAComputations.ProofPrograms.CheckerPrograms.NumericalProofs
