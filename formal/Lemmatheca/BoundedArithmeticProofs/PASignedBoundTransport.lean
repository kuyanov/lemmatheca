import Lemmatheca.BoundedArithmeticProofs.PABoundedSyntaxPrograms
import Lemmatheca.BoundedArithmeticProofs.PABoundTermTransport

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Transport the bound of an actual signed bounded-quantifier certificate
from its evaluated numeral to the original closed arithmetic term. -/
namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.SignedBoundTransport
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms NumericalProofs BoundedSyntaxPrograms BoundTermTransport
noncomputable section

def transportBound {α : Type} [Fintype α] {r : ℕ} (universal negative : Bool)
    (name : α → Program r) (t : language.Term α) (D : language.Formula (α ⊕ Unit))
    (pQuant : Program r) : Program r :=
  let actual := namedTermCode name t
  let evaluated := num (namedTermValue name t)
  let normalization := ternary symmetry (namedTermBuilder name t) actual evaluated
  let hole := unary (quantifiedBoundHole universal negative) (slotFormula 1 name D)
  .comp equalitySubstitutionCertificate ![normalization, pQuant, hole, evaluated, actual]

section Internal
variable {M : Type} [language.Structure M] [M ⊨ PA]

theorem value_comp_five {r : ℕ} (p : Program 5) (a b c d e : Program r) (x : Fin r → M) :
    (Program.comp p ![a, b, c, d, e]).value x =
      p.value ![a.value x, b.value x, c.value x, d.value x, e.value x] := by
  rw [Program.value_comp]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem transportBound_model_value {α : Type} [Fintype α] {r : ℕ} (universal negative : Bool)
    (name : α → Program r) (t : language.Term α) (D : language.Formula (α ⊕ Unit))
    (pQuant : Program r) (x : Fin r → M) :
    (transportBound universal negative name t D pQuant).value x =
      equalitySubstitutionCertificate.value ![
        symmetry.value ![(namedTermBuilder name t).value x, (namedTermCode name t).value x,
          numeralSyntax ((namedTermValue name t).value x)],
        pQuant.value x,
        (quantifiedBoundHole universal negative).value ![(slotFormula 1 name D).value x],
        numeralSyntax ((namedTermValue name t).value x), (namedTermCode name t).value x] := by
  simp only [transportBound, value_comp_five, ternary_value, unary_value, num_model_value]

theorem certified_transportBound {α : Type} [Fintype α] {r : ℕ} (universal negative : Bool)
    (name : α → Program r) (t : language.Term α) (D : language.Formula (α ⊕ Unit))
    (pQuant : Program r) (x : Fin r → M)
    (hq : Certified axiomVerifier (pQuant.value x)
      (quantifiedValue universal negative ((slotFormula 0 name D).value x)
        (numeralSyntax ((namedTermValue name t).value x)))) :
    Certified axiomVerifier ((transportBound universal negative name t D pQuant).value x)
      (quantifiedValue universal negative ((slotFormula 0 name D).value x)
        ((namedTermCode name t).value x)) := by
  let actual := (namedTermCode name t).value x
  let evaluated := numeralSyntax ((namedTermValue name t).value x)
  let shifted := (slotFormula 1 name D).value x
  let normal := (slotFormula 0 name D).value x
  let hole := (quantifiedBoundHole universal negative).value ![shifted]
  have ha : PureTerm actual := namedTermCode_pure name t x
  have he : PureTerm evaluated := PureTerm.numeral _
  have hn := certified_namedTermBuilder name t x
  have hsym := certified_symmetry axiomVerifier ((namedTermBuilder name t).value x)
    actual evaluated hn ha he
  have hb : FormulaBound 2 shifted := slotFormula_bound 1 name D x
  have hnormal : FormulaBound 1 normal := slotFormula_bound 0 name D x
  have hh : FormulaBound 1 hole := quantifiedBoundHole_bound universal negative shifted hb
  have hsource : instantiate.value ![hole, evaluated] =
      quantifiedValue universal negative normal evaluated :=
    quantifiedBoundHole_instantiate universal negative shifted normal evaluated hb he
      (slotFormula_shift_rewrite name D x evaluated)
  have htarget : instantiate.value ![hole, actual] =
      quantifiedValue universal negative normal actual :=
    quantifiedBoundHole_instantiate universal negative shifted normal actual hb ha
      (slotFormula_shift_rewrite name D x actual)
  have hq' : Certified axiomVerifier (pQuant.value x) (instantiate.value ![hole, evaluated]) := by
    rw [hsource]
    exact hq
  have h := certified_equalitySubstitution axiomVerifier
    (symmetry.value ![(namedTermBuilder name t).value x, actual, evaluated])
    (pQuant.value x) hole evaluated actual hsym hq' hh.namedForm he.namedTerm ha.namedTerm
    (by rw [htarget]; exact (quantifiedValue_pure universal negative normal actual hnormal ha).sentence)
  rw [transportBound_model_value]
  simpa only [htarget] using h

end Internal
end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms.SignedBoundTransport
