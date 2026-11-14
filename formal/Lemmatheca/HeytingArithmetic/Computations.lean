import Lemmatheca.HeytingArithmetic.Equality

namespace Lemmatheca.ProofTheory.HeytingArithmetic
noncomputable section

/-- External recursion appends only basic axiom instances and equality steps. -/
def numeralAddition (m n : ℕ) : TheoryCertificate false basic (∅ : Context Empty)
    (termEqual (addTerm (numeral m) (numeral n)) (numeral (m+n)))  := by
  induction n with
  | zero =>
    simpa only [Lemmatheca.ModelTheory.ArithmeticTheories.numeral, Nat.add_zero] using
      (TheoryCertificate.addZero (Γ := (∅ : Context Empty)) (T := basic) (fun _ h => h) (numeral m))
  | succ n ih =>
    have p := TheoryCertificate.addSucc (Γ := (∅ : Context Empty)) (T := basic)
      (fun _ h => h) (numeral m) (numeral n)
    have q := TheoryCertificate.succEquality ih
    simpa only [Lemmatheca.ModelTheory.ArithmeticTheories.numeral, Nat.add_succ] using
      TheoryCertificate.equalTransitivity p q

def numeralMultiplication (m n : ℕ) : TheoryCertificate false basic (∅ : Context Empty)
    (termEqual (mulTerm (numeral m) (numeral n)) (numeral (m*n)))  := by
  induction n with
  | zero =>
    simpa only [Lemmatheca.ModelTheory.ArithmeticTheories.numeral, Nat.mul_zero] using
      (TheoryCertificate.mulZero (Γ := (∅ : Context Empty)) (T := basic) (fun _ h => h) (numeral m))
  | succ n ih =>
    have p := TheoryCertificate.mulSucc (Γ := (∅ : Context Empty)) (T := basic)
      (fun _ h => h) (numeral m) (numeral n)
    have q := TheoryCertificate.addEquality ih
      (TheoryCertificate.equalIntro (c := false) (T := basic) (Γ := (∅ : Context Empty)) (numeral m))
    have r := numeralAddition (m*n) m
    simpa only [Lemmatheca.ModelTheory.ArithmeticTheories.numeral, Nat.mul_succ] using
      TheoryCertificate.equalTransitivity p (TheoryCertificate.equalTransitivity q r)

end
end Lemmatheca.ProofTheory.HeytingArithmetic
