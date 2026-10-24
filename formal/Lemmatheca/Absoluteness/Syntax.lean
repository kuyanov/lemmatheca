import Lemmatheca.MembershipModels.Relativization

namespace Lemmatheca.SetTheory.Absoluteness
open FirstOrder FirstOrder.Language
open Lemmatheca.SetTheory.MembershipModels
universe u

/-- Set-bounded quantifiers, distinct from the shared syntax's finite scoped slots. -/
inductive DeltaZero : ℕ → Type
  | falsum {n} : DeltaZero n
  | equal {n} (i j : Fin n) : DeltaZero n
  | mem {n} (i j : Fin n) : DeltaZero n
  | imp {n} (p q : DeltaZero n) : DeltaZero n
  | ball {n} (bound : Fin n) (body : DeltaZero (n+1)) : DeltaZero n

namespace DeltaZero
def neg {n} (p : DeltaZero n) : DeltaZero n := .imp p .falsum
def conj {n} (p q : DeltaZero n) : DeltaZero n := (p.imp q.neg).neg
def disj {n} (p q : DeltaZero n) : DeltaZero n := p.neg.imp q
def bex {n} (bound : Fin n) (body : DeltaZero (n+1)) : DeltaZero n :=
  (ball bound body.neg).neg

def toShared : {n : ℕ} → DeltaZero n → membershipLanguage.BoundedFormula Empty n
  | _, .falsum => .falsum
  | _, .equal i j => .equal (.var (.inr i)) (.var (.inr j))
  | _, .mem i j => memScoped i j
  | _, .imp p q => (toShared p).imp (toShared q)
  | n, .ball j p => ((memScoped (Fin.last n) j.castSucc).imp (toShared p)).all

def Holds {M : Type u} (E : M → M → Prop) :
    {n : ℕ} → DeltaZero n → (Fin n → M) → Prop
  | _, .falsum, _ => False
  | _, .equal i j, a => a i = a j
  | _, .mem i j, a => E (a i) (a j)
  | _, .imp p q, a => Holds E p a → Holds E q a
  | _, .ball j p, a => ∀ x, E x (a j) → Holds E p (Fin.snoc a x)

theorem toShared_realize {M : Type u} (E : M → M → Prop) {n}
    (p : DeltaZero n) (a : Fin n → M) :
    letI := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
    p.toShared.Realize Empty.elim a ↔ p.Holds E a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  induction p with
  | falsum => rfl
  | equal i j => rfl
  | mem i j => rfl
  | imp p q ihp ihq =>
    simp only [DeltaZero.toShared, BoundedFormula.realize_imp, DeltaZero.Holds, ihp, ihq]
  | @ball n j p ih =>
    simp only [DeltaZero.toShared, BoundedFormula.realize_all, BoundedFormula.realize_imp,
      DeltaZero.Holds]
    have hm (b : Fin (n+1) → M) :
        (memScoped (n := n+1) (Fin.last n) j.castSucc).Realize Empty.elim b ↔
          E (b (Fin.last n)) (b j.castSucc) := by rfl
    simp only [hm, Fin.snoc_last, Fin.snoc_castSucc, ih]

theorem bex_realize {M : Type u} (E : M → M → Prop) {n}
    (j : Fin n) (p : DeltaZero (n+1)) (a : Fin n → M) :
    (bex j p).Holds E a ↔ ∃ x, E x (a j) ∧ p.Holds E (Fin.snoc a x) := by
  classical
  change (¬∀ x, E x (a j) → ¬p.Holds E (Fin.snoc a x)) ↔ _
  simp only [not_forall, not_not, exists_prop]
end DeltaZero

inductive SigmaOne : ℕ → Type
  | matrix {n} (p : DeltaZero n) : SigmaOne n
  | ex {n} (p : SigmaOne (n+1)) : SigmaOne n
inductive PiOne : ℕ → Type
  | matrix {n} (p : DeltaZero n) : PiOne n
  | all {n} (p : PiOne (n+1)) : PiOne n

def SigmaOne.toShared : {n : ℕ} → SigmaOne n → membershipLanguage.BoundedFormula Empty n
  | _, .matrix p => p.toShared
  | _, .ex p => p.toShared.ex
def PiOne.toShared : {n : ℕ} → PiOne n → membershipLanguage.BoundedFormula Empty n
  | _, .matrix p => p.toShared
  | _, .all p => p.toShared.all

def SigmaOne.neg : {n : ℕ} → SigmaOne n → PiOne n
  | _, .matrix p => .matrix p.neg
  | _, .ex p => .all p.neg
def PiOne.neg : {n : ℕ} → PiOne n → SigmaOne n
  | _, .matrix p => .matrix p.neg
  | _, .all p => .ex p.neg

def nativeSatisfies {M : Type u} (E : M → M → Prop) {n}
    (p : membershipLanguage.BoundedFormula Empty n) (a : Fin n → M) : Prop :=
  letI := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  p.Realize Empty.elim a

theorem bounded_exists_guard {M : Type u} (E : M → M → Prop) {n}
    (j : Fin n) (p : DeltaZero (n+1)) (a : Fin n → M) :
    nativeSatisfies E (DeltaZero.bex j p).toShared a ↔
      nativeSatisfies E ((memScoped (Fin.last n) j.castSucc) ⊓ p.toShared).ex a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  change (DeltaZero.bex j p).toShared.Realize Empty.elim a ↔ _
  rw [DeltaZero.toShared_realize, DeltaZero.bex_realize]
  simp only [nativeSatisfies, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  have hm (b : Fin (n+1) → M) :
      (memScoped (n := n+1) (Fin.last n) j.castSucc).Realize Empty.elim b ↔
        E (b (Fin.last n)) (b j.castSucc) := by rfl
  simp only [hm, Fin.snoc_last, Fin.snoc_castSucc, DeltaZero.toShared_realize]

theorem sigma_neg_realize {M : Type u} (E : M → M → Prop) {n}
    (p : SigmaOne n) (a : Fin n → M) :
    nativeSatisfies E p.neg.toShared a ↔ ¬ nativeSatisfies E p.toShared a := by
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  induction p with
  | matrix p => rfl
  | ex p ih =>
    simp only [SigmaOne.neg, PiOne.toShared, SigmaOne.toShared, nativeSatisfies,
      BoundedFormula.realize_all, BoundedFormula.realize_ex]
    simp only [nativeSatisfies] at ih
    simp only [ih, not_exists]

theorem pi_neg_realize {M : Type u} (E : M → M → Prop) {n}
    (p : PiOne n) (a : Fin n → M) :
    nativeSatisfies E p.neg.toShared a ↔ ¬ nativeSatisfies E p.toShared a := by
  classical
  let := Lemmatheca.MathematicalLogic.FirstOrderSemantics.binaryRelStructure M E
  induction p with
  | matrix p => rfl
  | all p ih =>
    simp only [PiOne.neg, SigmaOne.toShared, PiOne.toShared, nativeSatisfies,
      BoundedFormula.realize_all, BoundedFormula.realize_ex]
    simp only [nativeSatisfies] at ih
    simp only [ih, not_forall]

end Lemmatheca.SetTheory.Absoluteness
