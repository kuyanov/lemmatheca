import Lemmatheca.EqualityFreeFirstOrderSignedFormulaDeductions.Scope

/-! Derived native connective and quantified conversion rules. No new native
proof constructors are introduced. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {c e : Bool}
noncomputable section
local instance signedConversionsFormulaEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

private def hypothesis {Γ : Context L α} (A : Formula L α) :
    Derivation c e L (insert A Γ) A := .assumption (Finset.mem_insert_self _ _)

private def under {Γ : Context L α} {A : Formula L α}
    (p : Derivation c e L Γ A) (B : Formula L α) : Derivation c e L (insert B Γ) A :=
  p.weaken (Finset.subset_insert _ _)

private theorem instantiate_lifted (B : BF L α 1) :
    (B.rename (Sum.inl : α → α ⊕ Fin 1)).instantiate (.var (.inr 0)) = B.toFormula := by
  unfold Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiateSlots Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toFormula
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr i =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl

private def openAll {Γ : Context L α} {B : BF L α 1}
    (p : Derivation c e L Γ (.all B)) :
    Derivation c e L (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ) B.toFormula := by
  have hp := p.rename (Sum.inl : α → α ⊕ Fin 1)
  have hi := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.allElim
    (classical := c) (equality := e) (Γ := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext Γ)
    (B := B.rename (Sum.inl : α → α ⊕ Fin 1)) (.var (.inr 0))
    (by simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.liftContext,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
      Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all] using hp)
  simpa only [instantiate_lifted] using hi

private def closeEx {Γ : Context L (α ⊕ Fin 1)} {B : BF L α 1}
    (p : Derivation c e L Γ B.toFormula) :
    Derivation c e L Γ ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.ex B).rename Sum.inl) := by
  have hx := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.exIntro
    (classical := c) (equality := e) (Γ := Γ) (B := B.rename (Sum.inl : α → α ⊕ Fin 1)) (.var (.inr 0)) (by simpa only [instantiate_lifted] using p)
  simpa only [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using hx

/-- The reverse conjunction De Morgan conversion uses no classical rule. -/
def negConjReverse (A B : Formula L α) :
    Convert c e (.disj (.neg A) (.neg B)) (.neg (.conj A B)) := by
  intro Γ p
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.disjElim (under p (.conj A B))
  · exact .negElim (.conjElimLeft (under (hypothesis (.conj A B)) (.neg A)))
      (hypothesis (.neg A))
  · exact .negElim (.conjElimRight (under (hypothesis (.conj A B)) (.neg B)))
      (hypothesis (.neg B))

/-- A negative witness contradicts a universal formula in either deduction mode. -/
def negAllReverse (B : BF L α 1) :
    Convert c e (.ex (.neg B)) (.neg (.all B)) := by
  intro Γ p
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.exElim (under p (.all B))
  exact .negElim (under (openAll (hypothesis (.all B))) (.neg B.toFormula))
    (hypothesis (.neg B.toFormula))

namespace Bridge
variable {A B C D : Formula L α}

def conj (p : Bridge c e A C) (q : Bridge c e B D) :
    Bridge c e (.conj A B) (.conj C D) where
  forward h := .conjIntro (p.forward (.conjElimLeft h)) (q.forward (.conjElimRight h))
  backward h := .conjIntro (p.backward (.conjElimLeft h)) (q.backward (.conjElimRight h))

def disj (p : Bridge c e A C) (q : Bridge c e B D) :
    Bridge c e (.disj A B) (.disj C D) where
  forward h := .disjElim h (.disjIntroLeft (p.forward (hypothesis A)))
    (.disjIntroRight (q.forward (hypothesis B)))
  backward h := .disjElim h (.disjIntroLeft (p.backward (hypothesis C)))
    (.disjIntroRight (q.backward (hypothesis D)))

def negConj (A B : Formula L α) :
    Bridge true e (.neg (.conj A B)) (.disj (.neg A) (.neg B)) where
  forward {Γ} h := by
    apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.disjElim (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.excludedMiddle Γ A)
    · apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.disjIntroRight
      apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
      exact .negElim (.conjIntro (under (hypothesis A) B) (hypothesis B))
        (under (under h A) B)
    · exact .disjIntroLeft (hypothesis (.neg A))
  backward := negConjReverse A B

def negDisj (A B : Formula L α) :
    Bridge c e (.neg (.disj A B)) (.conj (.neg A) (.neg B)) where
  forward h := .conjIntro
    (.negIntro (.negElim (.disjIntroLeft (hypothesis A)) (under h A)))
    (.negIntro (.negElim (.disjIntroRight (hypothesis B)) (under h B)))
  backward h := .negIntro (.disjElim (hypothesis (.disj A B))
    (.negElim (hypothesis A) (.conjElimLeft (under (under h (.disj A B)) A)))
    (.negElim (hypothesis B) (.conjElimRight (under (under h (.disj A B)) B))))

def implication (A B : Formula L α) :
    Bridge true e (.impl A B) (.disj (.neg A) B) where
  forward {Γ} h := .disjElim (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.excludedMiddle Γ A)
    (.disjIntroRight (.impElim (under h A) (hypothesis A)))
    (.disjIntroLeft (hypothesis (.neg A)))
  backward h := .impIntro (.disjElim (under h A)
    (.falsumElim (.negElim (under (hypothesis A) (.neg A)) (hypothesis (.neg A))))
    (hypothesis B))

def negImplication (A B : Formula L α) :
    Bridge true e (.neg (.impl A B)) (.conj A (.neg B)) where
  forward h := by
    have hA := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.doubleNegElim (A := A) (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
      (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negElim
        (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.impIntro (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.falsumElim
          (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negElim (hypothesis A) (under (hypothesis (.neg A)) A))))
        (under h (.neg A))))
    have hnB := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negElim
      (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.impIntro (under (hypothesis B) A)) (under h B))
    exact .conjIntro hA hnB
  backward h := .negIntro (.negElim
    (.impElim (hypothesis (.impl A B)) (.conjElimLeft (under h (.impl A B))))
    (.conjElimRight (under h (.impl A B))))

def all {B C : BF L α 1} (p : Bridge c e B.toFormula C.toFormula) :
    Bridge c e (.all B) (.all C) where
  forward h := .allIntro (p.forward (openAll h))
  backward h := .allIntro (p.backward (openAll h))

def ex {B C : BF L α 1} (p : Bridge c e B.toFormula C.toFormula) :
    Bridge c e (.ex B) (.ex C) where
  forward h := .exElim h (closeEx (p.forward (hypothesis B.toFormula)))
  backward h := .exElim h (closeEx (p.backward (hypothesis C.toFormula)))

def negEx (B : BF L α 1) :
    Bridge c e (.neg (.ex B)) (.all (.neg B)) where
  forward h := by
    apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.allIntro
    apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
    exact .negElim (closeEx (hypothesis B.toFormula))
      (under (h.rename (Sum.inl : α → α ⊕ Fin 1)) B.toFormula)
  backward h := by
    apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
    apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.exElim (hypothesis (.ex B))
    exact .negElim (hypothesis B.toFormula)
      (under (openAll (under h (.ex B))) B.toFormula)

def negAll (B : BF L α 1) :
    Bridge true e (.neg (.all B)) (.ex (.neg B)) where
  forward {Γ} h := by
    apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.classicalContradiction rfl
    have hn := (negEx (c := true) (e := e) (.neg B)).forward
      (hypothesis (Γ := Γ) (.neg (.ex (.neg B))))
    let p : Bridge true e (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.neg (.neg B)).toFormula B.toFormula :=
      ⟨fun d => Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.doubleNegElim d,
       fun d => doubleNegIntro d⟩
    exact .negElim ((all p).forward hn) (under h (.neg (.ex (.neg B))))
  backward := negAllReverse B

end Bridge
end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
