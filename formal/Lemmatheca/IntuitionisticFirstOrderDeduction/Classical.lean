import Lemmatheca.IntuitionisticFirstOrderDeduction.Structural

/-! Reusable classical operations on the actual native proof certificates. -/
namespace Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {e : Bool}
noncomputable section
local instance ndClassicalFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

def Derivation.doubleNegElim {Γ : Context L α} {A : Formula L α}
    (h : Derivation true e L Γ (.neg (.neg A))) : Derivation true e L Γ A := by
  exact .classicalContradiction rfl
    (.negElim (.assumption (Finset.mem_insert_self _ _))
      (h.weaken (Finset.subset_insert _ _)))

def Derivation.excludedMiddle (Γ : Context L α) (A : Formula L α) :
    Derivation true e L Γ (.disj A (.neg A)) := by
  apply Derivation.classicalContradiction rfl
  have hnA : Derivation true e L (insert (.neg (.disj A (.neg A))) Γ) (.neg A) := by
    apply Derivation.negIntro
    exact .negElim (.disjIntroLeft (.assumption (Finset.mem_insert_self _ _)))
      (.assumption (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  exact .negElim (.disjIntroRight hnA) (.assumption (Finset.mem_insert_self _ _))

def Proof.doubleNegElim {Γ : Context L α} {A : Formula L α}
    (h : Proof true e L Γ (.neg (.neg A))) : Proof true e L Γ A := by
  exact Derivation.doubleNegElim h

def Proof.excludedMiddle (Γ : Context L α) (A : Formula L α) :
    Proof true e L Γ (.disj A (.neg A)) := by
  exact Derivation.excludedMiddle _ (A.rename Sum.inl)


end
end Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
