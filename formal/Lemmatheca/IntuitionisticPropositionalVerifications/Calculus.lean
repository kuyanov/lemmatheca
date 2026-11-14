import Lemmatheca.IntuitionisticPropositionalCutElimination.Subformulas

namespace Lemmatheca.ProofTheory.Intuitionistic.Verification

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

mutual
  /-- Elimination spines whose head is an actual available assumption. -/
  inductive Neutral : Finset (PropFormula α) → PropFormula α → Type u
    | assumption {Γ A} : A ∈ Γ → Neutral Γ A
    | conjLeft {Γ A B} : Neutral Γ (conj A B) → Neutral Γ A
    | conjRight {Γ A B} : Neutral Γ (conj A B) → Neutral Γ B
    | implApply {Γ A B} : Neutral Γ (impl A B) → Normal Γ A → Neutral Γ B
    | negApply {Γ A} : Neutral Γ (neg A) → Normal Γ A → Neutral Γ falsum
  /-- Verifications with neutral major premises for case and explosion rules. -/
  inductive Normal : Finset (PropFormula α) → PropFormula α → Type u
    | neutral {Γ A} : Neutral Γ A → Normal Γ A
    | conjIntro {Γ A B} : Normal Γ A → Normal Γ B → Normal Γ (conj A B)
    | disjIntroLeft {Γ A B} : Normal Γ A → Normal Γ (disj A B)
    | disjIntroRight {Γ A B} : Normal Γ B → Normal Γ (disj A B)
    | implIntro {Γ A B} : Normal (insert A Γ) B → Normal Γ (impl A B)
    | negIntro {Γ A} : Normal (insert A Γ) falsum → Normal Γ (neg A)
    | cases {Γ A B C} : Neutral Γ (disj A B) → Normal (insert A Γ) C →
        Normal (insert B Γ) C → Normal Γ C
    | explode {Γ C} : Neutral Γ falsum → Normal Γ C
end

mutual
  def Neutral.weaken {Γ Δ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Neutral Γ A) (h : Γ ⊆ Δ) : Neutral Δ A :=
    match p with
    | .assumption hA => .assumption (h hA)
    | .conjLeft p => .conjLeft (p.weaken h)
    | .conjRight p => .conjRight (p.weaken h)
    | .implApply p q => .implApply (p.weaken h) (q.weaken h)
    | .negApply p q => .negApply (p.weaken h) (q.weaken h)
  def Normal.weaken {Γ Δ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Normal Γ A) (h : Γ ⊆ Δ) : Normal Δ A :=
    match p with
    | .neutral p => .neutral (p.weaken h)
    | .conjIntro p q => .conjIntro (p.weaken h) (q.weaken h)
    | .disjIntroLeft p => .disjIntroLeft (p.weaken h)
    | .disjIntroRight p => .disjIntroRight (p.weaken h)
    | .implIntro p => .implIntro (p.weaken (Finset.insert_subset_insert _ h))
    | .negIntro p => .negIntro (p.weaken (Finset.insert_subset_insert _ h))
    | .cases p q r => .cases (p.weaken h)
        (q.weaken (Finset.insert_subset_insert _ h))
        (r.weaken (Finset.insert_subset_insert _ h))
    | .explode p => .explode (p.weaken h)
end

/-- Source assumptions are assigned neutral certificates in the target context. -/
def Environment (Δ Γ : Finset (PropFormula α)) :=
  ∀ {D}, D ∈ Δ → Neutral Γ D

def Environment.identity (Γ : Finset (PropFormula α)) : Environment Γ Γ :=
  fun h => .assumption h

/-- Extend the requested assumptions by one specified neutral certificate. -/
def Environment.extend {Δ Γ : Finset (PropFormula α)} (η : Environment Δ Γ)
    {A : PropFormula α} (p : Neutral Γ A) : Environment (insert A Δ) Γ :=
  fun {D} h => if he : D = A then he ▸ p else η ((Finset.mem_insert.mp h).resolve_left he)

/-- A temporary source assumption is supplied by the same temporary target assumption. -/
def Environment.lift {Δ Γ : Finset (PropFormula α)} (η : Environment Δ Γ)
    (A : PropFormula α) : Environment (insert A Δ) (insert A Γ) :=
  Environment.extend (fun {_} h => (η h).weaken (Finset.subset_insert _ _))
    (.assumption (by simp))

end Lemmatheca.ProofTheory.Intuitionistic.Verification
