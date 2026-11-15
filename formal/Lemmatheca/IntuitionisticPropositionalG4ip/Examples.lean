import Lemmatheca.IntuitionisticPropositionalG4ip.Conversions

namespace Lemmatheca.Entry.IntuitionisticPropositionalG4ip
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
open Lemmatheca.ProofTheory.Intuitionistic
open G4ip
universe u
variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
theorem retained_loop [DecidableEq α] (p q : α) :
    RetainedProducer ({impl (atom p) (atom q)}, atom p)
      ({impl (atom p) (atom q)}, atom p) := by
  exact ⟨atom p, atom q, by simp, rfl⟩

def curriedExample (p q r : α) :
    Proof {atom p, atom q, impl (conj (atom p) (atom q)) (atom r)} (atom r) := by
  apply Proof.conjImplLeft (A := atom p) (B := atom q) (C := atom r) (by simp)
  apply Proof.atomImplLeft (a := p) (B := impl (atom q) (atom r))
    (by simp) (by simp [remainder])
  apply Proof.atomImplLeft (a := q) (B := atom r)
    (by simp) (by simp [remainder])
  exact .atom (by simp)

theorem curriedExample_weights (p q r : α) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    [goalWeight ({atom p, atom q, impl (conj (atom p) (atom q)) (atom r)}, atom r),
      goalWeight ({atom p, atom q, impl (atom p) (impl (atom q) (atom r))}, atom r),
      goalWeight ({atom p, atom q, impl (atom q) (atom r)}, atom r),
      goalWeight ({atom p, atom q, atom r}, atom r)] = [19, 17, 11, 8] := by
  simp [goalWeight, contextWeight, weight, hpq, hpr, hqr]

noncomputable def duplicateConclusion (A : PropFormula α) (hA : NegationFree A) :
    Proof ∅ (impl A (conj A A)) := by
  have hΓ : ReducedContext ({A} : Context α) := by
    intro X hX
    have hx : X = A := Finset.mem_singleton.mp hX
    exact hx.symm ▸ hA
  let p : Proof {A} A := Proof.identity A (by simp) hΓ
  exact .implRight (.conjRight p p)

end Lemmatheca.Entry.IntuitionisticPropositionalG4ip
