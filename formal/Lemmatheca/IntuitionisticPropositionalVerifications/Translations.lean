import Lemmatheca.IntuitionisticPropositionalVerifications.Calculus

namespace Lemmatheca.ProofTheory.Intuitionistic.Verification

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula

universe u
variable {α : Type u} [DecidableEq α]

/-- Recursion on the original cut-free certificate, generalized over target environments. -/
def interpret {Δ Γ : Finset (PropFormula α)} {C : PropFormula α}
    (p : CutFree.Proof Δ C) (η : Environment Δ Γ) : Normal Γ C :=
  match p with
  | .atom h => .neutral (η h)
  | .falsumLeft h => .explode (η h)
  | .conjLeft h p => interpret p (Environment.extend (Environment.extend η (.conjRight (η h))) (.conjLeft (η h)))
  | .conjRight p q => .conjIntro (interpret p η) (interpret q η)
  | .disjLeft h p q => .cases (η h) (interpret p (η.lift _)) (interpret q (η.lift _))
  | .disjRightLeft p => .disjIntroLeft (interpret p η)
  | .disjRightRight p => .disjIntroRight (interpret p η)
  | .implLeft h p q => interpret q (η.extend (.implApply (η h) (interpret p η)))
  | .implRight p => .implIntro (interpret p (η.lift _))
  | .negLeft h p => .explode (.negApply (η h) (interpret p η))
  | .negRight p => .negIntro (interpret p (η.lift _))

def ofSequent {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : CutFree.Proof Γ A) : Normal Γ A := interpret p (Environment.identity Γ)

theorem interpret_implLeft {Δ Γ : Finset (PropFormula α)} {A B C : PropFormula α}
    (h : impl A B ∈ Δ) (p : CutFree.Proof Δ A) (q : CutFree.Proof (insert B Δ) C)
    (η : Environment Δ Γ) :
    interpret (.implLeft h p q) η = interpret q (η.extend (.implApply (η h) (interpret p η))) := by
  rfl

mutual
  def Neutral.toSequent {Γ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Neutral Γ A) : CutFree.Proof Γ A :=
    match p with
    | .assumption h => CutFree.Proof.identity _ h
    | .conjLeft p => p.toSequent.invertConj.1
    | .conjRight p => p.toSequent.invertConj.2
    | .implApply p q => (q.toSequent.cut p.toSequent.invertImpl).weaken (by simp)
    | .negApply p q => (q.toSequent.cut p.toSequent.invertNeg).weaken (by simp)
  def Normal.toSequent {Γ : Finset (PropFormula α)} {A : PropFormula α}
      (p : Normal Γ A) : CutFree.Proof Γ A :=
    match p with
    | .neutral p => p.toSequent
    | .conjIntro p q => .conjRight p.toSequent q.toSequent
    | .disjIntroLeft p => .disjRightLeft p.toSequent
    | .disjIntroRight p => .disjRightRight p.toSequent
    | .implIntro p => .implRight p.toSequent
    | .negIntro p => .negRight p.toSequent
    | .cases p q r => CutFree.reduceDisj (CutFree.Proof.replace _) (CutFree.Proof.replace _)
        p.toSequent q.toSequent r.toSequent
    | .explode p => p.toSequent.explode
end

/-- Perform the projection within each branch, retaining the original neutral disjunction. -/
def projectCases {Γ : Finset (PropFormula α)} {A B X Y : PropFormula α}
    (u : Neutral Γ (disj A B)) (p : Normal (insert A Γ) (conj X Y))
    (q : Normal (insert B Γ) (conj X Y)) : Normal Γ X :=
  .cases u (ofSequent p.toSequent.invertConj.1) (ofSequent q.toSequent.invertConj.1)

/-- The specified reconstruction eliminates supplied cuts and then interprets the result. -/
def normalOfCut {Γ : Finset (PropFormula α)} {A : PropFormula α}
    (p : CutFree.CutProof Γ A) : Normal Γ A := ofSequent p.eliminate

theorem normal_iff_natural (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Nonempty (Normal Γ A) ↔ Intuitionistic.Derives (Γ : Set (PropFormula α)) A := by
  constructor
  · rintro ⟨p⟩
    exact p.toSequent.to_natural
  · intro h
    rcases CutFree.from_natural h with ⟨p⟩
    exact ⟨ofSequent p⟩

theorem arbitrary_premises (Θ : Set (PropFormula α)) (A : PropFormula α) :
    Intuitionistic.Derives Θ A ↔
      ∃ Γ : Finset (PropFormula α), (Γ : Set (PropFormula α)) ⊆ Θ ∧ Nonempty (Normal Γ A) := by
  constructor
  · intro h
    rcases Intuitionistic.finite_support.mp h with ⟨Δ, hf, hsub, hΔ⟩
    refine ⟨hf.toFinset, ?_, (normal_iff_natural _ _).mpr ?_⟩
    · simpa only [Set.Finite.coe_toFinset] using hsub
    · simpa only [Set.Finite.coe_toFinset] using hΔ
  · rintro ⟨Γ, hΓ, h⟩
    exact ((normal_iff_natural _ _).mp h).weaken hΓ

end Lemmatheca.ProofTheory.Intuitionistic.Verification
