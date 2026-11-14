import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Structural

namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u,v}} {α β : Type w}
noncomputable section
local instance ifoqTranslationFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _


private def replaceOne {Γ : Context L α} {A B : Formula L α}
    (body : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L (insert A Γ) B)
    (antecedent : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ B := by
  apply body.replace
  intro C hC
  by_cases he : C = A
  · subst C; exact antecedent
  · exact .assumption ((Finset.mem_insert.mp hC).resolve_left he)

private def replaceTwo {Γ : Context L α} {A B C : Formula L α}
    (body : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L (insert A (insert B Γ)) C)
    (left : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A)
    (right : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ B) : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ C :=
  replaceOne (replaceOne body (left.weaken (Finset.subset_insert _ _))) right

private theorem nativePureConclusion {Γ : Context L α} {A : Formula L α}
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A) (hp : p.Pure) : A.EqualityFree := by
  cases p <;> exact hp.2.1

private def cutSame {Γ : Context L α} {A B : Formula L α} (hA : A.EqualityFree)
    (producer : CutProof L Γ A) (consumer : CutProof L (insert A Γ) B) : CutProof L Γ B := by
  have out := CutProof.cut hA producer consumer
  rw [Finset.union_self] at out
  exact out

private def cutIdentity {Γ : Context L α} (A : Formula L α) (hA : A.EqualityFree)
    (hm : A ∈ Γ) : CutProof L Γ A := CutProof.ofCore (CoreProof.identity A hA hm)

variable {Γ : Context L α} {A : Formula L α}

/-- Rebuild the native proof, replacing the introduced left assumptions. -/
def CoreProof.toNatural (p : CoreProof L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A := by
  induction p with
  | relation R ts hm => exact .assumption hm
  | falsumLeft hm => exact .falsumElim (.assumption hm)
  | conjLeft hm _ ih =>
      exact replaceTwo ih (.conjElimLeft (.assumption hm)) (.conjElimRight (.assumption hm))
  | conjRight _ _ ihp ihq => exact .conjIntro ihp ihq
  | disjLeft hm _ _ ihp ihq => exact .disjElim (.assumption hm) ihp ihq
  | disjRightLeft _ ih => exact .disjIntroLeft ih
  | disjRightRight _ ih => exact .disjIntroRight ih
  | implLeft hm _ _ ihp ihq => exact replaceOne ihq (.impElim (.assumption hm) ihp)
  | implRight _ ih => exact .impIntro ih
  | negLeft hm _ ih => exact .falsumElim (.negElim ih (.assumption hm))
  | negRight _ ih => exact .negIntro ih
  | allLeft t hm _ ih => exact replaceOne ih (.allElim t (.assumption hm))
  | allRight _ ih => exact .allIntro ih
  | exLeft hm _ ih => exact .exElim (.assumption hm) ih
  | exRight t _ ih => exact .exIntro t ih

/-- Explicit cuts become the proved native composition operation. -/
def CutProof.toNatural (p : CutProof L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A := by
  induction p with
  | relation R ts hm => exact .assumption hm
  | falsumLeft hm => exact .falsumElim (.assumption hm)
  | conjLeft hm _ ih =>
      exact replaceTwo ih (.conjElimLeft (.assumption hm)) (.conjElimRight (.assumption hm))
  | conjRight _ _ ihp ihq => exact .conjIntro ihp ihq
  | disjLeft hm _ _ ihp ihq => exact .disjElim (.assumption hm) ihp ihq
  | disjRightLeft _ ih => exact .disjIntroLeft ih
  | disjRightRight _ ih => exact .disjIntroRight ih
  | implLeft hm _ _ ihp ihq => exact replaceOne ihq (.impElim (.assumption hm) ihp)
  | implRight _ ih => exact .impIntro ih
  | negLeft hm _ ih => exact .falsumElim (.negElim ih (.assumption hm))
  | negRight _ ih => exact .negIntro ih
  | allLeft t hm _ ih => exact replaceOne ih (.allElim t (.assumption hm))
  | allRight _ ih => exact .allIntro ih
  | exLeft hm _ ih => exact .exElim (.assumption hm) ih
  | exRight t _ ih => exact .exIntro t ih
  | cut _ _ _ ihp ihq => exact ihp.cut ihq

/-- Every elimination becomes a left-rule consumer followed by an explicit cut. -/
def CutProof.fromPureNatural
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A)
    (hp : p.Pure) : CutProof L Γ A := by
  revert hp
  induction p with
  | assumption hm =>
      intro hp
      exact cutIdentity _ hp.2.1 hm
  | conjIntro _ _ ihp ihq =>
      intro hp
      exact .conjRight (ihp hp.2.2.1) (ihq hp.2.2.2)
  | conjElimLeft _ ih =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2) (ih hp.2.2)
        (.conjLeft (Finset.mem_insert_self _ _) (cutIdentity _ hp.2.1 (Finset.mem_insert_self _ _)))
  | conjElimRight _ ih =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2) (ih hp.2.2)
        (.conjLeft (Finset.mem_insert_self _ _)
          (cutIdentity _ hp.2.1 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  | disjIntroLeft _ ih => intro hp; exact .disjRightLeft (ih hp.2.2)
  | disjIntroRight _ ih => intro hp; exact .disjRightRight (ih hp.2.2)
  | disjElim _ _ _ ihmajor ihleft ihright =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2.1) (ihmajor hp.2.2.1)
        (.disjLeft (Finset.mem_insert_self _ _)
          ((ihleft hp.2.2.2.1).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
          ((ihright hp.2.2.2.2).weaken (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))
  | impIntro _ ih => intro hp; exact .implRight (ih hp.2.2)
  | impElim _ _ ihmajor ihminor =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2.1) (ihmajor hp.2.2.1)
        (.implLeft (Finset.mem_insert_self _ _)
          ((ihminor hp.2.2.2).weaken (Finset.subset_insert _ _))
          (cutIdentity _ hp.2.1 (Finset.mem_insert_self _ _)))
  | negIntro _ ih => intro hp; exact .negRight (ih hp.2.2)
  | negElim _ _ ihpositive ihnegative =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2.2) (ihnegative hp.2.2.2)
        (.negLeft (Finset.mem_insert_self _ _)
          ((ihpositive hp.2.2.1).weaken (Finset.subset_insert _ _)))
  | falsumElim _ ih =>
      intro hp
      exact cutSame (A := .falsum) trivial (ih hp.2.2) (.falsumLeft (Finset.mem_insert_self _ _))
  | classicalContradiction hc _ _ => cases hc
  | allElim t _ ih =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2) (ih hp.2.2)
        (.allLeft t (Finset.mem_insert_self _ _)
          (cutIdentity _ hp.2.1 (Finset.mem_insert_self _ _)))
  | exIntro t _ ih => intro hp; exact .exRight t (ih hp.2.2)
  | allIntro _ ih => intro hp; exact .allRight (ih hp.2.2)
  | exElim _ _ ihmajor ihbranch =>
      intro hp
      exact cutSame (nativePureConclusion _ hp.2.2.1) (ihmajor hp.2.2.1)
        (.exLeft (Finset.mem_insert_self _ _)
          ((ihbranch hp.2.2.2).weaken (Finset.insert_subset_insert _
            (Finset.image_subset_image (Finset.subset_insert _ _)))))
  | equalIntro _ he => cases he
  | equalElim _ _ _ he _ _ _ _ => cases he

def RawProof.toNatural (p : RawProof L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A := p.tree.toNatural

def RawCutProof.toNatural (p : RawCutProof L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A := p.tree.toNatural

/-- Purify equality-disabled intermediate formulas before translating. -/
def RawCutProof.fromNatural
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A)
    (hΓ : ContextPure Γ) (hA : A.EqualityFree) : RawCutProof L Γ A := by
  let pureInput := p.purify hΓ hA
  exact ⟨CutProof.fromPureNatural pureInput.1 pureInput.2, hΓ, hA⟩

theorem raw_native_iff_cutful (hΓ : ContextPure Γ) (hA : A.EqualityFree) :
    Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ A) ↔
      Nonempty (RawCutProof L Γ A) := by
  constructor
  · rintro ⟨p⟩; exact ⟨RawCutProof.fromNatural p hΓ hA⟩
  · rintro ⟨p⟩; exact ⟨p.toNatural⟩

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
