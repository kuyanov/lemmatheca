import Lemmatheca.EqualityFreeIntuitionisticFirstOrderCutElimination.Cut
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Public

/-! Elimination through every cutful constructor and exact native/public bridges. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifocutPropertiesFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _
variable {Γ Δ : Context L α} {A C : Formula L α}

/-- Rebuild all fifteen primitive cases and replace each actual cut. -/
def CutProof.eliminate (p : CutProof L Γ C) : CoreProof L Γ C := by
  clear Δ A
  induction p with
  | relation R ts hm => exact .relation R ts hm
  | falsumLeft hm => exact .falsumLeft hm
  | conjLeft hm _ ih => exact .conjLeft hm ih
  | conjRight _ _ ihp ihq => exact .conjRight ihp ihq
  | disjLeft hm _ _ ihp ihq => exact .disjLeft hm ihp ihq
  | disjRightLeft _ ih => exact .disjRightLeft ih
  | disjRightRight _ ih => exact .disjRightRight ih
  | implLeft hm _ _ ihp ihq => exact .implLeft hm ihp ihq
  | implRight _ ih => exact .implRight ih
  | negLeft hm _ ih => exact .negLeft hm ih
  | negRight _ ih => exact .negRight ih
  | allLeft t hm _ ih => exact .allLeft t hm ih
  | allRight _ ih => exact .allRight ih
  | exLeft hm _ ih => exact .exLeft hm ih
  | exRight t _ ih => exact .exRight t ih
  | cut hB _ _ ihp ihq => exact CoreProof.cut hB ihp ihq

def RawProof.cut (p : RawProof L Γ A) (q : RawProof L (insert A Δ) C) :
    RawProof L (Γ ∪ Δ) C := by
  refine ⟨CoreProof.cut p.conclusion_pure p.tree q.tree, ?_, q.conclusion_pure⟩
  intro B hB
  rcases Finset.mem_union.mp hB with hB | hB
  · exact p.context_pure B hB
  · exact q.context_pure B (Finset.mem_insert_of_mem hB)

def RawCutProof.eliminate (p : RawCutProof L Γ C) : RawProof L Γ C := by
  exact ⟨p.tree.eliminate, p.context_pure, p.conclusion_pure⟩

def Proof.cut (p : Proof L Γ A) (q : Proof L (insert A Δ) C) :
    Proof L (Γ ∪ Δ) C := by
  unfold Proof at p q ⊢
  rw [Finset.image_union]
  apply RawProof.cut p
  simpa only [Finset.image_insert] using q

def CutCertificate.eliminate (p : CutCertificate L Γ C) : Proof L Γ C := by
  exact RawCutProof.eliminate p

theorem raw_cutful_iff_cutFree (Γ : Context L α) (C : Formula L α) :
    Nonempty (RawCutProof L Γ C) ↔ Nonempty (RawProof L Γ C) := by
  constructor
  · rintro ⟨p⟩; exact ⟨p.eliminate⟩
  · rintro ⟨p⟩; exact ⟨p.toCut⟩

theorem cutful_iff_cutFree (Γ : Context L α) (C : Formula L α) :
    CutDerives L Γ C ↔ Derives L Γ C := by
  constructor
  · rintro ⟨p⟩; exact ⟨p.eliminate⟩
  · rintro ⟨p⟩; exact ⟨p.toCut⟩

/-- Purify the native input, translate to cutful sequents and eliminate its cuts. -/
def RawProof.fromNatural
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ C)
    (hΓ : ContextPure Γ) (hC : C.EqualityFree) : RawProof L Γ C := by
  exact (RawCutProof.fromNatural p hΓ hC).eliminate

def Proof.fromNatural
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof false false L Γ C)
    (hΓ : ContextPure Γ) (hC : C.EqualityFree) : Proof L Γ C := by
  exact (CutCertificate.fromNatural p hΓ hC).eliminate

theorem raw_native_iff_cutFree (hΓ : ContextPure Γ) (hC : C.EqualityFree) :
    Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L Γ C) ↔
      Nonempty (RawProof L Γ C) := by
  constructor
  · rintro ⟨p⟩; exact ⟨RawProof.fromNatural p hΓ hC⟩
  · rintro ⟨p⟩; exact ⟨p.toNatural⟩

theorem native_iff_cutFree (hΓ : ContextPure Γ) (hC : C.EqualityFree) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false false L Γ C ↔
      Derives L Γ C := by
  constructor
  · rintro ⟨p⟩; exact ⟨Proof.fromNatural p hΓ hC⟩
  · rintro ⟨p⟩; exact ⟨p.toNatural⟩

/-- Last-rule analysis after actual elimination excludes closed falsum. -/
theorem no_cutful_closed_falsum :
    ¬ Nonempty (CutProof L (∅ : Context L α) .falsum) := by
  rintro ⟨p⟩
  have q := p.eliminate
  cases q <;> simp_all

theorem no_public_closed_falsum : ¬ CutDerives L (∅ : Context L α) .falsum := by
  rintro ⟨p⟩
  have q := p.eliminate
  unfold Proof at q
  simp only [Finset.image_empty, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] at q
  have tree := q.tree
  cases tree <;> simp_all

theorem no_raw_native_closed_falsum :
    ¬ Nonempty (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation
      false false L (∅ : Context L α) .falsum) := by
  rintro ⟨p⟩
  have q := RawProof.fromNatural p (by intro B hB; simp at hB) True.intro
  have tree := q.tree
  cases tree <;> simp_all

theorem no_native_closed_falsum :
    ¬ Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives
      false false L (∅ : Context L α) .falsum := by
  rintro ⟨p⟩
  have q := Proof.fromNatural p (by intro B hB; simp at hB) True.intro
  unfold Proof at q
  simp only [Finset.image_empty, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_falsum] at q
  have tree := q.tree
  cases tree <;> simp_all

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
