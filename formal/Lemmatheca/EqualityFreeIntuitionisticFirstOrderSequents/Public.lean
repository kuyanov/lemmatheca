import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Translation

namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderProofs
universe u v w
variable {L : Language.{u,v}} {α β : Type w}
noncomputable section
local instance ifoqPublicFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

private def reserveSubst (σ : α → L.Term β) : α ⊕ ℕ → L.Term (β ⊕ ℕ) :=
  Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i))

private theorem reserveFormula (A : Formula L α) (σ : α → L.Term β) :
    (A.rename (Sum.inl : α → α ⊕ ℕ)).subst (reserveSubst σ) =
      (A.subst σ).rename Sum.inl := by
  simp only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_rename_subst,
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_subst_rename,
    reserveSubst, Sum.elim_inl]

private theorem reserveContext (Γ : Context L α) (σ : α → L.Term β) :
    (Γ.image (fun A => A.rename (Sum.inl : α → α ⊕ ℕ))).image
      (fun A => A.subst (reserveSubst σ)) =
    (Γ.image (fun A => A.subst σ)).image (fun A => A.rename Sum.inl) := by
  simp only [Finset.image_image, Function.comp_def, reserveFormula]

private theorem pureImage {δ : Type w} {Γ : Context L α} (h : ContextPure Γ)
    (f : α → δ) : ContextPure (Γ.image (fun A => A.rename f)) := by
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨A, hA, rfl⟩
  exact (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).2 (h A hA)

private def reindexRaw {δ : Type w} {Γ Δ : Context L δ} {A B : Formula L δ}
    (hΓ : Γ = Δ) (hA : A = B) (p : RawProof L Γ A) : RawProof L Δ B :=
  hΓ ▸ hA ▸ p

private theorem reindexRaw_height {δ : Type w} {Γ Δ : Context L δ} {A B : Formula L δ}
    (hΓ : Γ = Δ) (hA : A = B) (p : RawProof L Γ A) :
    (reindexRaw hΓ hA p).tree.height = p.tree.height := by
  subst Δ
  subst B
  rfl

private def reindexCut {δ : Type w} {Γ Δ : Context L δ} {A B : Formula L δ}
    (hΓ : Γ = Δ) (hA : A = B) (p : RawCutProof L Γ A) : RawCutProof L Δ B :=
  hΓ ▸ hA ▸ p

private theorem reindexCut_height {δ : Type w} {Γ Δ : Context L δ} {A B : Formula L δ}
    (hΓ : Γ = Δ) (hA : A = B) (p : RawCutProof L Γ A) :
    (reindexCut hΓ hA p).tree.height = p.tree.height := by
  subst Δ
  subst B
  rfl

namespace Proof
variable {Γ Δ : Context L α} {A : Formula L α}

def weaken (p : Proof L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) : Proof L Δ A := by
  exact RawProof.weaken p (Finset.image_subset_image h) (pureImage hΔ Sum.inl)

theorem weaken_height (p : Proof L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) :
    (p.weaken h hΔ).tree.height = p.tree.height := by
  exact RawProof.weaken_height p (Finset.image_subset_image h) (pureImage hΔ Sum.inl)

def substitute (p : Proof L Γ A) (σ : α → L.Term β) :
    Proof L (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  exact reindexRaw (reserveContext Γ σ) (reserveFormula A σ)
    (RawProof.substitute p (reserveSubst σ))

theorem substitute_height (p : Proof L Γ A) (σ : α → L.Term β) :
    (p.substitute σ).tree.height = p.tree.height := by
  simpa only [substitute, reindexRaw_height] using
    RawProof.substitute_height p (reserveSubst σ)

def rename (p : Proof L Γ A) (f : α → β) :
    Proof L (Γ.image (fun B => B.rename f)) (A.rename f) := by
  exact substitute p (fun x => .var (f x))

theorem rename_height (p : Proof L Γ A) (f : α → β) :
    (p.rename f).tree.height = p.tree.height := by
  exact substitute_height p (fun x => .var (f x))

def toNatural (p : Proof L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof false false L Γ A := by
  exact RawProof.toNatural p

def identity (A : Formula L α) (hΓ : ContextPure Γ) (hA : A.EqualityFree)
    (hmem : A ∈ Γ) : Proof L Γ A := by
  exact RawProof.identity (A.rename Sum.inl) (pureImage hΓ Sum.inl)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).2 hA)
    (Finset.mem_image.mpr ⟨A, hmem, rfl⟩)

def explode (p : Proof L Γ .falsum) (A : Formula L α) (hA : A.EqualityFree) :
    Proof L Γ A := by
  exact RawProof.explode p (A.rename Sum.inl)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).2 hA)

def toCut (p : Proof L Γ A) : CutCertificate L Γ A := by
  exact RawProof.toCut p

end Proof

namespace CutCertificate
variable {Γ Δ : Context L α} {A : Formula L α}

def weaken (p : CutCertificate L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) : CutCertificate L Δ A := by
  exact RawCutProof.weaken p (Finset.image_subset_image h) (pureImage hΔ Sum.inl)

theorem weaken_height (p : CutCertificate L Γ A) (h : Γ ⊆ Δ) (hΔ : ContextPure Δ) :
    (p.weaken h hΔ).tree.height = p.tree.height := by
  exact RawCutProof.weaken_height p (Finset.image_subset_image h) (pureImage hΔ Sum.inl)

def substitute (p : CutCertificate L Γ A) (σ : α → L.Term β) :
    CutCertificate L (Γ.image (fun B => B.subst σ)) (A.subst σ) := by
  exact reindexCut (reserveContext Γ σ) (reserveFormula A σ)
    (RawCutProof.substitute p (reserveSubst σ))

theorem substitute_height (p : CutCertificate L Γ A) (σ : α → L.Term β) :
    (p.substitute σ).tree.height = p.tree.height := by
  simpa only [substitute, reindexCut_height] using
    RawCutProof.substitute_height p (reserveSubst σ)

def rename (p : CutCertificate L Γ A) (f : α → β) :
    CutCertificate L (Γ.image (fun B => B.rename f)) (A.rename f) := by
  exact substitute p (fun x => .var (f x))

theorem rename_height (p : CutCertificate L Γ A) (f : α → β) :
    (p.rename f).tree.height = p.tree.height := by
  exact substitute_height p (fun x => .var (f x))

def toNatural (p : CutCertificate L Γ A) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof false false L Γ A := by
  exact RawCutProof.toNatural p

def fromNatural
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof false false L Γ A)
    (hΓ : ContextPure Γ) (hA : A.EqualityFree) : CutCertificate L Γ A := by
  exact RawCutProof.fromNatural p (pureImage hΓ Sum.inl)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map A _).2 hA)

end CutCertificate

variable {Γ : Context L α} {A : Formula L α}

theorem native_iff_cutful (hΓ : ContextPure Γ) (hA : A.EqualityFree) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false false L Γ A ↔
      CutDerives L Γ A := by
  constructor
  · rintro ⟨p⟩
    exact ⟨CutCertificate.fromNatural p hΓ hA⟩
  · rintro ⟨p⟩
    exact ⟨CutCertificate.toNatural p⟩

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder
