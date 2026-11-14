import Lemmatheca.EqualityFreeFirstOrderSignedFormulaDeductions.Normalization

/-! The same supplied-tree operations on the existing countable reserve. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w} {e : Bool}
noncomputable section
local instance signedPublicFormulaEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

namespace Public
variable {Γ : Context L α}

def toPositive (F : Formula L α) (h : F.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ F) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (positive F h) := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p ⊢
  have q :=
    (Raw.toPositive (F.rename Sum.inl)
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h) p)
  change Derivation true e L _ (reading _ _ true) at q
  rw [reading_rename F h (Sum.inl : α → α ⊕ ℕ) true] at q
  exact q

def fromPositive (F : Formula L α) (h : F.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (positive F h)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ F := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p ⊢
  apply Raw.fromPositive (F.rename Sum.inl)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h)
  change Derivation true e L _ (reading _ _ true)
  rw [reading_rename F h (Sum.inl : α → α ⊕ ℕ) true]
  exact p

def toNegative (F : Formula L α) (h : F.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (.neg F)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (negative F h) := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p ⊢
  have q :=
    (Raw.toNegative (F.rename Sum.inl)
      ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h) p)
  change Derivation true e L _ (reading _ _ false) at q
  rw [reading_rename F h (Sum.inl : α → α ⊕ ℕ) false] at q
  exact q

def fromNegative (F : Formula L α) (h : F.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (negative F h)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (.neg F) := by
  unfold Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof at p ⊢
  apply Raw.fromNegative (F.rename Sum.inl)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h)
  change Derivation true e L _ (reading _ _ false)
  rw [reading_rename F h (Sum.inl : α → α ⊕ ℕ) false]
  exact p

def negToDual (A : Nnf L α 0)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (.neg A.read)) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ A.dual.read := by
  have q := toNegative A.read A.read_equalityFree p
  simpa only [negative, reading_negative_read] using q

def dualToNeg (A : Nnf L α 0)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ A.dual.read) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof true e L Γ (.neg A.read) := by
  apply fromNegative A.read A.read_equalityFree
  simpa only [negative, reading_negative_read] using p

end Public

theorem public_positive_iff (Γ : Context L α) (F : Formula L α) (h : F.EqualityFree) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true e L Γ F ↔
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true e L Γ (positive F h) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨Public.toPositive F h p⟩
  · rintro ⟨p⟩
    exact ⟨Public.fromPositive F h p⟩

theorem public_negative_iff (Γ : Context L α) (F : Formula L α) (h : F.EqualityFree) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true e L Γ (.neg F) ↔
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives true e L Γ (negative F h) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨Public.toNegative F h p⟩
  · rintro ⟨p⟩
    exact ⟨Public.fromNegative F h p⟩

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
