import Lemmatheca.EqualityFreeFirstOrderSequents.Operations
import Lemmatheca.IntuitionisticFirstOrderDeduction.Classical

/-! Full readings of the specified signed normalizations, and actual maps between
native deduction certificates in a fixed ambient context. -/
namespace Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
open _root_.FirstOrder _root_.FirstOrder.Language
abbrev BF := Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula
abbrev Context := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Context
abbrev Derivation := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation
universe u v w w'
variable {L : Language.{u,v}} {α : Type w} {β : Type w'}

/-- The actual full reading of the positive or negative signed normalization. -/
def reading {n} (F : BF L α n) (h : F.EqualityFree) (b : Bool) : BF L α n :=
  (Nnf.normalize F h b).read

def positive {n} (F : BF L α n) (h : F.EqualityFree) : BF L α n := reading F h true

def negative {n} (F : BF L α n) (h : F.EqualityFree) : BF L α n := reading F h false

/-- A context-uniform actual transformation of supplied raw trees. -/
abbrev Convert (c e : Bool) (A B : Formula L α) : Type max u v (w+1) :=
  ∀ {Γ : Context L α}, Derivation c e L Γ A → Derivation c e L Γ B

/-- Two conversions of conclusions, both retaining the same ambient context. -/
structure Bridge (c e : Bool) (A B : Formula L α) where
  forward : Convert c e A B
  backward : Convert c e B A

/-- Four actual maps, packaged as positive and negative conversion pairs. -/
structure Package (e : Bool) (F : Formula L α) (h : F.EqualityFree) where
  positive : Bridge true e F (positive F h)
  negative : Bridge true e (.neg F) (negative F h)

theorem reading_map {n m} (F : BF L α n) (h : F.EqualityFree)
    (σ : Lemmatheca.ProofTheory.FirstOrder.ScopeSubst L α β n m) (b : Bool) :
    reading (F.map σ) ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F σ).2 h) b =
      (reading F h b).map σ := by
  unfold reading
  rw [Nnf.normalize_map, Nnf.read_map]

theorem reading_subst {n} (F : BF L α n) (h : F.EqualityFree)
    (σ : α → L.Term β) (b : Bool) :
    reading (F.subst σ) ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h) b =
      (reading F h b).subst σ := by
  exact reading_map F h _ b

theorem reading_rename {n} (F : BF L α n) (h : F.EqualityFree)
    (f : α → β) (b : Bool) :
    reading (F.rename f) ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h) b =
      (reading F h b).rename f := by
  exact reading_subst F h _ b

theorem reading_open {n} (F : BF L α n) (h : F.EqualityFree) (b : Bool) :
    reading F.toFormula ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h) b =
      (reading F h b).toFormula := by
  exact reading_map F h _ b

theorem reading_instance (F : BF L α 1) (h : F.EqualityFree) (t : L.Term α) (b : Bool) :
    reading (F.instantiate t) ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map F _).2 h) b =
      (reading F h b).instantiate t := by
  exact reading_map F h _ b

theorem reading_negative_read {n} (A : Nnf L α n) :
    reading A.read A.read_equalityFree false = A.dual.read := by
  simp only [reading, Nnf.normalize_dual, Nnf.normalize_read]

noncomputable section
local instance signedScopeFormulaEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

/-- Double-negation introduction is a native operation in either deduction mode. -/
def doubleNegIntro {c e : Bool} {Γ : Context L α} {A : Formula L α}
    (p : Derivation c e L Γ A) : Derivation c e L Γ (.neg (.neg A)) := by
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.negIntro
  exact .negElim (p.weaken (Finset.subset_insert _ _))
    (.assumption (Finset.mem_insert_self _ _))

end
end Lemmatheca.ProofTheory.ClassicalFirstOrder.SignedDeductions
