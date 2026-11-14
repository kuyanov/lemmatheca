import Lemmatheca.EqualityFreeIntuitionisticFirstOrderCutElimination.Properties

/-! Actual tagged disjuncts and dependent term/instance proof data. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifowpPacketsEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

/-- The tag retains which actual empty-antecedent pure proof was returned. -/
def DisjunctPacket (A B : Formula L α) :=
  Sum (RawProof L (∅ : Context L α) A) (RawProof L (∅ : Context L α) B)

/-- The stored syntax term and a proof of precisely its capture-free instance. -/
structure WitnessPacket (B : BF L α 1) where
  term : L.Term α
  proof : RawProof L (∅ : Context L α) (B.instantiate term)

/-- Inspect the supplied tree's last constructor; no proof is chosen from Prop. -/
def rawDisjunction {A B : Formula L α} (p : RawProof L ∅ (.disj A B)) :
    DisjunctPacket A B := by
  rcases p with ⟨tree, hΓ, hAB⟩
  cases tree with
  | disjRightLeft q => exact .inl ⟨q, hΓ, hAB.1⟩
  | disjRightRight q => exact .inr ⟨q, hΓ, hAB.2⟩
  | falsumLeft hm => exact (Finset.notMem_empty _ hm).elim
  | conjLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | disjLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | implLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | negLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | allLeft _ hm _ => exact (Finset.notMem_empty _ hm).elim
  | exLeft hm _ => exact (Finset.notMem_empty _ hm).elim

def rebuildDisjunct {A B : Formula L α} (hA : A.EqualityFree) (hB : B.EqualityFree)
    (d : DisjunctPacket A B) : RawProof L ∅ (.disj A B) := by
  cases d with
  | inl p => exact ⟨.disjRightLeft p.tree, p.context_pure, ⟨hA, hB⟩⟩
  | inr p => exact ⟨.disjRightRight p.tree, p.context_pure, ⟨hA, hB⟩⟩

theorem rawDisjunction_left {A B : Formula L α} (p : RawProof L ∅ A)
    (hB : B.EqualityFree) :
    rawDisjunction (⟨.disjRightLeft p.tree, p.context_pure,
      ⟨p.conclusion_pure, hB⟩⟩ : RawProof L ∅ (.disj A B)) =
      (Sum.inl p : DisjunctPacket A B) := by
  rfl

theorem rawDisjunction_right {A B : Formula L α} (hA : A.EqualityFree)
    (p : RawProof L ∅ B) :
    rawDisjunction (⟨.disjRightRight p.tree, p.context_pure,
      ⟨hA, p.conclusion_pure⟩⟩ : RawProof L ∅ (.disj A B)) =
      (Sum.inr p : DisjunctPacket A B) := by
  rfl

theorem disjunct_roundtrip {A B : Formula L α} (p : RawProof L ∅ (.disj A B)) :
    rebuildDisjunct p.conclusion_pure.1 p.conclusion_pure.2 (rawDisjunction p) = p := by
  rcases p with ⟨tree, hΓ, hAB⟩
  cases tree with
  | disjRightLeft q => rfl
  | disjRightRight q => rfl
  | falsumLeft hm => exact (Finset.notMem_empty _ hm).elim
  | conjLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | disjLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | implLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | negLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | allLeft _ hm _ => exact (Finset.notMem_empty _ hm).elim
  | exLeft hm _ => exact (Finset.notMem_empty _ hm).elim

theorem raw_disjunction_iff (A B : Formula L α) (hA : A.EqualityFree) (hB : B.EqualityFree) :
    Nonempty (RawProof L ∅ (.disj A B)) ↔
      Nonempty (RawProof L ∅ A) ∨ Nonempty (RawProof L ∅ B) := by
  constructor
  · rintro ⟨p⟩
    cases rawDisjunction p with
    | inl q => exact Or.inl ⟨q⟩
    | inr q => exact Or.inr ⟨q⟩
  · intro h
    cases h with
    | inl hp =>
      rcases hp with ⟨p⟩
      exact ⟨rebuildDisjunct hA hB (.inl p)⟩
    | inr hp =>
      rcases hp with ⟨p⟩
      exact ⟨rebuildDisjunct hA hB (.inr p)⟩

/-- Return the actual final existential term together with its actual child. -/
def rawWitness {B : BF L α 1} (p : RawProof L ∅ (.ex B)) : WitnessPacket B := by
  rcases p with ⟨tree, hΓ, hB⟩
  cases tree with
  | exRight t q => exact ⟨t, ⟨q, hΓ,
      (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).mpr hB⟩⟩
  | falsumLeft hm => exact (Finset.notMem_empty _ hm).elim
  | conjLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | disjLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | implLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | negLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | allLeft _ hm _ => exact (Finset.notMem_empty _ hm).elim
  | exLeft hm _ => exact (Finset.notMem_empty _ hm).elim

def rebuildWitness {B : BF L α 1} (hB : B.EqualityFree) (d : WitnessPacket B) :
    RawProof L ∅ (.ex B) := by
  exact ⟨.exRight d.term d.proof.tree, d.proof.context_pure, hB⟩

theorem rawWitness_exRight {B : BF L α 1} (hB : B.EqualityFree)
    (t : L.Term α) (p : RawProof L ∅ (B.instantiate t)) :
    rawWitness (⟨.exRight t p.tree, p.context_pure, hB⟩ : RawProof L ∅ (.ex B)) =
      (⟨t, p⟩ : WitnessPacket B) := by
  rfl

theorem witness_roundtrip {B : BF L α 1} (p : RawProof L ∅ (.ex B)) :
    rebuildWitness p.conclusion_pure (rawWitness p) = p := by
  rcases p with ⟨tree, hΓ, hB⟩
  cases tree with
  | exRight t q => rfl
  | falsumLeft hm => exact (Finset.notMem_empty _ hm).elim
  | conjLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | disjLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | implLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | negLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | allLeft _ hm _ => exact (Finset.notMem_empty _ hm).elim
  | exLeft hm _ => exact (Finset.notMem_empty _ hm).elim

theorem raw_existence_iff (B : BF L α 1) (hB : B.EqualityFree) :
    Nonempty (RawProof L ∅ (.ex B)) ↔
      ∃ t : L.Term α, Nonempty (RawProof L ∅ (B.instantiate t)) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨(rawWitness p).term, ⟨(rawWitness p).proof⟩⟩
  · rintro ⟨t, ⟨p⟩⟩
    exact ⟨rebuildWitness hB ⟨t, p⟩⟩

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
