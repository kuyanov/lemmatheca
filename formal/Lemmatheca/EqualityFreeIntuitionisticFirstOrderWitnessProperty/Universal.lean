import Lemmatheca.EqualityFreeIntuitionisticFirstOrderWitnessProperty.Public

/-! Open the outer available slot and protect the inner existential slot. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifowpUniversalEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

def openOuter (B : BF L α 2) : BF L (α ⊕ Fin 1) 1 :=
  B.map (Lemmatheca.ProofTheory.FirstOrder.liftScope
    (fun x : α ⊕ Fin 1 => .var (.inl x)))

theorem openOuter_ex (B : BF L α 2) :
    (.ex B : BF L α 1).toFormula = .ex (openOuter B) := by
  rfl

/-- The actual last universal-right premise of an empty-antecedent core tree. -/
def allPremise {C : BF L α 1} (p : CoreProof L ∅ (.all C)) :
    CoreProof L (liftContext (∅ : Context L α)) C.toFormula := by
  cases p with
  | allRight q => exact q
  | falsumLeft hm => exact (Finset.notMem_empty _ hm).elim
  | conjLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | disjLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | implLeft hm _ _ => exact (Finset.notMem_empty _ hm).elim
  | negLeft hm _ => exact (Finset.notMem_empty _ hm).elim
  | allLeft _ hm _ => exact (Finset.notMem_empty _ hm).elim
  | exLeft hm _ => exact (Finset.notMem_empty _ hm).elim

theorem allPremise_allRight {C : BF L α 1}
    (p : CoreProof L (liftContext (∅ : Context L α)) C.toFormula) :
    allPremise (.allRight p) = p := by
  rfl

def universalWitness {B : BF L α 2} (p : RawProof L ∅ (.all (.ex B))) :
    WitnessPacket (openOuter B) := by
  let hΓ : liftContext (∅ : Context L α) = ∅ := Finset.image_empty _
  let tree : CoreProof L ∅ (.ex (openOuter B)) :=
    hΓ ▸ (openOuter_ex B ▸ allPremise p.tree)
  exact rawWitness (⟨tree, (fun C hC => (Finset.notMem_empty C hC).elim),
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).mpr
      p.conclusion_pure⟩ : RawProof L ∅ (.ex (openOuter B)))

def publicUniversalWitness {B : BF L α 2} (p : Proof L ∅ (.all (.ex B))) :
    WitnessPacket (openOuter (B.rename (Sum.inl : α → α ⊕ ℕ))) := by
  let σ : α → L.Term (α ⊕ ℕ) := fun x => .var (.inl x)
  let e : ((.all (.ex B) : Formula L α).rename (Sum.inl : α → α ⊕ ℕ)) =
      .all (.ex (B.rename (Sum.inl : α → α ⊕ ℕ))) :=
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all (.ex B) σ).trans
      (congrArg Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.all
        (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex B σ))
  exact universalWitness (reindexRaw rfl e (underlyingPublic p))

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
