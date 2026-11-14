import Lemmatheca.EqualityFreeIntuitionisticFirstOrderWitnessProperty.Inputs

/-! Public data retain the reserve. Removing it requires a supplied original term. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifowpPublicEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

/-- Transport only the indices of this supplied actual record. -/
def reindexRaw {Γ Δ : Context L α} {A C : Formula L α}
    (hΓ : Γ = Δ) (hA : A = C) (p : RawProof L Γ A) : RawProof L Δ C := hΓ ▸ hA ▸ p

/-- The identical reserved record, with its empty image context transported. -/
def underlyingPublic {A : Formula L α} (p : Proof L ∅ A) :
    RawProof L ∅ (A.rename (Sum.inl : α → α ⊕ ℕ)) :=
  reindexRaw (Finset.image_empty _) rfl p

private def publicFromUnderlying {A : Formula L α}
    (p : RawProof L ∅ (A.rename (Sum.inl : α → α ⊕ ℕ))) : Proof L ∅ A :=
  reindexRaw (Finset.image_empty _).symm rfl p

def publicDisjunction {A B : Formula L α} (p : Proof L ∅ (.disj A B)) :
    Sum (Proof L ∅ A) (Proof L ∅ B) := by
  let q := rawDisjunction (reindexRaw rfl
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj A B
      (fun x : α => (Term.var (Sum.inl x) : L.Term (α ⊕ ℕ)))) (underlyingPublic p))
  exact Sum.map (publicFromUnderlying (A := A)) (publicFromUnderlying (A := B)) q

def publicWitness {B : BF L α 1} (p : Proof L ∅ (.ex B)) :
    WitnessPacket (B.rename (Sum.inl : α → α ⊕ ℕ)) := rawWitness (reindexRaw rfl
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex B
      (fun x : α => (Term.var (Sum.inl x) : L.Term (α ⊕ ℕ)))) (underlyingPublic p))

theorem public_disjunction_iff (A B : Formula L α) (hA : A.EqualityFree) (hB : B.EqualityFree) :
    Derives L ∅ (.disj A B) ↔ Derives L ∅ A ∨ Derives L ∅ B := by
  constructor
  · rintro ⟨p⟩
    cases publicDisjunction p with
    | inl q => exact Or.inl ⟨q⟩
    | inr q => exact Or.inr ⟨q⟩
  · intro h
    cases h with
    | inl hp =>
      rcases hp with ⟨p⟩
      exact ⟨Proof.fromNatural (.disjIntroLeft p.toNatural)
        (fun C hC => (Finset.notMem_empty C hC).elim) ⟨hA, hB⟩⟩
    | inr hp =>
      rcases hp with ⟨p⟩
      exact ⟨Proof.fromNatural (.disjIntroRight p.toNatural)
        (fun C hC => (Finset.notMem_empty C hC).elim) ⟨hA, hB⟩⟩

/-- Fix original variables and replace each reserve variable by this original term. -/
def reserveSubstitution (r : L.Term α) : α ⊕ ℕ → L.Term α :=
  Sum.elim Term.var (fun _ => r)

theorem reserve_body {n} (B : BF L α n) (r : L.Term α) :
    (B.rename (Sum.inl : α → α ⊕ ℕ)).subst (reserveSubstitution r) = B := by
  rw [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.formula_rename_subst]
  exact B.subst_id

theorem reserve_instance (B : BF L α 1) (t : L.Term (α ⊕ ℕ)) (r : L.Term α) :
    ((B.rename (Sum.inl : α → α ⊕ ℕ)).instantiate t).subst (reserveSubstitution r) =
      B.instantiate (t.subst (reserveSubstitution r)) := by
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.instantiate_subst, reserve_body]

def removeReserve {B : BF L α 1}
    (d : WitnessPacket (B.rename (Sum.inl : α → α ⊕ ℕ))) (r : L.Term α) :
    WitnessPacket B := ⟨d.term.subst (reserveSubstitution r),
    reindexRaw (Finset.image_empty _) (reserve_instance B d.term r)
      (d.proof.substitute (reserveSubstitution r))⟩

theorem removeReserve_term {B : BF L α 1}
    (d : WitnessPacket (B.rename (Sum.inl : α → α ⊕ ℕ))) (r : L.Term α) :
    (removeReserve d r).term = d.term.subst (reserveSubstitution r) := by
  rfl

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.WitnessProperty
