import Lemmatheca.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Inputs
import Lemmatheca.EqualityFreeIntuitionisticFirstOrderWitnessProperty.Public

/-! Public extraction uses the actual renamed context and retains its reserve. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
open _root_.FirstOrder _root_.FirstOrder.Language
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifohPublicEq {δ : Type w} : DecidableEq (Formula L δ) := Classical.decEq _

abbrev reservedContext (Γ : Context L α) : Context L (α ⊕ ℕ) :=
  Γ.image (fun D => D.rename (Sum.inl : α → α ⊕ ℕ))

private def underlyingDisjunction {Γ : Context L α} {A B : Formula L α}
    (p : Proof L Γ (.disj A B)) :
    RawProof L (reservedContext Γ) (.disj (A.rename (Sum.inl : α → α ⊕ ℕ)) (B.rename Sum.inl)) :=
  WitnessProperty.reindexRaw rfl
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_disj A B
      (fun x : α => (Term.var (Sum.inl x) : L.Term (α ⊕ ℕ)))) p

private def underlyingExistential {Γ : Context L α} {B : BF L α 1}
    (p : Proof L Γ (.ex B)) :
    RawProof L (reservedContext Γ) (.ex (B.rename (Sum.inl : α → α ⊕ ℕ))) :=
  WitnessProperty.reindexRaw rfl
    (Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex B
      (fun x : α => (Term.var (Sum.inl x) : L.Term (α ⊕ ℕ)))) p

def publicDisjunction {Γ : Context L α} {A B : Formula L α} (hΓ : ContextHarrop Γ)
    (p : Proof L Γ (.disj A B)) : Sum (Proof L Γ A) (Proof L Γ B) :=
  disjunction (context_rename hΓ (Sum.inl : α → α ⊕ ℕ)) (underlyingDisjunction p)

def publicOutcome {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (p : Proof L Γ (.ex B)) : Outcome (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ)) :=
  outcome (context_rename hΓ (Sum.inl : α → α ⊕ ℕ)) (underlyingExistential p)

/-- The default is the literal first reserved variable in this actual public scope. -/
def publicWitness {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (p : Proof L Γ (.ex B)) : WitnessPacket (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ)) :=
  resolveDefault (underlyingExistential p).conclusion_pure (.var (.inr 0)) (publicOutcome hΓ p)

def publicWitnessOfConsistent {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (hCon : Consistent (reservedContext Γ)) (p : Proof L Γ (.ex B)) :
    WitnessPacket (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ)) :=
  resolveConsistent hCon (publicOutcome hΓ p)

def publicCutDisjunction {Γ : Context L α} {A B : Formula L α} (hΓ : ContextHarrop Γ)
    (p : CutCertificate L Γ (.disj A B)) : Sum (Proof L Γ A) (Proof L Γ B) :=
  publicDisjunction hΓ p.eliminate

def publicNativeDisjunction {Γ : Context L α} {A B : Formula L α} (hΓ : ContextHarrop Γ)
    (hA : A.EqualityFree) (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof false false L Γ (.disj A B)) :
    Sum (Proof L Γ A) (Proof L Γ B) :=
  publicDisjunction hΓ (Proof.fromNatural p (context_pure hΓ) ⟨hA, hB⟩)

def publicCutWitness {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (p : CutCertificate L Γ (.ex B)) :
    WitnessPacket (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ)) :=
  publicWitness hΓ p.eliminate

def publicNativeWitness {Γ : Context L α} {B : BF L α 1} (hΓ : ContextHarrop Γ)
    (hB : B.EqualityFree)
    (p : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof false false L Γ (.ex B)) :
    WitnessPacket (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ)) :=
  publicWitness hΓ (Proof.fromNatural p (context_pure hΓ) hB)

theorem public_disjunction_iff {Γ : Context L α} (hΓ : ContextHarrop Γ)
    (A B : Formula L α) (hA : A.EqualityFree) (hB : B.EqualityFree) :
    Derives L Γ (.disj A B) ↔ Derives L Γ A ∨ Derives L Γ B := by
  constructor
  · rintro ⟨p⟩
    cases publicDisjunction hΓ p with
    | inl q => exact Or.inl ⟨q⟩
    | inr q => exact Or.inr ⟨q⟩
  · intro h
    cases h with
    | inl hp =>
      obtain ⟨p⟩ := hp
      exact ⟨Proof.fromNatural (.disjIntroLeft p.toNatural) (context_pure hΓ) ⟨hA, hB⟩⟩
    | inr hp =>
      obtain ⟨p⟩ := hp
      exact ⟨Proof.fromNatural (.disjIntroRight p.toNatural) (context_pure hΓ) ⟨hA, hB⟩⟩

theorem native_disjunction_iff {Γ : Context L α} (hΓ : ContextHarrop Γ)
    (A B : Formula L α) (hA : A.EqualityFree) (hB : B.EqualityFree) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false false L Γ (.disj A B) ↔
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false false L Γ A ∨
      Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false false L Γ B := by
  rw [native_iff_cutFree (C := .disj A B) (context_pure hΓ) ⟨hA, hB⟩,
    native_iff_cutFree (C := A) (context_pure hΓ) hA,
    native_iff_cutFree (C := B) (context_pure hΓ) hB]
  exact public_disjunction_iff hΓ A B hA hB

theorem native_reserved_existence {Γ : Context L α} (hΓ : ContextHarrop Γ)
    (B : BF L α 1) (hB : B.EqualityFree)
    (h : Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derives false false L Γ (.ex B)) :
    ∃ t : L.Term (α ⊕ ℕ), Nonempty (RawProof L (reservedContext Γ)
      ((B.rename (Sum.inl : α → α ⊕ ℕ)).instantiate t)) := by
  obtain ⟨p⟩ := h
  let d := publicNativeWitness hΓ hB p
  exact ⟨d.term, ⟨d.proof⟩⟩

/-- All original assumptions, including open ones, are fixed by this actual substitution. -/
theorem reserve_context (Γ : Context L α) (r : L.Term α) :
    (reservedContext Γ).image (fun D => D.subst (WitnessProperty.reserveSubstitution r)) = Γ := by
  simp only [reservedContext, Finset.image_image, Function.comp_def,
    WitnessProperty.reserve_body]
  exact Finset.image_id

def removeReserve {Γ : Context L α} {B : BF L α 1}
    (d : WitnessPacket (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ)))
    (r : L.Term α) : WitnessPacket Γ B :=
  ⟨d.term.subst (WitnessProperty.reserveSubstitution r),
    WitnessProperty.reindexRaw (reserve_context Γ r)
      (WitnessProperty.reserve_instance B d.term r)
      (d.proof.substitute (WitnessProperty.reserveSubstitution r))⟩

theorem removeReserve_term {Γ : Context L α} {B : BF L α 1}
    (d : WitnessPacket (reservedContext Γ) (B.rename (Sum.inl : α → α ⊕ ℕ))) (r : L.Term α) :
    (removeReserve d r).term = d.term.subst (WitnessProperty.reserveSubstitution r) := by
  rfl

def removeReserveContradiction {Γ : Context L α}
    (q : RawProof L (reservedContext Γ) .falsum) (r : L.Term α) : RawProof L Γ .falsum :=
  WitnessProperty.reindexRaw (reserve_context Γ r) rfl
    (q.substitute (WitnessProperty.reserveSubstitution r))

theorem consistent_reserved_of_term {Γ : Context L α} (r : L.Term α)
    (hCon : Consistent Γ) : Consistent (reservedContext Γ) := by
  rintro ⟨q⟩
  exact hCon ⟨removeReserveContradiction q r⟩

def publicOriginalWitness {Γ : Context L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (p : Proof L Γ (.ex B)) (r : L.Term α) : WitnessPacket Γ B :=
  removeReserve (publicWitness hΓ p) r

end
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
