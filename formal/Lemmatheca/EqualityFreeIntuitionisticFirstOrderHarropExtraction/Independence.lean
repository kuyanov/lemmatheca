import Lemmatheca.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Examples
import Lemmatheca.IntuitionisticFirstOrderQuantifierPrinciples.Laws

/-! Existential independence of a Harrop premise, with actual supplied proof data. -/
namespace Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop

open _root_.FirstOrder _root_.FirstOrder.Language
namespace Independence

universe u v w
variable {L : Language.{u,v}} {α β : Type w}
noncomputable section
local instance independenceFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

private abbrev ND := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation
private abbrev PublicND := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof

/-- The old premise has no occurrence of the body's one new bound slot. -/
def body (H : Formula L α) (B : BF L α 1) : BF L α 1 :=
  .impl (Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples.vacuous H) B

theorem body_instantiate (H : Formula L α) (B : BF L α 1) (t : L.Term α) :
    (body H B).instantiate t = .impl H (B.instantiate t) := by
  change Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.impl ((Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples.vacuous H).instantiate t)
    (B.instantiate t) = _
  rw [Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples.vacuous_instantiate]

theorem body_rename (H : Formula L α) (B : BF L α 1) (f : α → β) :
    (body H B).rename f = body (H.rename f) (B.rename f) := by
  change Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.impl ((Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples.vacuous H).rename f)
    (B.rename f) = _
  unfold body
  congr 1
  simp only [Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples.vacuous,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.map_comp]
  congr 1
  funext x
  cases x with
  | inl x => rfl
  | inr x => exact x.elim0

theorem body_pure (H : Formula L α) (B : BF L α 1)
    (hH : H.EqualityFree) (hB : B.EqualityFree) : (body H B).EqualityFree := by
  change (Lemmatheca.ProofTheory.FirstOrder.QuantifierPrinciples.vacuous H).EqualityFree ∧ B.EqualityFree
  exact ⟨(Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map H _).mpr hH, hB⟩

theorem inserted_harrop {Γ : Context L α} {H : Formula L α}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) : ContextHarrop (insert H Γ) := by
  intro D hD
  rcases Finset.mem_insert.mp hD with rfl | hD
  · exact hH
  · exact hΓ D hD

/-- The stored term is accompanied by its exact discharged native instance. -/
structure Packet (Γ : Context L α) (H : Formula L α) (B : BF L α 1) : Type max u v (w+1) where
  term : L.Term α
  instanceProof : ND false false L Γ (.impl H (B.instantiate term))

private def reindexNative {Γ Δ : Context L α} {A C : Formula L α}
    (hΓ : Γ = Δ) (hA : A = C) (p : ND false false L Γ A) : ND false false L Δ C :=
  hΓ ▸ hA ▸ p

/-- Existential introduction uses this packet's literal term and stored instance. -/
def Packet.conclusion {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (d : Packet Γ H B) : ND false false L Γ (.ex (body H B)) :=
  .exIntro d.term (reindexNative rfl (body_instantiate H B d.term).symm d.instanceProof)

/-- Apply the actual supplied implication after weakening it into the enlarged context. -/
def applied {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (p : ND false false L Γ (.impl H (.ex B))) : ND false false L (insert H Γ) (.ex B) :=
  .impElim (p.weaken (Finset.subset_insert H Γ)) (.assumption (Finset.mem_insert_self H Γ))

/-- Normalize precisely that applied native proof, in the same original-name universe. -/
def normalized {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (p : ND false false L Γ (.impl H (.ex B))) : RawProof L (insert H Γ) (.ex B) :=
  RawProof.fromNatural (applied p) (context_pure (inserted_harrop hΓ hH)) hB

/-- Discharge the same retained assumption from the exact returned instance tree. -/
def fromWitness {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (d : WitnessPacket (insert H Γ) B) : Packet Γ H B :=
  ⟨d.term, .impIntro d.proof.toNatural⟩

def withDefault {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree) (r : L.Term α)
    (p : ND false false L Γ (.impl H (.ex B))) : Packet Γ H B :=
  fromWitness (witnessWithDefault (inserted_harrop hΓ hH) r (normalized hΓ hH hB p))

def ofConsistent {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (hCon : Consistent (insert H Γ))
    (p : ND false false L Γ (.impl H (.ex B))) : Packet Γ H B :=
  fromWitness (witnessOfConsistent (inserted_harrop hΓ hH) hCon (normalized hΓ hH hB p))

theorem withDefault_term {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree) (r : L.Term α)
    (p : ND false false L Γ (.impl H (.ex B))) :
    (withDefault hΓ hH hB r p).term =
      (witnessWithDefault (inserted_harrop hΓ hH) r (normalized hΓ hH hB p)).term := by
  rfl

theorem ofConsistent_term {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (hCon : Consistent (insert H Γ))
    (p : ND false false L Γ (.impl H (.ex B))) :
    (ofConsistent hΓ hH hB hCon p).term =
      (witnessOfConsistent (inserted_harrop hΓ hH) hCon (normalized hΓ hH hB p)).term := by
  rfl

/-- Both sequent grammars feed their actual input tree through the native bridge. -/
def rawWithDefault {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree) (r : L.Term α)
    (p : RawProof L Γ (.impl H (.ex B))) : Packet Γ H B :=
  withDefault hΓ hH hB r p.toNatural

def rawOfConsistent {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (hCon : Consistent (insert H Γ)) (p : RawProof L Γ (.impl H (.ex B))) : Packet Γ H B :=
  ofConsistent hΓ hH hB hCon p.toNatural

def cutWithDefault {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree) (r : L.Term α)
    (p : RawCutProof L Γ (.impl H (.ex B))) : Packet Γ H B :=
  withDefault hΓ hH hB r p.toNatural

def cutOfConsistent {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (hCon : Consistent (insert H Γ)) (p : RawCutProof L Γ (.impl H (.ex B))) : Packet Γ H B :=
  ofConsistent hΓ hH hB hCon p.toNatural

private def underlyingInput {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (p : PublicND false false L Γ (.impl H (.ex B))) :
    ND false false L (reservedContext Γ)
      (.impl (H.rename (Sum.inl : α → α ⊕ ℕ)) (.ex (B.rename Sum.inl))) := by
  simpa only [Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Proof,
    PublicND, ND, reservedContext,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.rename,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl,
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex] using p

/-- The default is literally the first reserved variable, in precisely α ⊕ ℕ. -/
def publicPacket {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (p : PublicND false false L Γ (.impl H (.ex B))) :
    Packet (reservedContext Γ) (H.rename (Sum.inl : α → α ⊕ ℕ)) (B.rename Sum.inl) :=
  withDefault (context_rename hΓ Sum.inl) (harrop_map hH _)
    ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map B _).2 hB)
    (.var (.inr 0)) (underlyingInput p)

def publicNative {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (p : PublicND false false L Γ (.impl H (.ex B))) :
    PublicND false false L Γ (.ex (body H B)) := by
  have q := (publicPacket hΓ hH hB p).conclusion
  change ND false false L (reservedContext Γ)
    (((body H B).ex).rename (Sum.inl : α → α ⊕ ℕ))
  apply reindexNative rfl _ q
  exact ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex (body H B)
    (fun x : α => (Term.var (Sum.inl x) : L.Term (α ⊕ ℕ)))).trans
    (congrArg (fun D : BF L (α ⊕ ℕ) 1 => D.ex) (body_rename H B Sum.inl))).symm

def publicSequent {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (p : Proof L Γ (.impl H (.ex B))) : Proof L Γ (.ex (body H B)) :=
  Proof.fromNatural (publicNative hΓ hH hB p.toNatural) (context_pure hΓ)
    (body_pure H B (harrop_pure hH) hB)

def publicCut {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (p : CutCertificate L Γ (.impl H (.ex B))) : Proof L Γ (.ex (body H B)) :=
  publicSequent hΓ hH hB p.eliminate

/-- Substitute through the same packet's term and instance, fixing original assumptions. -/
def removeReserve {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (d : Packet (reservedContext Γ) (H.rename (Sum.inl : α → α ⊕ ℕ)) (B.rename Sum.inl))
    (r : L.Term α) : Packet Γ H B := by
  refine ⟨d.term.subst (WitnessProperty.reserveSubstitution r), ?_⟩
  refine reindexNative (reserve_context Γ r) ?_
    (d.instanceProof.substitute (WitnessProperty.reserveSubstitution r))
  rw [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_impl,
    WitnessProperty.reserve_body, WitnessProperty.reserve_instance]

theorem removeReserve_term {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (d : Packet (reservedContext Γ) (H.rename (Sum.inl : α → α ⊕ ℕ)) (B.rename Sum.inl))
    (r : L.Term α) :
    (removeReserve d r).term = d.term.subst (WitnessProperty.reserveSubstitution r) := by
  rfl

def publicOriginal {Γ : Context L α} {H : Formula L α} {B : BF L α 1}
    (hΓ : ContextHarrop Γ) (hH : IsHarrop H) (hB : B.EqualityFree)
    (p : PublicND false false L Γ (.impl H (.ex B))) (r : L.Term α) : Packet Γ H B :=
  removeReserve (publicPacket hΓ hH hB p) r

end
end Independence
end Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop

namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Independence
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder.EqualityFreeHarrop
noncomputable section
local instance boundaryFormulaEq {δ : Type*} :
    DecidableEq (Formula Language.empty δ) := Classical.decEq _

/-- The native implication has a finite explosion proof and requires no term. -/
def boundaryInput :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false Language.empty
      (∅ : Context Language.empty Empty) (.impl .falsum (.ex .falsum)) :=
  .impIntro (.falsumElim (.assumption (Finset.mem_insert_self _ _)))

theorem empty_consistent : Consistent (∅ : Context Language.empty Empty) := by
  rintro ⟨p⟩
  have q := p.tree
  cases q <;> simp_all

theorem no_raw_boundary : ¬ Nonempty (RawProof Language.empty
    (∅ : Context Language.empty Empty)
    (.ex (EqualityFreeHarrop.Independence.body .falsum .falsum))) := by
  rintro ⟨p⟩
  cases p.tree with
  | falsumLeft h => simp at h
  | conjLeft h _ => simp at h
  | disjLeft h _ _ => simp at h
  | implLeft h _ _ => simp at h
  | negLeft h _ => simp at h
  | allLeft _ h _ => simp at h
  | exLeft h _ => simp at h
  | exRight t _ =>
    exact Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderSequents.constantFreeNoGroundTerm ⟨t⟩

theorem no_cut_boundary : ¬ Nonempty (RawCutProof Language.empty
    (∅ : Context Language.empty Empty)
    (.ex (EqualityFreeHarrop.Independence.body .falsum .falsum))) := by
  rintro ⟨p⟩
  exact no_raw_boundary ⟨p.eliminate⟩

theorem no_native_boundary : ¬ Nonempty
    (Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false Language.empty
      (∅ : Context Language.empty Empty)
      (.ex (EqualityFreeHarrop.Independence.body .falsum .falsum))) := by
  rintro ⟨p⟩
  apply no_raw_boundary
  exact ⟨RawProof.fromNatural p (by intro D hD; simp at hD)
    (EqualityFreeHarrop.Independence.body_pure .falsum .falsum True.intro True.intro)⟩

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderHarropExtraction.Independence
