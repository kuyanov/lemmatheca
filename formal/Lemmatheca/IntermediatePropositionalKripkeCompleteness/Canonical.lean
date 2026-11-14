import Lemmatheca.IntuitionisticPropositionalKripkeCompleteness.CanonicalModel
import Lemmatheca.IntuitionisticPropositionalKripkeMorphisms.Morphisms
import Lemmatheca.PropositionalWeakExcludedMiddle.Schemas

/-! Restrict the existing prime-theory model to a fixed consistent axiom set. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.IntermediateCanonical

open Lemmatheca.MathematicalLogic.Propositional
open PropFormula Canonical Extensions Kripke

universe v

/-- These are actual old prime worlds, with the additional containment condition. -/
abbrev World (S : Set Formula) := {P : PrimeWorld // S ⊆ P.val}

/-- The model depends on the fixed axiom set and its consistency, before Γ or A. -/
noncomputable def model (S : Set Formula) (hS : Consistent S) : Model ℕ (World S) where
  world_nonempty := ⟨⟨extensionWorld S falsum hS, extension_contains S falsum⟩⟩
  valuation P p := atom p ∈ P.val.val
  persistent hPQ _ h := hPQ h

theorem inclusion_boundedMorphism (S : Set Formula) (hS : Consistent S) :
    IsBoundedMorphism (model S hS) canonicalModel (Subtype.val : World S → PrimeWorld) := by
  refine { forth := fun _ _ h => h, back := ?_, atoms := fun _ _ => Iff.rfl }
  intro P Q hPQ
  exact ⟨⟨Q, fun B hB => hPQ (P.property hB)⟩, hPQ, rfl⟩

theorem truth_lemma (S : Set Formula) (hS : Consistent S) (P : World S) (A : Formula) :
    Forces (model S hS) P A ↔ A ∈ P.val.val := by
  exact (boundedMorphism_forcing (model S hS) canonicalModel Subtype.val
    (inclusion_boundedMorphism S hS) P A).trans (canonical_truth A P.val)

/-- The actual earlier avoiding extension of Γ ∪ S, with its specified formula set. -/
noncomputable def counterworld (S Γ : Set Formula) (A : Formula)
    (h : ¬ SchemaConsequence S Γ A) : World S :=
  ⟨extensionWorld (Γ ∪ S) A (fun hd => h ((schemaConsequence_iff_union S Γ A).mpr hd)),
    fun _ hB => extension_contains (Γ ∪ S) A (Or.inr hB)⟩

theorem specified_countermodel (S : Set Formula) (hS : Consistent S)
    (Γ : Set Formula) (A : Formula) (h : ¬ SchemaConsequence S Γ A) :
    Countermodel (model S hS) (counterworld S Γ A h) Γ A := by
  constructor
  · intro B hB
    apply (truth_lemma S hS _ B).mpr
    exact extension_contains (Γ ∪ S) A (Or.inl hB)
  · intro hA
    have hn : ¬ Derives (Γ ∪ S) A :=
      fun hd => h ((schemaConsequence_iff_union S Γ A).mpr hd)
    exact extension_omits hn ((truth_lemma S hS _ A).mp hA)

/-- Only a universe lift: the worlds, inclusion relation and valuation are unchanged. -/
noncomputable def liftedModel (S : Set Formula) (hS : Consistent S) :
    Model ℕ (ULift.{v} (World S)) where
  world_nonempty := ⟨ULift.up ⟨extensionWorld S falsum hS, extension_contains S falsum⟩⟩
  valuation P p := atom p ∈ P.down.val.val
  persistent hPQ _ h := hPQ h

/-- A bookkeeping bridge for the arbitrary world universe in class consequence. -/
theorem lifted_forcing (S : Set Formula) (hS : Consistent S)
    (P : ULift.{v} (World S)) (A : Formula) :
    Forces (liftedModel S hS) P A ↔ Forces (model S hS) P.down A := by
  apply boundedMorphism_forcing (liftedModel S hS) (model S hS) ULift.down
  refine { forth := fun _ _ h => h, back := ?_, atoms := fun _ _ => Iff.rfl }
  intro P Q hPQ
  exact ⟨ULift.up Q, hPQ, rfl⟩

/-- Empty support is the literal native truth formula, and repetitions are retained. -/
def package : List Formula → Formula
  | [] => impl falsum falsum
  | B :: L => conj B (package L)

private theorem package_from_members (L : List Formula) (Γ : Set Formula)
    (hL : ∀ B ∈ L, Derives Γ B) : Derives Γ (package L) := by
  induction L with
  | nil => exact .implIntro (.assumption (Set.mem_insert _ _))
  | cons B L ih =>
      exact .conjIntro (hL B (by simp)) (ih (fun C hC => hL C (by simp [hC])))

private theorem member_from_package (L : List Formula) (Γ : Set Formula)
    (B : Formula) (hB : B ∈ L) (h : Derives Γ (package L)) : Derives Γ B := by
  induction L with
  | nil => simp at hB
  | cons C L ih =>
      rcases List.mem_cons.mp hB with rfl | hB
      · exact .conjElimLeft h
      · exact ih hB (.conjElimRight h)

theorem package_premises (U : Set Formula) (L : List Formula) (A : Formula) :
    Derives (U ∪ {B | B ∈ L}) A ↔ Derives (insert (package L) U) A := by
  constructor
  · intro hd
    apply hd.replace
    intro B hB
    rcases hB with hU | hL
    · exact .assumption (Set.mem_insert_of_mem _ hU)
    · exact member_from_package L _ B hL (.assumption (Set.mem_insert _ _))
  · intro hd
    apply hd.replace
    intro B hB
    rcases Set.mem_insert_iff.mp hB with rfl | hU
    · exact package_from_members L _ (fun C hC => .assumption (Or.inr hC))
    · exact .assumption (Or.inl hU)

theorem package_mem_closed (R : Set Formula) (hR : DeductivelyClosed R)
    (L : List Formula) (hL : ∀ B ∈ L, B ∈ R) : package L ∈ R := by
  exact hR (package_from_members L R (fun B hB => .assumption (hL B hB)))

theorem inconsistent_union_package (Q R : Set Formula)
    (hQ : DeductivelyClosed Q) (hR : DeductivelyClosed R)
    (h : Derives (Q ∪ R) falsum) :
    ∃ L : List Formula, (∀ B ∈ L, B ∈ R) ∧ package L ∈ R ∧ neg (package L) ∈ Q := by
  classical
  obtain ⟨D, hD, hsub, hd⟩ := finite_support.mp h
  let E := hD.toFinset.filter (fun B => B ∈ R)
  let L := E.toList
  have hL : ∀ B ∈ L, B ∈ R := by
    intro B hB
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hB)).2
  have hDR : D ⊆ Q ∪ {B | B ∈ L} := by
    intro B hB
    rcases hsub hB with hQ | hR
    · exact Or.inl hQ
    · apply Or.inr
      exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨by simpa using hB, hR⟩)
  have hpackage : Derives (insert (package L) Q) falsum :=
    (package_premises Q L falsum).mp (hd.weaken hDR)
  exact ⟨L, hL, package_mem_closed R hR L hL, hQ (.negIntro hpackage)⟩

end Lemmatheca.ProofTheory.Intuitionistic.IntermediateCanonical
