import Lemmatheca.RiceShapiroTheorem.SelfReference

/-! The effective family of positive finite graph certificates and its direct search converse. -/
namespace Lemmatheca.ComputabilityTheory.RiceShapiroTheorem

open UniversalComputation
open RicesTheorem (Extensional)

noncomputable section
open Classical

def IsEffectiveBasis (A B : Set ℕ) : Prop :=
  REPred (fun d => d ∈ B) ∧ (∀ d ∈ B, Valid d) ∧
    ∀ e, e ∈ A ↔ ∃ d ∈ B, GraphInclusion (fragment d) (phi e)

def HasEffectiveBasis (A : Set ℕ) : Prop := ∃ B, IsEffectiveBasis A B

def canonicalBasis (A : Set ℕ) : Set ℕ := {d | Valid d ∧ fragmentIndex d ∈ A}

theorem canonicalBasis_enumerable (A : Set ℕ) (hA : REPred (fun e => e ∈ A)) :
    REPred (fun d => d ∈ canonicalBasis A) := by
  exact enumerable_inter valid_primitive.computablePred.to_re
    (enumerable_preimage hA fragmentIndex_primitive.to_comp)

theorem canonicalBasis_correct (A : Set ℕ) (hA : REPred (fun e => e ∈ A))
    (hext : Extensional A) : IsEffectiveBasis A (canonicalBasis A) := by
  obtain ⟨r, hr⟩ := (enumerable_iff_index (fun e => e ∈ A)).mp hA
  have hAr : A = W r := Set.ext hr
  subst A
  refine ⟨canonicalBasis_enumerable _ hA, fun d hd => hd.1, ?_⟩
  intro e
  constructor
  · intro he
    obtain ⟨hj, hje, t, _, hfin, _⟩ := finite_accepted_subfunction r e hext he
    obtain ⟨d, hd, hdf⟩ := finite_graph_has_code _ hfin
    have hphi : phi (fragmentIndex d) = phi (cutoffIndex r e) := by
      funext x
      rw [fragmentIndex_eval, hdf]
    refine ⟨d, ⟨hd, (hext _ _ hphi).mpr hj⟩, ?_⟩
    rw [hdf]
    exact hje
  · rintro ⟨d, hd, hde⟩
    apply upward_closure r (fragmentIndex d) e hext hd.2
    intro x y hy
    apply hde x y
    simpa only [fragmentIndex_eval] using hy

/-- A code w unpairs to (fragment code, enumeration stage, common computation bound). -/
def basisOffer (r e w : ℕ) : Option ℕ :=
  let d := w.unpair.1
  let s := w.unpair.2.unpair.1
  let t := w.unpair.2.unpair.2
  if Valid d ∧ d ∈ EffectiveEnumerations.stage r s ∧ Match e d t then some 0 else none

def basisSearch (r e : ℕ) : Part ℕ := Nat.rfindOpt (basisOffer r e)

theorem basis_offer_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => basisOffer p.1.1 p.1.2 p.2) := by
  have hu : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2.unpair) :=
    Primrec.unpair.comp Primrec.snd
  have hd := Primrec.fst.comp hu
  have hv := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hs := Primrec.fst.comp hv
  have ht := Primrec.snd.comp hv
  have hr : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have he : Primrec (fun p : (ℕ × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.ite ((valid_primitive.comp hd).and
    ((EffectiveEnumerations.stage_predicate_primitive.comp ((hr.pair hs).pair hd)).and
      (match_primitive.comp ((he.pair hd).pair ht))))
    (Primrec.const (some 0)) (Primrec.const none)

theorem basis_search_partial : Partrec₂ basisSearch := by
  exact Partrec.rfindOpt basis_offer_primitive.to_comp

theorem basis_search_correct (A B : Set ℕ) (r : ℕ)
    (hB : IsEffectiveBasis A B) (hr : B = W r) (e : ℕ) :
    (basisSearch r e).Dom ↔ e ∈ A := by
  rw [basisSearch, Nat.rfindOpt_dom]
  constructor
  · rintro ⟨w, z, hw⟩
    have hc : Valid w.unpair.1 ∧
        w.unpair.1 ∈ EffectiveEnumerations.stage r w.unpair.2.unpair.1 ∧
        Match e w.unpair.1 w.unpair.2.unpair.2 := by
      by_contra hn
      simp [basisOffer, hn] at hw
    apply (hB.2.2 e).mpr
    refine ⟨w.unpair.1, ?_, (match_iff e _ hc.1).mpr ⟨_, hc.2.2⟩⟩
    rw [hr]
    exact (EffectiveEnumerations.stage_union r _).mpr ⟨_, hc.2.1⟩
  · intro he
    obtain ⟨d, hd, hde⟩ := (hB.2.2 e).mp he
    have hv := hB.2.1 d hd
    obtain ⟨s, hs⟩ := (EffectiveEnumerations.stage_union r d).mp (show d ∈ W r from by rwa [← hr])
    obtain ⟨t, ht⟩ := (match_iff e d hv).mp hde
    exact ⟨Nat.pair d (Nat.pair s t), 0, by simp [basisOffer, hv, hs, ht]⟩

theorem effectiveBasis_extensional (A B : Set ℕ) (hB : IsEffectiveBasis A B) :
    Extensional A := by
  intro e d heq
  rw [hB.2.2 e, hB.2.2 d, heq]

theorem rice_shapiro (A : Set ℕ) :
    (REPred (fun e => e ∈ A) ∧ Extensional A) ↔ HasEffectiveBasis A := by
  constructor
  · rintro ⟨hA, hext⟩
    exact ⟨canonicalBasis A, canonicalBasis_correct A hA hext⟩
  · rintro ⟨B, hB⟩
    obtain ⟨r, hr⟩ := (enumerable_iff_index (fun d => d ∈ B)).mp hB.1
    have hBr : B = W r := Set.ext hr
    have hp : Partrec (basisSearch r) :=
      basis_search_partial.comp (Computable.const r) Computable.id
    exact ⟨hp.dom_re.of_eq (basis_search_correct A B r hB hBr),
      effectiveBasis_extensional A B hB⟩

theorem trivial_bases :
    IsEffectiveBasis ∅ ∅ ∧ IsEffectiveBasis Set.univ {pairListCode []} := by
  constructor
  · refine ⟨?_, by simp, ?_⟩
    · exact (Partrec.none : Partrec (fun _ : ℕ => (Part.none : Part ℕ))).dom_re.of_eq
        (fun _ => by simp)
    · intro e
      simp
  · refine ⟨?_, ?_, ?_⟩
    · exact (Primrec.eq.comp Primrec.id (Primrec.const (pairListCode []))).computablePred.to_re
    · intro d hd
      have he : d = pairListCode [] := Set.mem_singleton_iff.mp hd
      rw [he]
      exact empty_fragment.1
    · intro e
      refine ⟨fun _ => ⟨pairListCode [], Set.mem_singleton _, ?_⟩, fun _ => Set.mem_univ _⟩
      rw [empty_fragment.2]
      intro x y hy
      exact (Part.notMem_none _ hy).elim

end
end Lemmatheca.ComputabilityTheory.RiceShapiroTheorem
