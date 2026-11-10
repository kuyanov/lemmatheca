import Lemmatheca.DominationAndHyperimmuneDegrees.Arrays
import Lemmatheca.EffectiveEnumerations.Injective

namespace Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets

open UniversalComputation OracleComputation HyperimmuneDegrees

noncomputable section
open Classical

def deficiency (a : ℕ → ℕ) : Set ℕ := {s | ∃ t, s < t ∧ a t < a s}

def nondeficient (a : ℕ → ℕ) : Set ℕ := (deficiency a)ᶜ

theorem nondeficient_iff_tail (a : ℕ → ℕ) (ha : Function.Injective a) (s : ℕ) :
    s ∈ nondeficient a ↔ ∀ t, s < t → a s < a t := by
  change (¬ ∃ t, s < t ∧ a t < a s) ↔ _
  constructor
  · intro h t hst
    have hn : ¬ a t < a s := fun hlt => h ⟨t, hst, hlt⟩
    have he : a s ≠ a t := fun he => (Nat.ne_of_lt hst) (ha he)
    omega
  · intro h ⟨t, hst, hlt⟩
    exact (Nat.not_lt_of_gt (h t hst)) hlt

theorem bounded_range_membership (a : ℕ → ℕ) (ha : Function.Injective a)
    (s x : ℕ) (hs : s ∈ nondeficient a) (hx : x < a s) :
    x ∈ Set.range a ↔ ∃ i ≤ s, a i = x := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, hi⟩
    by_contra hn
    have hgt := (nondeficient_iff_tail a ha s).mp hs i (by omega)
    omega
  · rintro ⟨i, _, hi⟩
    exact ⟨i, hi⟩

theorem deficiency_ce (a : ℕ → ℕ) (hc : Computable a) : REPred (deficiency a) := by
  apply (enumerable_iff_decidable_certificate (deficiency a)).mpr
  refine ⟨fun s t => s < t ∧ a t < a s, ?_, fun _ => Iff.rfl⟩
  apply Computable.computablePred
  have h1 : Computable (fun p : ℕ × ℕ => decide (p.1 < p.2)) :=
    (Primrec.nat_lt.comp Primrec.fst Primrec.snd).decide.to_comp
  have h2 : Computable (fun p : ℕ × ℕ => decide (a p.2 < a p.1)) :=
    Primrec.nat_lt.decide.to_comp.comp (hc.comp Computable.snd) (hc.comp Computable.fst)
  exact (Primrec.and.to_comp.comp h1 h2).of_eq (fun p => by simp)

theorem nondeficient_arbitrarily_late (a : ℕ → ℕ) (ha : Function.Injective a) (N : ℕ) :
    ∃ s, N ≤ s ∧ s ∈ nondeficient a := by
  have hn : ∃ v, ∃ t, N ≤ t ∧ a t = v := ⟨a N, N, le_rfl, rfl⟩
  obtain ⟨s, hNs, hmin⟩ := Nat.find_spec hn
  refine ⟨s, hNs, (nondeficient_iff_tail a ha s).mpr ?_⟩
  intro t hst
  have hle := Nat.find_min' hn ⟨t, hNs.trans (Nat.le_of_lt hst), rfl⟩
  have he : a s ≠ a t := fun he => (Nat.ne_of_lt hst) (ha he)
  omega

theorem nondeficient_infinite (a : ℕ → ℕ) (ha : Function.Injective a) :
    (nondeficient a).Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  obtain ⟨s, hs, hc⟩ := nondeficient_arbitrarily_late a ha (N + 1)
  exact ⟨s, hc, by omega⟩

theorem nondeficient_values_unbounded (a : ℕ → ℕ) (ha : Function.Injective a) (x : ℕ) :
    ∃ s, s ∈ nondeficient a ∧ x < a s := by
  have hi : (a '' nondeficient a).Infinite :=
    (Set.infinite_image_iff ha.injOn).mpr (nondeficient_infinite a ha)
  obtain ⟨v, hv, hx⟩ := hi.exists_gt x
  obtain ⟨s, hs, rfl⟩ := hv
  exact ⟨s, hs, hx⟩

theorem deficiency_prefix_iff (a : ℕ → ℕ) (ha : Function.Injective a) (s : ℕ) :
    s ∈ deficiency a ↔ ∃ x < a s, x ∈ Set.range a ∧ ∀ i < s, a i ≠ x := by
  constructor
  · rintro ⟨t, hst, hlt⟩
    refine ⟨a t, hlt, ⟨t, rfl⟩, ?_⟩
    intro i his he
    have hi := ha he
    omega
  · rintro ⟨x, hx, ⟨t, ht⟩, hnot⟩
    refine ⟨t, ?_, by omega⟩
    by_contra hn
    by_cases hts : t < s
    · exact hnot t hts ht
    · have he : t = s := by omega
      subst t
      omega

def Hypersimple (S : Set ℕ) : Prop := REPred S ∧ HyperimmuneSet Sᶜ

theorem hypersimple_iff_arrays (S : Set ℕ) :
    Hypersimple S ↔ REPred S ∧ Sᶜ.Infinite ∧
      ∀ d : ℕ → ℕ, StrongArray d → ∃ n, ∀ x ∈ arraySet d n, x ∈ S := by
  unfold Hypersimple
  rw [hyperimmune_iff_no_array]
  constructor
  · rintro ⟨hc, hi, hno⟩
    refine ⟨hc, hi, ?_⟩
    intro d hd
    by_contra h
    apply hno
    refine ⟨d, hd, ?_⟩
    intro n
    have hn : ¬ ∀ x ∈ arraySet d n, x ∈ S := fun hx => h ⟨n, hx⟩
    push Not at hn
    obtain ⟨x, hx, hnx⟩ := hn
    exact ⟨x, hx, hnx⟩
  · rintro ⟨hc, hi, hit⟩
    refine ⟨hc, hi, ?_⟩
    rintro ⟨d, hd, hh⟩
    obtain ⟨n, hn⟩ := hit d hd
    obtain ⟨x, hx, hnx⟩ := hh n
    exact hnx (hn x hx)

theorem hypersimple_simple (S : Set ℕ) (hS : Hypersimple S) : SimpleSets.Simple S := by
  exact ⟨hS.1, hyperimmune_implies_immune Sᶜ hS.2⟩

end
end Lemmatheca.ComputabilityTheory.DekkerDeficiencyAndHypersimpleSets
