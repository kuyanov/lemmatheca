import Lemmatheca.EffectiveEnumerations.Increasing
import Lemmatheca.EffectiveEnumerations.Settling
import Lemmatheca.RicesTheorem.RicesTheorem

namespace Lemmatheca.ComputabilityTheory.FriedbergNumberings

open Encodable Denumerable UniversalComputation EffectiveEnumerations
open Nat.Partrec (Code)

def UniformCE (F : ℕ → Set ℕ) : Prop :=
  REPred (fun z : ℕ => z.unpair.2 ∈ F z.unpair.1)

def FriedbergNumbering (F : ℕ → Set ℕ) : Prop :=
  UniformCE F ∧ Function.Injective F ∧ ∀ e, ∃ n, F n = indexSet e

theorem standard_uniform : UniformCE indexSet := by
  exact (phi_recursive.comp
    (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp).dom_re

theorem standard_repeats : ¬ Function.Injective indexSet := by
  intro h
  have he : indexSet (encode Code.succ) = indexSet (encode Code.left) := by
    ext x
    simp [indexSet, phi, ofNat_encode, Code.eval]
  have hc : Code.succ = Code.left := Encodable.encode_injective (h he)
  cases hc

theorem friedberg_iff_unique_ce (F : ℕ → Set ℕ) :
    FriedbergNumbering F ↔ UniformCE F ∧ ∀ A : Set ℕ, REPred A → ∃! n, F n = A := by
  constructor
  · rintro ⟨hu, hi, hs⟩
    refine ⟨hu, ?_⟩
    intro A hA
    obtain ⟨e, he⟩ := (enumerable_iff_index A).mp hA
    have ha : A = indexSet e := Set.ext he
    obtain ⟨n, hn⟩ := hs e
    have hna : F n = A := hn.trans ha.symm
    exact ⟨n, hna, fun m hm => hi (hm.trans hna.symm)⟩
  · rintro ⟨hu, hs⟩
    have hrow (n : ℕ) : REPred (F n) := by
      have h := hu.comp (Primrec₂.natPair.comp (Primrec.const n) Primrec.id).to_comp
      exact h.of_eq (fun y => by
        dsimp only [id_eq]
        rw [Nat.unpair_pair]
        rfl)
    refine ⟨hu, ?_, ?_⟩
    · intro a b hab
      obtain ⟨n, _, hn⟩ := hs (F a) (hrow a)
      exact (hn a rfl).trans (hn b hab.symm).symm
    · intro e
      have he : REPred (indexSet e) :=
        (enumerable_iff_index _).mpr ⟨e, fun _ => Iff.rfl⟩
      obtain ⟨n, hn, _⟩ := hs (indexSet e) he
      exact ⟨n, hn⟩

theorem initial_segment_classification (A : Set ℕ) :
    IsLowerSet A ↔ A = ∅ ∨ A = Set.univ ∨ ∃ k, A = Set.Iic k := by
  classical
  constructor
  · intro h
    by_cases hall : A = Set.univ
    · exact Or.inr (Or.inl hall)
    have hex : ∃ n, n ∉ A := (Set.ne_univ_iff_exists_notMem A).mp hall
    have hlt (n : ℕ) (hn : n ∈ A) : n < Nat.find hex := by
      by_contra hh
      exact Nat.find_spec hex (h (Nat.le_of_not_gt hh) hn)
    have hmem (n : ℕ) (hn : n < Nat.find hex) : n ∈ A := by
      by_contra hh
      exact Nat.find_min hex hn hh
    cases hc : Nat.find hex with
    | zero =>
      left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have := hlt n hn
      omega
    | succ k =>
      right
      right
      refine ⟨k, ?_⟩
      ext n
      constructor
      · intro hn
        have := hlt n hn
        change n ≤ k
        omega
      · intro hn
        apply hmem n
        change n ≤ k at hn
        omega
  · rintro (rfl | rfl | ⟨k, rfl⟩)
    · intro a b hab hb
      exact False.elim hb
    · intro a b hab hb
      trivial
    · intro a b hab hb
      exact hab.trans hb

theorem noninitial_witness (A : Set ℕ) :
    ¬ IsLowerSet A ↔ ∃ a b, a < b ∧ a ∉ A ∧ b ∈ A := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    intro a b hab hb
    by_cases he : a = b
    · simpa only [he] using hb
    · by_contra ha
      exact hn ⟨b, a, by omega, ha, hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩ h
    exact ha (h hab.le hb)

def visit (s : ℕ) : ℕ := s.unpair.1

theorem fair_visits (e S : ℕ) : ∃ s, S ≤ s ∧ visit s = e := by
  exact ⟨Nat.pair e S, (Nat.le_add_left S e).trans (Nat.add_le_pair e S), by simp [visit]⟩

theorem finite_prefix_stabilization (e b : ℕ) :
    ∃ S, ∀ s, S ≤ s → stage e s ∩ Set.Iic b = indexSet e ∩ Set.Iic b := by
  obtain ⟨S, hS⟩ := prefix_settled_exists (indexSet e) (stage e)
    (stage_monotone e) (stage_union e) (b + 1)
  refine ⟨S, ?_⟩
  intro s hSs
  have ht := settling_persists (indexSet e) (stage e)
    (stage_monotone e) (stage_union e) hS hSs
  ext x
  constructor
  · rintro ⟨hx, hxb⟩
    exact ⟨(ht x (Nat.lt_succ_of_le hxb)).mpr hx, hxb⟩
  · rintro ⟨hx, hxb⟩
    exact ⟨(ht x (Nat.lt_succ_of_le hxb)).mp hx, hxb⟩

end Lemmatheca.ComputabilityTheory.FriedbergNumberings
