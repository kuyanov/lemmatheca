import Lemmatheca.IncomparableTuringDegrees.Prefixes
import Lemmatheca.EffectiveEnumerations.Stages
import Lemmatheca.OracleComputation.Closure
import Lemmatheca.TuringJump.Recoding
import Lemmatheca.TuringDegrees.Joins

/-! Finite-word requirements and effective meet-or-avoid genericity. Definitions and the meet-or-avoid equivalences. -/
namespace Lemmatheca.ComputabilityTheory.OneGenericSets

open OracleComputation OracleProgramNumberings IncomparableTuringDegrees
  ComputableTreesAndPaths PostsTheorem UniversalComputation

noncomputable section

/-- Canonical binary code even when the supplied numerical list has nonbinary entries. -/
def normalize (u : ℕ) : ℕ := FiniteSequenceCoding.code (word u)

def wordSet (e : ℕ) : Set ℕ := {u | ValidCode u ∧ u ∈ EffectiveEnumerations.indexSet e}

def Meets (G S : Set ℕ) : Prop := ∃ u, ValidCode u ∧ Realizes u G ∧ u ∈ S

def Avoids (u : ℕ) (S : Set ℕ) : Prop :=
  ∀ v, ValidCode v → Prefix u v → v ∉ S

def Dense (S : Set ℕ) : Prop :=
  ∀ u, ValidCode u → ∃ v, ValidCode v ∧ Prefix u v ∧ v ∈ S

def densification (S : Set ℕ) : Set ℕ :=
  {u | ValidCode u ∧ (u ∈ S ∨ Avoids u S)}

def IsOneGeneric (G : Set ℕ) : Prop :=
  ∀ e, Meets G (wordSet e) ∨
    ∃ u, ValidCode u ∧ Realizes u G ∧ Avoids u (wordSet e)

theorem normalize_primitive : Primrec normalize := by
  have hm := Primrec.list_map (Primrec.ofNat (List ℕ))
    (Primrec.nat_mod.comp₂ Primrec₂.right (Primrec₂.const 2))
  exact (Primrec.encode.comp hm).of_eq (fun _ => rfl)

theorem normalize_spec (u : ℕ) :
    ValidCode (normalize u) ∧ word (normalize u) = word u ∧
      wordLength (normalize u) = wordLength u := by
  have hb := (word_interpretation u 0).1
  refine ⟨?_, binary_word_recovery (word u) hb, ?_⟩
  · change BinaryWord (FiniteSequenceCoding.decode (FiniteSequenceCoding.code (word u)))
    rw [FiniteSequenceCoding.decode_code]
    exact hb
  · simp [normalize, wordLength, FiniteSequenceCoding.length, word]

theorem normalize_valid (u : ℕ) (hu : ValidCode u) : normalize u = u := by
  rw [normalize, valid_code_interpretation u hu, FiniteSequenceCoding.code_decode]

theorem word_set_enumerable (e : ℕ) : REPred (fun u => u ∈ wordSet e) := by
  have hi : REPred (fun u => u ∈ EffectiveEnumerations.indexSet e) :=
    (enumerable_iff_index _).mpr ⟨e, fun _ => Iff.rfl⟩
  exact enumerable_inter valid_code_primitive.computablePred.to_re hi

theorem generic_iff_enumerable_collections (G : Set ℕ) :
    IsOneGeneric G ↔ ∀ S : Set ℕ, REPred (fun u => u ∈ S) →
      (∀ u ∈ S, ValidCode u) →
      Meets G S ∨ ∃ u, ValidCode u ∧ Realizes u G ∧ Avoids u S := by
  constructor
  · intro hG S hS hvalid
    obtain ⟨e, he⟩ := (enumerable_iff_index _).mp hS
    have hEq : wordSet e = S := by
      ext u
      constructor
      · intro hu
        exact (he u).mpr hu.2
      · intro hu
        exact ⟨hvalid u hu, (he u).mp hu⟩
    simpa only [hEq] using hG e
  · intro hG e
    exact hG (wordSet e) (word_set_enumerable e) (fun _ hu => hu.1)

theorem densification_dense (S : Set ℕ) : Dense (densification S) := by
  classical
  intro u hu
  by_cases h : ∃ v, ValidCode v ∧ Prefix u v ∧ v ∈ S
  · obtain ⟨v, hv, huv, hS⟩ := h
    exact ⟨v, hv, huv, hv, Or.inl hS⟩
  · refine ⟨u, hu, prefix_refl u, hu, Or.inr ?_⟩
    intro v hv huv hS
    exact h ⟨v, hv, huv, hS⟩

theorem generic_iff_dense_completions (G : Set ℕ) :
    IsOneGeneric G ↔ ∀ e, Meets G (densification (wordSet e)) := by
  constructor
  · intro hG e
    rcases hG e with ⟨u, hu, hr, hS⟩ | ⟨u, hu, hr, ha⟩
    · exact ⟨u, hu, hr, hu, Or.inl hS⟩
    · exact ⟨u, hu, hr, hu, Or.inr ha⟩
  · intro hG e
    obtain ⟨u, hu, hr, _, hS | ha⟩ := hG e
    · exact Or.inl ⟨u, hu, hr, hS⟩
    · exact Or.inr ⟨u, hu, hr, ha⟩

end
end Lemmatheca.ComputabilityTheory.OneGenericSets
