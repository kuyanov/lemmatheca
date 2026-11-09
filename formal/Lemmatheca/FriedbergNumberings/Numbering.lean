import Lemmatheca.FriedbergNumberings.Completed

namespace Lemmatheca.ComputabilityTheory.FriedbergNumberings

open UniversalComputation EffectiveEnumerations

def RecognizerIndex (r : ℕ) : Prop :=
  ∀ e y, phi r (Nat.pair e y) = recognizer e y

def compiler (r e : ℕ) : ℕ := specialize r e

theorem recognizer_index_exists : ∃ r, RecognizerIndex r := by
  have hp : Nat.Partrec (fun w : ℕ => recognizer w.unpair.1 w.unpair.2) :=
    Partrec.nat_iff.mp (recognizer_partial.comp (Computable.fst.comp Computable.unpair)
      (Computable.snd.comp Computable.unpair))
  obtain ⟨r, hr⟩ := phi_complete hp
  refine ⟨r, fun e y => ?_⟩
  simpa only [Nat.unpair_pair] using congrFun hr (Nat.pair e y)

theorem compiler_primitive (r : ℕ) : Nat.Primrec (compiler r) := by
  exact Primrec.nat_iff.mp (specialize_primitive.comp (Primrec.const r) Primrec.id)

theorem compiler_evaluation (r : ℕ) (hr : RecognizerIndex r) (e y : ℕ) :
    phi (compiler r e) y = recognizer e y := by
  rw [compiler, specialize_eval, hr e y]

theorem compiler_domain (r : ℕ) (hr : RecognizerIndex r) (e : ℕ) :
    indexSet (compiler r e) = completedRow e := by
  classical
  ext y
  change (phi (compiler r e) y).Dom ↔ y ∈ completedRow e
  rw [compiler_evaluation r hr, recognizer_spec]
  by_cases hy : y ∈ completedRow e <;> simp [hy]

theorem no_reverse_translator :
    ¬ ∃ q : ℕ → ℕ, Computable q ∧ ∀ e, completedRow (q e) = indexSet e := by
  classical
  rintro ⟨q, hc, hq⟩
  obtain ⟨z, hz⟩ := phi_complete (f := fun _ => Part.none) Nat.Partrec.none
  have hempty : indexSet z = ∅ := by
    ext x
    simp [indexSet, hz]
  have heq (e : ℕ) : indexSet e = ∅ ↔ q e = q z := by
    constructor
    · intro h
      apply completed_injective
      rw [hq e, hq z, h, hempty]
    · intro h
      rw [← hq e, h, hq z, hempty]
  have htest : ComputablePred (fun e => q e = q z) :=
    (Primrec.eq.decide.to_comp.comp hc (Computable.const (q z))).computablePred
  have hdec : ComputablePred (fun e => indexSet e = ∅) :=
    htest.of_eq (fun e => (heq e).symm)
  let C : Set RicesTheorem.PartialFunction := {f | ∀ x, ¬ (f x).Dom}
  have hC : RicesTheorem.Nontrivial C := by
    refine ⟨⟨fun _ => Part.none, Nat.Partrec.none, ?_⟩,
      ⟨fun _ => Part.some 0, Nat.Partrec.zero, ?_⟩⟩
    · change ∀ x, ¬ (Part.none : Part ℕ).Dom
      intro x h
      exact h
    · change ¬ ∀ x, ¬ (Part.some 0).Dom
      intro h
      exact h 0 trivial
  have hmem (e : ℕ) : e ∈ RicesTheorem.indexSet C ↔ indexSet e = ∅ := by
    change (∀ x, ¬ (phi e x).Dom) ↔ _
    constructor
    · intro h
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact h
    · intro h x hx
      have : x ∈ indexSet e := hx
      rw [h] at this
      exact this
  exact RicesTheorem.rice_undecidable C hC (hdec.of_eq (fun e => (hmem e).symm))

end Lemmatheca.ComputabilityTheory.FriedbergNumberings
