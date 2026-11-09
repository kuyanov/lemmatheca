import Lemmatheca.HigherLevelCompleteSetIsomorphisms.Hierarchy
import Lemmatheca.IndexSetCompleteness.Classification
import Lemmatheca.MyhillsIsomorphismTheorem.Examples

/-! A concrete positive-level application and the level-zero boundary. -/
namespace Lemmatheca.Entry.HigherLevelCompleteSetIsomorphisms

open Lemmatheca.ComputabilityTheory
open HigherCompleteIsomorphism ArithmeticalHierarchy PostsTheorem Myhill

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- The exact common decider map used for both finite targets. -/
def zeroLevelMap (D : Set ℕ) (x : ℕ) : ℕ := if x ∈ D then 0 else 2

theorem zero_level_map_spec (D : Set ℕ) (hD : ComputablePred D) :
    Computable (zeroLevelMap D) ∧
      (∀ x, x ∈ D ↔ zeroLevelMap D x ∈ ({0, 1} : Set ℕ)) ∧
      ∀ x, x ∈ D ↔ zeroLevelMap D x ∈ ({0} : Set ℕ) := by
  refine ⟨ComputablePred.ite (Computable.const 0) (Computable.const 2) hD, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ D <;> simp [zeroLevelMap, hx]
  · intro x
    by_cases hx : x ∈ D <;> simp [zeroLevelMap, hx]

theorem zero_complete_sets :
    SigmaComplete ∅ 0 ({0, 1} : Set ℕ) ∧ SigmaComplete ∅ 0 ({0} : Set ℕ) := by
  have hz (S : Set ℕ) : Sigma ∅ 0 S ↔ ComputablePred S :=
    (level_zero_iff ∅ true S).trans
      ((TuringJump.relative_decidable_iff_reducible ∅ S).trans
        (TuringDegrees.reducible_empty_iff S))
  have htwo : ComputablePred ({0, 1} : Set ℕ) := by
    apply (Primrec.nat_le.comp Primrec.id (Primrec.const 1)).computablePred.of_eq
    intro x
    change x ≤ 1 ↔ x = 0 ∨ x = 1
    omega
  have hone : ComputablePred ({0} : Set ℕ) := by
    apply (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred.of_eq
    intro x
    change x = 0 ↔ x = 0
    rfl
  constructor
  · refine ⟨(hz _).mpr htwo, fun D hD => ?_⟩
    have hm := zero_level_map_spec D ((hz D).mp hD)
    exact ⟨zeroLevelMap D, hm.1, hm.2.1⟩
  · refine ⟨(hz _).mpr hone, fun D hD => ?_⟩
    have hm := zero_level_map_spec D ((hz D).mp hD)
    exact ⟨zeroLevelMap D, hm.1, hm.2.2⟩

theorem finite_no_injection :
    ¬ ∃ f : ℕ → ℕ, Function.Injective f ∧
      ∀ x, x ∈ ({0, 1} : Set ℕ) ↔ f x ∈ ({0} : Set ℕ) := by
  rintro ⟨f, hf, hm⟩
  have hzero : f 0 = 0 := by simpa using (hm 0).mp (by simp)
  have hone : f 1 = 0 := by simpa using (hm 1).mp (by simp)
  have hbad := hf (hzero.trans hone.symm)
  norm_num at hbad

theorem totality_infinitude_maps :
    ∃ P Q : ℕ → ℕ,
      IsomorphismPair Lemmatheca.Entry.ArithmeticalHierarchy.Totality IndexSetCompleteness.Infinitude P Q := by
  obtain ⟨P_H, Q_H, P_D, Q_D, _, _, hp⟩ :=
    pi_class_maps (B := ∅) (n := 2) (by decide)
      IndexSetCompleteness.totality_complete IndexSetCompleteness.infinitude_complete
  exact ⟨Q_D ∘ P_H, Q_H ∘ P_D, hp⟩

end
end Lemmatheca.Entry.HigherLevelCompleteSetIsomorphisms
