import Lemmatheca.RelativizedLimitComputability.Theorems
import Lemmatheca.IndexSetCompleteness.Classification
import Lemmatheca.PostsTheorem.Examples
import Lemmatheca.DominationAndHyperimmuneDegrees.Bounds

/-! Highness, its function quantifiers, and the second-jump degree of totality. -/
namespace Lemmatheca.ComputabilityTheory.HighDegreesAndDomination

open UniversalComputation OracleComputation TuringDegrees TuringJump
open LimitComputability (Approximation Binary)
open RelativizedLimitComputability

noncomputable section
set_option backward.isDefEq.respectTransparency false

local notation "TOT" => Lemmatheca.Entry.ArithmeticalHierarchy.Totality

def High (A : Set ℕ) : Prop := Reducible (jump haltingDiagonal) (jump A)

def DominatesComputable (g : ℕ → ℕ) : Prop :=
  ∀ f : ℕ → ℕ, Computable f → Filter.EventuallyLE Filter.atTop f g

def IsTotalityApprox (a : Approximation) : Prop :=
  Binary a ∧ ConvergesTo a (indicator TOT)

theorem totality_complement_maps :
    ManyOneReducible TOTᶜ (jump haltingDiagonal) ∧
      ManyOneReducible (jump haltingDiagonal)ᶜ TOT := by
  have hK := Lemmatheca.Entry.PostsTheorem.halting_jump_levels.1
  have hT := IndexSetCompleteness.totality_complete
  exact ⟨hK.2 TOTᶜ ((ArithmeticalHierarchy.level_complement ∅ 2 false TOT).mp hT.1),
    hT.2 (jump haltingDiagonal)ᶜ
      ((ArithmeticalHierarchy.level_complement ∅ 2 true (jump haltingDiagonal)).mp hK.1)⟩

theorem totality_jump_equivalence : Equivalent TOT (jump haltingDiagonal) := by
  obtain ⟨hT, hK⟩ := totality_complement_maps
  exact ⟨reducible_trans (complement_equivalent TOT).1 (manyOne_imp_reducible hT),
    reducible_trans (complement_equivalent (jump haltingDiagonal)).1 (manyOne_imp_reducible hK)⟩

theorem high_totality_approximation (A : Set ℕ) (hA : High A) :
    ∃ (a : Approximation) (c : ℕ), IsTotalityApprox a ∧
      ∀ s e, OracleProgramNumberings.phi A c (Nat.pair s e) = Part.some (a s e) := by
  have hT : Reducible TOT (jump A) := reducible_trans totality_jump_equivalence.1 hA
  obtain ⟨a, ⟨c, hc⟩, hb, hconv⟩ := (relative_set_limit A TOT).mpr hT
  refine ⟨a, OracleProgramNumberings.encodeCode c, ⟨hb, hconv⟩, ?_⟩
  intro s e
  simpa only [OracleProgramNumberings.phi, OracleProgramNumberings.decode_encode, Nat.unpair_pair]
    using congrFun hc (Nat.pair s e)

end
end Lemmatheca.ComputabilityTheory.HighDegreesAndDomination
