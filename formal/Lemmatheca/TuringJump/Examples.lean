import Lemmatheca.TuringJump.Degrees

/-! The questions' specified parity oracle and join counterexample. -/
namespace Lemmatheca.Entry.TuringJump

open Lemmatheca.ComputabilityTheory
open OracleProgramNumberings TuringDegrees TuringJump UniversalComputation

noncomputable section

def evenOracle : Set ℕ := Set.range (fun n : ℕ => 2 * n)

theorem even_oracle_computable : ComputablePred (fun n => n ∈ evenOracle) := by
  have he : (fun n => n ∈ evenOracle) = (fun n => n % 2 = 0) := by
    funext n
    apply propext
    change (∃ k, 2 * k = n) ↔ n % 2 = 0
    constructor
    · rintro ⟨k, rfl⟩
      omega
    · intro h
      exact ⟨n / 2, by omega⟩
  rw [he]
  have hp : PrimrecPred (fun n : ℕ => n % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0)
  obtain ⟨d, hd⟩ := hp
  exact ⟨d, hd.to_comp⟩

theorem even_oracle_equiv_empty : Equivalent evenOracle ∅ := by
  exact ⟨(reducible_empty_iff evenOracle).mpr even_oracle_computable,
    zeroDegree_le (degree evenOracle)⟩


theorem halting_join_self :
    Equivalent (join haltingDiagonal haltingDiagonal) haltingDiagonal := by
  exact ⟨(join_reducible_iff _ _ _).mpr ⟨reducible_refl _, reducible_refl _⟩,
    manyOne_imp_reducible ⟨_, (join_even_reduction haltingDiagonal haltingDiagonal).1.to_comp,
      (join_even_reduction haltingDiagonal haltingDiagonal).2⟩⟩

theorem halting_jump_not_join :
    ¬ Equivalent (jump haltingDiagonal) (join haltingDiagonal haltingDiagonal) := by
  intro h
  exact (jump_strict haltingDiagonal).2 (reducible_trans h.1 halting_join_self.1)

end
end Lemmatheca.Entry.TuringJump
