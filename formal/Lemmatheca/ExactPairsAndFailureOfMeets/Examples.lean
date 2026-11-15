import Lemmatheca.ExactPairsAndFailureOfMeets.Degrees
import Lemmatheca.TuringJump.Degrees

/-! Actual jump-family input and protected-column output. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs
noncomputable section

def jumpFamily : ℕ → Set ℕ := TuringJump.iterate ∅

def jumpLeft : Set ℕ := leftSet jumpFamily

def jumpRight : Set ℕ := rightSet jumpFamily

theorem jump_pair_exact :
    ExactPair (TuringJump.degreeIterate TuringDegrees.zeroDegree)
      (TuringDegrees.degree jumpLeft) (TuringDegrees.degree jumpRight) := by
  have h := constructed_degree_exact_pair jumpFamily
    (fun n => (TuringJump.iterate_strict ∅ (Nat.lt_succ_self n)).1)
  have heq : (fun n => TuringDegrees.degree (jumpFamily n)) =
      TuringJump.degreeIterate TuringDegrees.zeroDegree := by
    funext n
    exact (TuringJump.iterate_degree ∅ n).symm
  rwa [heq] at h

theorem jump_pair_no_glb :
    ¬ ∃ d, IsGLB ({TuringDegrees.degree jumpLeft, TuringDegrees.degree jumpRight} :
      Set TuringDegrees.Degree) d := by
  exact exact_pair_no_glb _
    (fun n => TuringJump.degree_iterate_strict _ (Nat.lt_succ_self n)) _ _ jump_pair_exact

theorem jump_pair_incomparable :
    ¬ TuringDegrees.degree jumpLeft ≤ TuringDegrees.degree jumpRight ∧
      ¬ TuringDegrees.degree jumpRight ≤ TuringDegrees.degree jumpLeft := by
  exact no_glb_incomparable _ _ jump_pair_no_glb
end
end Lemmatheca.ComputabilityTheory.ExactPairs
