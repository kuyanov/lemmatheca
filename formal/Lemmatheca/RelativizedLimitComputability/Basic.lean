import Lemmatheca.LimitComputability.LimitLemma
import Lemmatheca.BusyBeaverFunctions.FunctionOracles
import Lemmatheca.TuringJump.IndexMaps

namespace Lemmatheca.ComputabilityTheory.RelativizedLimitComputability

open OracleComputation UniversalComputation
open LimitComputability (Approximation)

def JointComputableIn (B : Set ℕ) (a : Approximation) : Prop :=
  PartialComputable B (fun w => Part.some (a w.unpair.1 w.unpair.2))

def ConvergesTo (a : Approximation) (f : ℕ → ℕ) : Prop :=
  ∀ x, ∃ S, ∀ s, S ≤ s → a s x = f x

noncomputable def RelativeLimitComputable (B X : Set ℕ) : Prop :=
  ∃ a, JointComputableIn B a ∧ LimitComputability.Binary a ∧
    ConvergesTo a (indicator X)

def ModulusTo (a : Approximation) (f m : ℕ → ℕ) : Prop :=
  ∀ x s, m x ≤ s → a s x = f x

theorem joint_index_iff (B : Set ℕ) (a : Approximation) :
    JointComputableIn B a ↔ ∃ e, ∀ s x,
      OracleProgramNumberings.phi B e (Nat.pair s x) = Part.some (a s x) := by
  rw [JointComputableIn, OracleProgramNumberings.indexed_complete]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun s x => by simpa using congrFun he (Nat.pair s x)⟩
  · rintro ⟨e, he⟩
    refine ⟨e, funext fun w => ?_⟩
    simpa using he w.unpair.1 w.unpair.2

theorem characteristic_convergence (a : Approximation) (X : Set ℕ) :
    ConvergesTo a (indicator X) ↔ LimitComputability.Converges a X := by
  rfl

theorem finite_prefix_stability (a : Approximation) (f : ℕ → ℕ)
    (ha : ConvergesTo a f) (u : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ x < u, a s x = f x := by
  induction u with
  | zero => exact ⟨0, fun _ _ _ hx => False.elim (Nat.not_lt_zero _ hx)⟩
  | succ u ih =>
      obtain ⟨S, hS⟩ := ih
      obtain ⟨T, hT⟩ := ha u
      refine ⟨max S T, fun s hs x hx => ?_⟩
      by_cases h : x < u
      · exact hS s (by omega) x h
      · have he : x = u := by omega
        subst x
        exact hT s (by omega)

theorem joint_empty_iff (a : Approximation) :
    JointComputableIn ∅ a ↔ Computable₂ a := by
  have hEmpty : ComputablePred (fun q : ℕ => q ∈ (∅ : Set ℕ)) :=
    by
      simpa only [Set.mem_empty_iff_false] using
        (Computable.computablePred (Computable.const false) : ComputablePred (fun _ : ℕ => False))
  rw [JointComputableIn, computable_oracle_iff ∅ hEmpty]
  constructor
  · intro h
    have hcomp : Computable (fun w : ℕ => a w.unpair.1 w.unpair.2) :=
      Partrec.nat_iff.mpr h
    change Computable (fun p : ℕ × ℕ => a p.1 p.2)
    exact (hcomp.comp (Primrec₂.natPair.to_comp)).of_eq (fun _ => by simp)
  · intro h
    exact Partrec.nat_iff.mp
      ((h.comp (Computable.fst.comp Computable.unpair)
        (Computable.snd.comp Computable.unpair)).partrec)

end Lemmatheca.ComputabilityTheory.RelativizedLimitComputability
