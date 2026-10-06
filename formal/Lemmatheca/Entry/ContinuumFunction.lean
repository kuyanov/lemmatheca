import Lemmatheca.SetTheory.ContinuumFunction
import Mathlib.Tactic

/-! Particular examples and counterexamples for the human entry. -/

set_option autoImplicit false
universe u
namespace Lemmatheca.Entry.ContinuumFunction
open Lemmatheca.SetTheory.ContinuumFunction
open Order
open scoped Cardinal Ordinal

/-- The two Hausdorff–Tarski exercises at aleph omega. -/
theorem reduction_examples :
    (Cardinal.aleph (ω : Ordinal.{u}) ≤ 2 ^ (ℵ₀ : Cardinal.{u}) →
      Cardinal.aleph (ω : Ordinal.{u}) ^ ℵ₀ = 2 ^ (ℵ₀ : Cardinal.{u})) ∧
    ((∀ μ < Cardinal.aleph (ω : Ordinal.{u}), μ ^ Cardinal.aleph 1 < Cardinal.aleph ω) →
      Cardinal.aleph (ω : Ordinal.{u}) ^ Cardinal.aleph 1 = Cardinal.aleph ω ^ ℵ₀) := by
  have hcof : (Cardinal.aleph (ω : Ordinal.{u})).ord.cof = ℵ₀ := by
    rw [Cardinal.ord_aleph, Ordinal.cof_omega Ordinal.isSuccLimit_omega0, Ordinal.cof_omega0]
  constructor
  · intro h
    exact large_exponents _ _ le_rfl
      (Cardinal.natCast_le_aleph0.trans (Cardinal.aleph0_le_aleph _)) h
  · intro h
    simpa only [hcof] using power_at_cofinality _ _ (Cardinal.aleph0_le_aleph _)
      (Cardinal.aleph0_le_aleph _) h (hcof ▸ Cardinal.aleph0_le_aleph 1)

/-- The three sample GCH powers. -/
theorem gch_examples (h : GCH.{u}) :
    (Cardinal.aleph 1 : Cardinal.{u}) ^ ℵ₀ = Cardinal.aleph 1 ∧
    Cardinal.aleph (ω : Ordinal.{u}) ^ ℵ₀ = Cardinal.aleph (ω + 1) ∧
    (Cardinal.aleph 2 : Cardinal.{u}) ^ Cardinal.aleph 3 = Cardinal.aleph 4 := by
  have hcof1 : (Cardinal.aleph 1 : Cardinal.{u}).ord.cof = Cardinal.aleph 1 := by
    rw [Cardinal.ord_aleph, Cardinal.cof_omega_one]
  have hcofω : (Cardinal.aleph (ω : Ordinal.{u})).ord.cof = ℵ₀ := by
    rw [Cardinal.ord_aleph, Ordinal.cof_omega Ordinal.isSuccLimit_omega0, Ordinal.cof_omega0]
  have h01 : (ℵ₀ : Cardinal.{u}) < Cardinal.aleph 1 := Cardinal.aleph0_lt_aleph_one
  have h0ω : (ℵ₀ : Cardinal.{u}) < Cardinal.aleph ω := by
    simpa only [Cardinal.aleph_zero] using Cardinal.aleph.strictMono Ordinal.omega0_pos
  have h23 : (Cardinal.aleph 2 : Cardinal.{u}) < Cardinal.aleph 3 :=
    Cardinal.aleph.strictMono (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [not_le_of_gt h01, ite_false, hcof1, h01, ite_true] using
      gch_powers h (Cardinal.aleph 1) ℵ₀ (Cardinal.aleph0_le_aleph 1) le_rfl
  · simpa only [not_le_of_gt h0ω, ite_false, hcofω, lt_self_iff_false,
      Cardinal.succ_aleph] using
      gch_powers h (Cardinal.aleph ω) ℵ₀ (Cardinal.aleph0_le_aleph ω) le_rfl
  · simpa only [h23.le, ite_true, Cardinal.succ_aleph,
      show (3 : Ordinal.{u}) + 1 = 4 by norm_num] using
      gch_powers h (Cardinal.aleph 2) (Cardinal.aleph 3)
        (Cardinal.aleph0_le_aleph 2) (Cardinal.aleph0_le_aleph 3)

end Lemmatheca.Entry.ContinuumFunction
