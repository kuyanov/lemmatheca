import Lemmatheca.BusyBeaverFunctions.Bounds

/-! Program-size Busy Beaver growth, with a specified binary constant compiler. -/
namespace Lemmatheca.ComputabilityTheory.BusyBeaverFunctions

open UniversalComputation
open Nat.Partrec (Code)

set_option backward.isDefEq.respectTransparency false

noncomputable section

theorem output_eventually_dominates {f : ℕ → ℕ} (hf : Computable f) :
    ∃ N, ∀ n, N ≤ n → f n < outputMaximum n := by
  obtain ⟨p, hp⟩ := Code.exists_code.mp
    (Partrec.nat_iff.mp (Computable.succ.comp hf).partrec)
  obtain ⟨N, hN⟩ := eventual_binary_budget (nodeSize p + 2) constantOverhead
  refine ⟨N, ?_⟩
  intro n hn
  let q := Code.comp p (binaryConstant n)
  have hsize : nodeSize q ≤ n := by
    have hc := binaryConstant_size n
    have hb := hN n hn
    change 1 + nodeSize p + nodeSize (binaryConstant n) ≤ n
    omega
  have hy : f n + 1 ∈ Code.eval q 0 := by
    change f n + 1 ∈ (Code.eval (binaryConstant n) 0).bind (Code.eval p)
    rw [binaryConstant_eval, Part.bind_some, hp]
    exact Part.mem_some _
  have hb := (outputMaximum_le_iff n (outputMaximum n)).mp le_rfl q hsize _ hy
  omega

theorem no_computable_output_upper_bound :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧ ∃ N, ∀ n, N ≤ n → outputMaximum n ≤ g n := by
  rintro ⟨g, hg, N, hN⟩
  obtain ⟨M, hM⟩ := output_eventually_dominates hg
  have hupper := hN (max N M) (le_max_left _ _)
  have hlower := hM (max N M) (le_max_right _ _)
  omega

theorem outputMaximum_not_computable : ¬ Computable outputMaximum := by
  intro h
  exact no_computable_output_upper_bound ⟨outputMaximum, h, 0, fun _ _ => le_rfl⟩

theorem no_computable_final_stage :
    ¬ ∃ t : ℕ → ℕ, Computable t ∧ ∀ n, outputStage (t n) n = outputMaximum n := by
  rintro ⟨t, ht, he⟩
  have h := stages_computable.1.comp ht Computable.id
  exact outputMaximum_not_computable (h.of_eq he)

end
end Lemmatheca.ComputabilityTheory.BusyBeaverFunctions
