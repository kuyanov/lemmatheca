import Lemmatheca.OracleProgramNumberings.Schemes
import Lemmatheca.OracleProgramNumberings.Parameters

/-! One actual bounded-code search, chosen before all oracles. -/
namespace Lemmatheca.ComputabilityTheory.OracleProgramNumberings

open OracleComputation

set_option backward.isDefEq.respectTransparency false

def predecessorCode : Code :=
  .comp (.prec .zero (.comp .left .right)) (.pair .zero identityCode)

noncomputable def allowanceTest : Code :=
  .comp (embed zeroTest) (.comp boundedCode (.pair .right .left))

noncomputable def allowanceSearch : Code :=
  .comp (.find' allowanceTest) (.pair identityCode .zero)

noncomputable def universalCode : Code :=
  .comp predecessorCode (.comp boundedCode (.pair allowanceSearch identityCode))

noncomputable def firstAllowance (A : Set ℕ) (e x : ℕ) : Part ℕ :=
  Nat.rfind (fun k => Part.some (decide (0 < boundedValue A k e x)))

theorem predecessor_eval (A : Set ℕ) (x : ℕ) :
    eval A predecessorCode x = Part.some (x - 1) := by
  have hr (n : ℕ) : eval A (.prec .zero (.comp .left .right)) (Nat.pair 0 n) =
      Part.some (n - 1) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [eval_prec_succ, ih]
      simp [eval]
  change ((Part.some 0).bind fun u => (eval A identityCode x).map (Nat.pair u)).bind
    (eval A (.prec .zero (.comp .left .right))) = _
  rw [identity_eval]
  simpa only [Part.map_some, Part.bind_some] using hr x

private theorem allowance_test_eval (A : Set ℕ) (e x k : ℕ) :
    eval A allowanceTest (Nat.pair (Nat.pair e x) k) =
      Part.some (if boundedValue A k e x = 0 then 1 else 0) := by
  simp only [allowanceTest, eval, Nat.unpair_pair, Part.bind_some, Part.map_some,
    bounded_code_eval, eval_embed, zeroTest_eval]

theorem allowance_search_eval (A : Set ℕ) (e x : ℕ) :
    eval A allowanceSearch (Nat.pair e x) = firstAllowance A e x := by
  simp only [allowanceSearch, eval, identity_eval, Part.map_some, Part.bind_some,
    Nat.unpair_pair, Nat.add_zero, allowance_test_eval, Part.map_some]
  change (Nat.rfind (fun k => Part.some (decide
    ((if boundedValue A k e x = 0 then 1 else 0) = 0)))).map (fun j => j) = _
  rw [Part.map_id' (fun _ => rfl)]
  congr 1
  funext k
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  split <;> omega

private theorem output_certificate (A : Set ℕ) (e x y : ℕ) :
    y ∈ phi A e x ↔ ∃ k, boundedValue A k e x = y + 1 := by
  simp only [phi, bounded_complete, boundedValue_output]

private theorem allowance_positive (A : Set ℕ) (e x k : ℕ)
    (hk : k ∈ firstAllowance A e x) : 0 < boundedValue A k e x := by
  have ht := Nat.rfind_spec hk
  exact of_decide_eq_true (Part.mem_some_iff.mp ht).symm

private theorem allowance_dom (A : Set ℕ) (e x : ℕ) :
    (firstAllowance A e x).Dom ↔ ∃ k, 0 < boundedValue A k e x := by
  unfold firstAllowance
  rw [Nat.rfind_dom]
  simp

private theorem universal_map (A : Set ℕ) (e x : ℕ) :
    eval A universalCode (Nat.pair e x) =
      (firstAllowance A e x).map (fun k => boundedValue A k e x - 1) := by
  change (((eval A allowanceSearch (Nat.pair e x)).bind fun u =>
    (eval A identityCode (Nat.pair e x)).map (Nat.pair u)).bind
      (eval A boundedCode)).bind (eval A predecessorCode) = _
  rw [identity_eval, allowance_search_eval]
  simp only [Part.map_some, Part.bind_map, bounded_code_eval,
    predecessor_eval, Part.bind_some_eq_map]

theorem universal_code_eval (A : Set ℕ) (e x : ℕ) :
    eval A universalCode (Nat.pair e x) = phi A e x := by
  rw [universal_map]
  apply Part.ext
  intro y
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hp := allowance_positive A e x k hk
    exact (output_certificate A e x _).mpr ⟨k, by omega⟩
  · intro hy
    obtain ⟨k, hk⟩ := (output_certificate A e x y).mp hy
    have hd : (firstAllowance A e x).Dom := (allowance_dom A e x).mpr ⟨k, by omega⟩
    obtain ⟨j, hj⟩ := Part.dom_iff_mem.mp hd
    have hp := allowance_positive A e x j hj
    have hv := (output_certificate A e x (boundedValue A j e x - 1)).mpr ⟨j, by omega⟩
    exact ⟨j, hj, Part.mem_unique hv hy⟩

theorem phi_output_certificate (A : Set ℕ) (e x y : ℕ) :
    y ∈ phi A e x ↔ ∃ k, boundedValue A k e x = y + 1 := output_certificate A e x y

theorem phi_domain_certificate (A : Set ℕ) (e x : ℕ) :
    (phi A e x).Dom ↔ ∃ k, 0 < boundedValue A k e x := by
  rw [Part.dom_iff_mem]
  simp only [phi_output_certificate]
  constructor
  · rintro ⟨y, k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨boundedValue A k e x - 1, k, by omega⟩

end Lemmatheca.ComputabilityTheory.OracleProgramNumberings
