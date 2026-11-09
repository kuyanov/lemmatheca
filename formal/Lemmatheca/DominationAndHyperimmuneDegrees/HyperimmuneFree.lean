import Lemmatheca.DominationAndHyperimmuneDegrees.Approximation
import Lemmatheca.TruthTableAndWeakTruthTableReductions.Characterization

/-! Computable bounds on the actual successful evaluation allowance give truth tables. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneDegrees

open OracleComputation TuringDegrees UniversalComputation
open OracleProgramNumberings StrongReductions

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- No oracle occurs in this program family before evaluation. -/
def allowanceProgram (e : ℕ) : Code :=
  .comp allowanceSearch (.pair (constantCode e) identityCode)

/-- A natural-valued version of the existing partial firstAllowance on a supplied total index. -/
def leastAllowance (A : Set ℕ) (e : ℕ) (ht : ∀ x, (phi A e x).Dom) (x : ℕ) : ℕ :=
  Nat.find ((phi_domain_certificate A e x).mp (ht x))

theorem allowance_program_partial_eval (A : Set ℕ) (e x : ℕ) :
    eval A (allowanceProgram e) x = firstAllowance A e x := by
  simp [allowanceProgram, eval, constant_eval, identity_eval, allowance_search_eval]

theorem least_allowance_spec (A : Set ℕ) (e : ℕ) (ht : ∀ x, (phi A e x).Dom) (x : ℕ) :
    0 < boundedValue A (leastAllowance A e ht x) e x ∧
      ∀ k, k < leastAllowance A e ht x → ¬ 0 < boundedValue A k e x := by
  exact ⟨Nat.find_spec ((phi_domain_certificate A e x).mp (ht x)),
    fun k hk => Nat.find_min ((phi_domain_certificate A e x).mp (ht x)) hk⟩

theorem allowance_program_eval (A : Set ℕ) (e : ℕ) (ht : ∀ x, (phi A e x).Dom) (x : ℕ) :
    eval A (allowanceProgram e) x = Part.some (leastAllowance A e ht x) := by
  rw [allowance_program_partial_eval]
  apply Part.eq_some_iff.mpr
  simpa [firstAllowance, Nat.mem_rfind] using least_allowance_spec A e ht x

theorem least_allowance_relative (A : Set ℕ) (e : ℕ) (ht : ∀ x, (phi A e x).Dom) :
    PartialComputable A (fun x => Part.some (leastAllowance A e ht x)) := by
  exact ⟨allowanceProgram e, funext (allowance_program_eval A e ht)⟩

theorem bounded_after_least (A : Set ℕ) (e : ℕ) (ht : ∀ x, (phi A e x).Dom)
    (x y k : ℕ) (hy : y ∈ phi A e x) (hk : leastAllowance A e ht x ≤ k) :
    boundedValue A k e x = y + 1 := by
  let u := leastAllowance A e ht x
  have hp : 0 < boundedValue A u e x := (least_allowance_spec A e ht x).1
  obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  have hvphi := (phi_output_certificate A e x v).mpr ⟨u, hv⟩
  have heq : v = y := Part.mem_unique hvphi hy
  have hu : boundedValue A u e x = y + 1 := by simpa [heq] using hv
  have hm := bounded_monotone (indicator A) u (k - u) (decodeCode e) x y
    ((boundedValue_output A u e x y).mp hu)
  apply (boundedValue_output A k e x y).mpr
  change boundedQ (indicator A) k (decodeCode e) x = some y
  have hku : u ≤ k := hk
  have he : u + (k - u) = k := Nat.add_sub_of_le hku
  rw [he] at hm
  exact hm

theorem hyperimmune_free_allowance_bound (A : Set ℕ) (hA : HyperimmuneFree A)
    (e : ℕ) (ht : ∀ x, (phi A e x).Dom) :
    ∃ h : ℕ → ℕ, Computable h ∧ Majorizes h (leastAllowance A e ht) ∧
      ∀ x y, y ∈ phi A e x → boundedValue A (h x) e x = y + 1 := by
  obtain ⟨h, hh, hb⟩ := (computable_bounds_equivalent (leastAllowance A e ht)).mp
    (hA _ (least_allowance_relative A e ht))
  exact ⟨h, hh, hb, fun x y hy => bounded_after_least A e ht x y (h x) hy (hb x)⟩

theorem hyperimmune_free_truth_table_scheme (A B : Set ℕ) (hA : HyperimmuneFree A)
    (e : ℕ) (he : ∀ x, phi A e x = Part.some (indicator B x)) :
    ∃ h : ℕ → ℕ, Computable h ∧
      (∀ x, boundedValue A (h x) e x = indicator B x + 1) ∧
      Presents (boundedData e h) B A := by
  have ht : ∀ x, (phi A e x).Dom := by
    intro x
    rw [he x]
    exact Part.some_dom _
  obtain ⟨h, hh, _, hb⟩ := hyperimmune_free_allowance_bound A hA e ht
  have hv : ∀ x, boundedValue A (h x) e x = indicator B x + 1 := by
    intro x
    apply hb x
    rw [he x]
    exact Part.mem_some _
  exact ⟨h, hh, hv, bounded_allowance_scheme ⟨hh, hv⟩⟩

theorem hyperimmune_free_truth_table (A B : Set ℕ) (hA : HyperimmuneFree A)
    (hBA : Reducible B A) : TruthTableReducible B A := by
  obtain ⟨c, hc⟩ := hBA
  have he : ∀ x, phi A (encodeCode c) x = Part.some (indicator B x) := by
    intro x
    rw [OracleProgramNumberings.phi, decode_encode, hc x]
    simp only [indicator]
    rfl
  obtain ⟨h, hh, hb, _⟩ := hyperimmune_free_truth_table_scheme A B hA (encodeCode c) he
  exact tt_of_boundedAllowance hh hb

end
end Lemmatheca.ComputabilityTheory.HyperimmuneDegrees
