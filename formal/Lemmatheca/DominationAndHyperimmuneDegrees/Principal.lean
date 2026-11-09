import Lemmatheca.DominationAndHyperimmuneDegrees.Bounds
import Lemmatheca.EffectiveEnumerations.Increasing
import Lemmatheca.OracleProgramNumberings.Parameters

/-! The existing least-member enumeration with common actual oracle programs. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneDegrees

open OracleComputation TuringDegrees UniversalComputation
open OracleProgramNumberings (identityCode)
open EffectiveEnumerations BusyBeaverFunctions

noncomputable section
set_option backward.isDefEq.respectTransparency false

def HyperimmuneSet (X : Set ℕ) : Prop :=
  ∃ hX : X.Infinite, HyperimmuneFunction (increasingList X hX)

/-- The absolute least member at or above the supplied starting position. -/
def memberSearch : Code := .find' (.comp complementQuery .right)

def principalProgram : Code :=
  .comp (.prec
    (.comp memberSearch (.pair .zero .zero))
    (.comp memberSearch (.pair .zero (.comp .succ (.comp .right .right)))))
    (.pair .zero identityCode)

private theorem member_search_at (X : Set ℕ) (a m y : ℕ) (hy : y ∈ X) (hm : m ≤ y)
    (hmin : ∀ i, m ≤ i → i < y → i ∉ X) :
    eval X memberSearch (Nat.pair a m) = Part.some y := by
  classical
  have ht (i : ℕ) : eval X (.comp complementQuery .right) (Nat.pair a i) =
      Part.some (indicator (fun q => q ∈ Xᶜ) i) := by
    change (Part.some (Nat.pair a i).unpair.2).bind (eval X complementQuery) = _
    rw [Nat.unpair_pair, Part.bind_some, complement_query_eval]
  apply Part.eq_some_iff.mpr
  rw [memberSearch, eval_find]
  refine ⟨hm, ?_, ?_⟩
  · rw [ht]
    simp [indicator, hy]
  · intro i hmi hiy
    refine ⟨1, ?_, by decide⟩
    rw [ht]
    simp [indicator, hmin i hmi hiy]

theorem principal_program_eval (X : Set ℕ) (hX : X.Infinite) (n : ℕ) :
    eval X principalProgram n = Part.some (increasingList X hX n) := by
  obtain ⟨hfirst, hfirstmin, hnext⟩ := least_members_spec X hX
  let base : Code := .comp memberSearch (.pair .zero .zero)
  let step : Code := .comp memberSearch (.pair .zero (.comp .succ (.comp .right .right)))
  have hb : eval X base 0 = Part.some (firstMember X hX) := by
    have hi : eval X (.pair .zero .zero) 0 = Part.some (Nat.pair 0 0) := by
      simp [eval]
    change (eval X (.pair .zero .zero) 0).bind (eval X memberSearch) = _
    rw [hi, Part.bind_some]
    apply member_search_at X 0 0 _ hfirst (Nat.zero_le _)
    intro i _ hi hmem
    have := hfirstmin i hmem
    omega
  have hs (k v : ℕ) : eval X step (Nat.pair 0 (Nat.pair k v)) =
      Part.some (nextMember X hX v) := by
    have hi : eval X (.pair .zero (.comp .succ (.comp .right .right)))
        (Nat.pair 0 (Nat.pair k v)) = Part.some (Nat.pair 0 (v + 1)) := by
      simp [eval]
    change (eval X (.pair .zero (.comp .succ (.comp .right .right)))
      (Nat.pair 0 (Nat.pair k v))).bind (eval X memberSearch) = _
    rw [hi, Part.bind_some]
    apply member_search_at X 0 (v + 1) _ (hnext v).1 (by have := (hnext v).2.1; omega)
    intro i hvi hi hmem
    have := (hnext v).2.2 i hmem (by omega)
    omega
  have hr : ∀ k, eval X (.prec base step) (Nat.pair 0 k) =
      Part.some (increasingList X hX k) := by
    intro k
    induction k with
    | zero => rw [eval_prec_zero]; exact hb
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some, hs]
      rfl
  have hi : eval X (.pair .zero identityCode) n = Part.some (Nat.pair 0 n) := by
    simp [eval, OracleProgramNumberings.identity_eval]
  change (eval X (.pair .zero identityCode) n).bind (eval X (.prec base step)) = _
  rw [hi, Part.bind_some]
  exact hr n

def pairMax (z : ℕ) : ℕ := max z.unpair.1 z.unpair.2

theorem pairMax_computable : Computable pairMax := by
  exact Primrec.nat_max.to_comp.comp (Primrec.fst.comp Primrec.unpair).to_comp
    (Primrec.snd.comp Primrec.unpair).to_comp

def maxCode : Code := embed (ordinaryProgram pairMax pairMax_computable)

/-- At input x, compute values at 0 through x and take the maximum of the equality bits. -/
def boundedRangeProgram (c : Code) : Code :=
  .comp
    (.prec
      (.comp (embed (ordinaryProgram equalityBit equalityBit_computable))
        (.pair (.comp c .zero) identityCode))
      (.comp maxCode
        (.pair (.comp .right .right)
          (.comp (embed (ordinaryProgram equalityBit equalityBit_computable))
            (.pair (.comp c (.comp .succ (.comp .left .right))) .left)))))
    (.pair identityCode identityCode)

theorem bounded_range_program_eval (A : Set ℕ) (c : Code) (f : ℕ → ℕ)
    (hc : ∀ n, eval A c n = Part.some (f n)) (x : ℕ) :
    eval A (boundedRangeProgram c) x =
      Part.some (indicator (fun x => ∃ n ≤ x, f n = x) x) := by
  classical
  let base : Code := .comp (embed (ordinaryProgram equalityBit equalityBit_computable))
    (.pair (.comp c .zero) identityCode)
  let step : Code := .comp maxCode
    (.pair (.comp .right .right)
      (.comp (embed (ordinaryProgram equalityBit equalityBit_computable))
        (.pair (.comp c (.comp .succ (.comp .left .right))) .left)))
  have hb : eval A base x = Part.some (indicator (fun x => ∃ n ≤ 0, f n = x) x) := by
    simp [base, eval, eval_embed, ordinaryProgram_eval, hc, equalityBit, OracleProgramNumberings.identity_eval, indicator]
  have hs (k v : ℕ) : eval A step (Nat.pair x (Nat.pair k v)) =
      Part.some (max v (if f (k + 1) = x then 1 else 0)) := by
    simp [step, maxCode, pairMax, eval, eval_embed, ordinaryProgram_eval, hc, equalityBit]
  have hr : ∀ k, eval A (.prec base step) (Nat.pair x k) =
      Part.some (indicator (fun x => ∃ n ≤ k, f n = x) x) := by
    intro k
    induction k with
    | zero => rw [eval_prec_zero]; exact hb
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some, hs]
      have he : (∃ n ≤ k + 1, f n = x) ↔ (∃ n ≤ k, f n = x) ∨ f (k + 1) = x := by
        constructor
        · rintro ⟨n, hn, hv⟩
          by_cases hnk : n ≤ k
          · exact Or.inl ⟨n, hnk, hv⟩
          · have he : n = k + 1 := by omega
            exact Or.inr (he ▸ hv)
        · rintro (⟨n, hn, hv⟩ | hv)
          · exact ⟨n, by omega, hv⟩
          · exact ⟨k + 1, le_rfl, hv⟩
      by_cases h0 : ∃ n ≤ k, f n = x <;> by_cases h1 : f (k + 1) = x <;>
        simp [indicator, he, h0, h1]
  have hi : eval A (.pair identityCode identityCode) x = Part.some (Nat.pair x x) := by
    simp [eval, OracleProgramNumberings.identity_eval]
  change (eval A (.pair identityCode identityCode) x).bind (eval A (.prec base step)) = _
  rw [hi, Part.bind_some]
  exact hr x

theorem increasing_range_program_reduces (A : Set ℕ) (c : Code) (f : ℕ → ℕ)
    (hc : ∀ n, eval A c n = Part.some (f n)) (hf : StrictMono f) :
    Reduces (boundedRangeProgram c) (Set.range f) A := by
  have he : (fun x => ∃ n ≤ x, f n = x) = (fun x => x ∈ Set.range f) :=
    funext (fun x => propext (increasing_range_bounded hf x).symm)
  intro x
  rw [bounded_range_program_eval A c f hc x, he]

def principalInverseProgram : Code := boundedRangeProgram graphLookup

theorem principal_inverse_eval (X : Set ℕ) (hX : X.Infinite) :
    Reduces principalInverseProgram X (graph (increasingList X hX)) := by
  have h := increasing_range_program_reduces (graph (increasingList X hX)) graphLookup
    (increasingList X hX) (graphLookup_eval _) (increasing_list_correct X hX).1.1
  rw [(increasing_list_correct X hX).1.2] at h
  exact h

theorem principal_graph_equivalence (X : Set ℕ) (hX : X.Infinite) :
    Equivalent (graph (increasingList X hX)) X := by
  exact ⟨(function_computable_iff_graph_reducible X (increasingList X hX)).mp
    ⟨principalProgram, funext (principal_program_eval X hX)⟩,
    principalInverseProgram, principal_inverse_eval X hX⟩

end
end Lemmatheca.ComputabilityTheory.HyperimmuneDegrees
