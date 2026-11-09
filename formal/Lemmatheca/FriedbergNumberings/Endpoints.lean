import Lemmatheca.FriedbergNumberings.Verification

namespace Lemmatheca.ComputabilityTheory.FriedbergNumberings

open UniversalComputation EffectiveEnumerations

noncomputable section

def endpointStop (n : ℕ) : ℕ := Nat.find (latest_unbounded n)

def endpointTest (n : ℕ) : Bool :=
  (events (state (endpointStop n))).any (fun p => p.2 == n)

theorem endpoint_stop_spec (n : ℕ) :
    n ≤ latest (state (endpointStop n)) ∧
      ∀ s, s < endpointStop n → latest (state s) < n := by
  exact ⟨Nat.find_spec (latest_unbounded n),
    fun s hs => Nat.lt_of_not_ge (Nat.find_min (latest_unbounded n) hs)⟩

theorem endpoint_stop_computable : Computable endpointStop := by
  have hl : Computable (fun s => latest (state s)) :=
    Computable.fst.comp (Computable.snd.comp state_computable)
  exact Computable.find
    (Primrec.nat_le.decide.to_comp.comp Computable.fst (hl.comp Computable.snd)).computablePred latest_unbounded

theorem endpoint_test_computable : Computable endpointTest := by
  classical
  have hp : PrimrecRel (fun (p : ℕ × ℕ) (n : ℕ) => p.2 = n) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hq : Computable₂ (fun (L : List (ℕ × ℕ)) (n : ℕ) => decide (∃ p ∈ L, p.2 = n)) :=
    hp.exists_mem_list.decide.to_comp
  have hl : Computable (fun n => events (state (endpointStop n))) :=
    (Computable.snd.comp (Computable.snd.comp state_computable)).comp endpoint_stop_computable
  exact (hq.comp hl Computable.id).of_eq (fun n => by
    apply Bool.eq_iff_iff.mpr
    simp [endpointTest, List.any_eq_true])

theorem endpoint_test_spec (n : ℕ) : endpointTest n = true ↔ n ∈ retirementEndpoints := by
  classical
  simp only [endpointTest, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨x, k⟩, hp, hk⟩
    dsimp only [Prod.snd] at hk
    subst k
    exact ⟨endpointStop n, x, hp⟩
  · rintro ⟨s, x, hs⟩
    refine ⟨(x, n), ?_, rfl⟩
    rcases le_total s (endpointStop n) with hle | hle
    · exact events_monotone hle hs
    · exact (events_stable_below (endpointStop n) s hle (x, n)
        (endpoint_stop_spec n).1).mp hs

theorem retirement_endpoints_computable : ComputablePred retirementEndpoints := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨endpointTest, endpoint_test_computable, ?_⟩
  funext n
  exact propext (endpoint_test_spec n).symm

theorem retirement_endpoints_positive_even :
    ∀ k ∈ retirementEndpoints, 0 < k ∧ Even k := by
  rintro k ⟨s, x, hk⟩
  exact retired_positive_even s x k ((retirement_record_spec s x k).mp hk)

theorem omitted_endpoints_infinite : retirementEndpointsᶜ.Infinite := by
  have hi : (Set.range (fun n : ℕ => 2 * n + 1)).Infinite :=
    Set.infinite_range_of_injective (fun a b hab => by omega)
  apply hi.mono
  rintro k ⟨n, rfl⟩ hk
  obtain ⟨m, hm⟩ := (retirement_endpoints_positive_even (2 * n + 1) hk).2
  omega

def omittedEndpoint : ℕ → ℕ :=
  Nat.rec 0 (fun _ y => nextMember retirementEndpointsᶜ omitted_endpoints_infinite y)

theorem omitted_endpoint_equations : omittedEndpoint 0 = 0 ∧
    ∀ n, omittedEndpoint (n + 1) ∉ retirementEndpoints ∧
      omittedEndpoint n < omittedEndpoint (n + 1) ∧
      ∀ k, omittedEndpoint n < k → k ∉ retirementEndpoints → omittedEndpoint (n + 1) ≤ k := by
  refine ⟨rfl, ?_⟩
  intro n
  have hn := (least_members_spec retirementEndpointsᶜ omitted_endpoints_infinite).2.2 (omittedEndpoint n)
  exact ⟨hn.1, hn.2.1, fun k hk hkn => hn.2.2 k hkn hk⟩

theorem omitted_endpoint_computable : Computable omittedEndpoint := by
  have hn : Computable (nextMember retirementEndpointsᶜ omitted_endpoints_infinite) :=
    next_member_computable _ _ retirement_endpoints_computable.not
  have hs : Computable₂ (fun (_ : ℕ) (z : ℕ × ℕ) =>
      nextMember retirementEndpointsᶜ omitted_endpoints_infinite z.2) :=
    hn.comp (Computable.snd.comp Computable.snd)
  exact Computable.nat_rec Computable.id (Computable.const 0) hs

theorem omitted_endpoint_enumerates : StrictMono omittedEndpoint ∧
    Set.range omittedEndpoint = retirementEndpointsᶜ := by
  have hzero : 0 ∉ retirementEndpoints := by
    intro h
    exact (Nat.lt_irrefl 0) (retirement_endpoints_positive_even 0 h).1
  have hmem : ∀ n, omittedEndpoint n ∈ retirementEndpointsᶜ := by
    intro n
    cases n with
    | zero => exact hzero
    | succ n => exact (omitted_endpoint_equations.2 n).1
  have hmono : StrictMono omittedEndpoint :=
    strictMono_nat_of_lt_succ (fun n => (omitted_endpoint_equations.2 n).2.1)
  have hinv : ∀ n k, k ∉ retirementEndpoints → k ≤ omittedEndpoint n →
      ∃ j ≤ n, omittedEndpoint j = k := by
    intro n
    induction n with
    | zero =>
      intro k _ hk
      exact ⟨0, le_rfl, by have hz := omitted_endpoint_equations.1; omega⟩
    | succ n ih =>
      intro k hk hle
      by_cases hkn : k ≤ omittedEndpoint n
      · obtain ⟨j, hj, he⟩ := ih k hk hkn
        exact ⟨j, hj.trans (Nat.le_succ n), he⟩
      · exact ⟨n + 1, le_rfl,
          le_antisymm ((omitted_endpoint_equations.2 n).2.2 k (by omega) hk) hle⟩
  refine ⟨hmono, ?_⟩
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    exact hmem n
  · intro hk
    obtain ⟨j, _, hj⟩ := hinv k k hk hmono.le_apply
    exact ⟨j, hj⟩

end
end Lemmatheca.ComputabilityTheory.FriedbergNumberings
