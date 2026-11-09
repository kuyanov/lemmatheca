import Lemmatheca.BeyondComputableChangeBounds.Pointwise
import Lemmatheca.ComputablyBoundedChanges.Basic

/-! Candidate pairs allow the proposed input bound itself to be a partial program. -/
namespace Lemmatheca.ComputabilityTheory.BeyondComputableChangeBounds

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges
open UniversalFiniteChangeSets ComputablyBoundedChanges

set_option backward.isDefEq.respectTransparency false

def candidateGuess (e s x : ℕ) : ℕ :=
  let v := boundedValue s e.unpair.2 x
  if v = 0 then 0 else universalGuess (v - 1) e.unpair.1 s x

noncomputable def candidateSet (e : ℕ) : Set ℕ :=
  {x | ∃ n, phi e.unpair.2 x = Part.some n ∧ x ∈ rowSet n e.unpair.1}

theorem candidate_data :
    Computable (fun t : (ℕ × ℕ) × ℕ => candidateGuess t.1.1 t.1.2 t.2) ∧
      ∀ e, Binary (candidateGuess e) ∧ StartsZero (candidateGuess e) := by
  have hv : Primrec (fun t : (ℕ × ℕ) × ℕ => boundedValue t.1.2 t.1.1.unpair.2 t.2) :=
    boundedValue_primitive.comp
      (show Primrec (fun t : (ℕ × ℕ) × ℕ => ((t.1.2, t.1.1.unpair.2), t.2)) from by fun_prop)
  have hp : Primrec (fun t : (ℕ × ℕ) × ℕ => t.1.1.unpair.1) := by fun_prop
  have hs : Primrec (fun t : (ℕ × ℕ) × ℕ => t.1.2) := by fun_prop
  have hm := (((Primrec.nat_sub.comp hv (Primrec.const 1)).pair hp).pair hs).pair Primrec.snd
  have hg : Computable (fun t : (ℕ × ℕ) × ℕ =>
      universalGuess (boundedValue t.1.2 t.1.1.unpair.2 t.2 - 1)
        t.1.1.unpair.1 t.1.2 t.2) :=
    (guess_computable.comp hm.to_comp).of_eq (fun _ => rfl)
  refine ⟨?_, fun e => ⟨?_, ?_⟩⟩
  · exact (Computable.cond (Primrec.eq.comp hv (Primrec.const 0)).decide.to_comp
      (Computable.const 0) hg).of_eq (fun t => by simp [candidateGuess])
  · intro s x
    dsimp only [candidateGuess]
    split_ifs
    · exact Or.inl rfl
    · exact (simulation_invariants _ _ _ _).1
  · intro x
    simp [candidateGuess, universalGuess, simulation]

theorem candidate_undefined (e x : ℕ) (hq : ¬ (phi e.unpair.2 x).Dom) :
    (∀ s, candidateGuess e s x = 0) ∧ x ∉ candidateSet e := by
  have hv : ∀ s, boundedValue s e.unpair.2 x = 0 := by
    intro s
    by_contra hn
    have hp : boundedValue s e.unpair.2 x =
        (boundedValue s e.unpair.2 x - 1) + 1 := by omega
    have hm := (phi_output e.unpair.2 x _).mpr ⟨s, hp⟩
    exact hq (Part.dom_iff_mem.mpr ⟨_, hm⟩)
  refine ⟨fun s => by simp [candidateGuess, hv], ?_⟩
  rintro ⟨n, hn, _⟩
  exact hq (Part.dom_iff_mem.mpr ⟨n, Part.eq_some_iff.mp hn⟩)

theorem candidate_tail (e x n : ℕ) (hq : phi e.unpair.2 x = Part.some n) :
    ∃ t, ∀ s, t ≤ s → candidateGuess e s x = universalGuess n e.unpair.1 s x := by
  obtain ⟨t, ht⟩ := (phi_output e.unpair.2 x n).mp (Part.eq_some_iff.mp hq)
  refine ⟨t, fun s hs => ?_⟩
  have hv : boundedValue s e.unpair.2 x = n + 1 :=
    (boundedValue_output _ _ _ _).mpr
      (Nat.Partrec.Code.evaln_mono hs ((boundedValue_output _ _ _ _).mp ht))
  simp [candidateGuess, hv]

theorem candidate_converges (e : ℕ) : Converges (candidateGuess e) (candidateSet e) := by
  classical
  intro x
  by_cases hq : (phi e.unpair.2 x).Dom
  · obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hq
    have hval := Part.eq_some_iff.mpr hn
    have hset : x ∈ candidateSet e ↔ x ∈ rowSet n e.unpair.1 := by
      constructor
      · rintro ⟨m, hm, hx⟩
        have heq : m = n := Part.mem_unique (Part.eq_some_iff.mp hm) hn
        simpa [heq] using hx
      · intro hx
        exact ⟨n, hval, hx⟩
    obtain ⟨t, ht⟩ := candidate_tail e x n hval
    obtain ⟨u, hu⟩ := row_converges n e.unpair.1 x
    refine ⟨max t u, fun s hs => ?_⟩
    rw [ht s (by omega), hu s (by omega)]
    simp only [indicator]
    exact if_congr hset.symm rfl rfl
  · obtain ⟨hv, hx⟩ := candidate_undefined e x hq
    refine ⟨0, fun s _ => ?_⟩
    rw [hv s]
    have hx' : ¬ candidateSet e x := hx
    simp [indicator, hx']

theorem supplied_presentation (a : Approximation) (b : ℕ → ℕ) (A : Set ℕ) (p q : ℕ)
    (hp : Presents p a) (hq : ∀ x, phi q x = Part.some (b x))
    (hb : Binary a) (hz : StartsZero a) (hn : BoundedBy a b) (hl : Converges a A) :
    candidateSet (Nat.pair p q) = A := by
  classical
  ext x
  have hf := pointwise_faithfulness (b x) p a x (indicator A x)
    (fun k => hp k x) (fun k => hb k x) (hz x) (fun s => hn s x) (hl x)
  have hset : x ∈ candidateSet (Nat.pair p q) ↔ x ∈ rowSet (b x) p := by
    simp only [candidateSet, Set.mem_ofPred_eq, Nat.unpair_pair]
    constructor
    · rintro ⟨n, hn, hx⟩
      have heq : n = b x := Part.mem_unique (Part.eq_some_iff.mp hn)
        (Part.eq_some_iff.mp (hq x))
      simpa [heq] using hx
    · intro hx
      exact ⟨b x, hq x, hx⟩
  rw [hset, hf.2]
  change indicator A x = 1 ↔ A x
  by_cases hx : A x <;> simp [indicator, hx]

theorem omega_covered (A : Set ℕ) (ha : OmegaCE A) : ∃ e, candidateSet e = A := by
  obtain ⟨a, b, hc, hb, hl, hz, hbc, hn⟩ := ha
  obtain ⟨p, hp⟩ := presents_exists a hc
  obtain ⟨q, hq⟩ := phi_complete (Partrec.nat_iff.mp hbc.partrec)
  refine ⟨Nat.pair p q, supplied_presentation a b A p q hp ?_ hb hz hn hl⟩
  intro x
  simp [hq]

end Lemmatheca.ComputabilityTheory.BeyondComputableChangeBounds
