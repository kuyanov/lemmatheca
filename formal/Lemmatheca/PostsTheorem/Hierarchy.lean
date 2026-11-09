import Lemmatheca.PostsTheorem.Correspondence
import Lemmatheca.ArithmeticalHierarchy.Arithmetic

/-! Strict classes, completeness with its matching base and finite arithmetic prefixes. -/
namespace Lemmatheca.ComputabilityTheory.PostsTheorem

open OracleProgramNumberings ArithmeticalHierarchy TuringJump TuringDegrees

theorem iterate_not_pi (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    ¬ Pi B n (iterate B n) := by
  cases n with
  | zero => omega
  | succ n =>
      intro h
      exact (jump_strict (iterate B n)).2
        ((delta_iff_reducible B n (iterate B (n + 1))).mp ⟨iterate_sigma B _, h⟩)

theorem complement_iterate_polarity (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    Pi B n (iterate B n)ᶜ ∧ ¬ Sigma B n (iterate B n)ᶜ := by
  refine ⟨(level_complement B n true _).mp (iterate_sigma B n), ?_⟩
  intro h
  apply iterate_not_pi B n hn
  have hp := (level_complement B n true _).mp h
  change Level B n false (fun x => ¬¬(iterate B n) x) at hp
  have he : (fun x => ¬¬(iterate B n) x) = (iterate B n : ℕ → Prop) := by
    funext x
    exact propext not_not
  rw [he] at hp
  exact hp

theorem polarity_incomparable (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    ¬ {S : Set ℕ | Sigma B n S} ⊆ {S | Pi B n S} ∧
      ¬ {S : Set ℕ | Pi B n S} ⊆ {S | Sigma B n S} := by
  constructor
  · intro h
    exact iterate_not_pi B n hn (h (iterate_sigma B n))
  · intro h
    exact (complement_iterate_polarity B n hn).2
      (h (complement_iterate_polarity B n hn).1)

theorem delta_proper_polarities (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    {S : Set ℕ | Delta B n S} ⊂ {S | Sigma B n S} ∧
      {S : Set ℕ | Delta B n S} ⊂ {S | Pi B n S} := by
  constructor
  · refine ⟨fun _ h => h.1, ?_⟩
    intro h
    exact iterate_not_pi B n hn (h (iterate_sigma B n)).2
  · refine ⟨fun _ h => h.2, ?_⟩
    intro h
    exact (complement_iterate_polarity B n hn).2
      (h (complement_iterate_polarity B n hn).1).1

theorem sigma_step_proper (B : Set ℕ) (n : ℕ) :
    {S : Set ℕ | Sigma B n S} ⊂ {S | Sigma B (n + 1) S} := by
  refine ⟨fun S h => level_padding B n true true S h, ?_⟩
  intro h
  exact iterate_not_pi B (n + 1) (by omega)
    (level_padding B n true false _ (h (iterate_sigma B (n + 1))))

theorem pi_step_proper (B : Set ℕ) (n : ℕ) :
    {S : Set ℕ | Pi B n S} ⊂ {S | Pi B (n + 1) S} := by
  refine ⟨fun S h => level_padding B n false false S h, ?_⟩
  intro h
  exact (complement_iterate_polarity B (n + 1) (by omega)).2
    (level_padding B n false true _
      (h (complement_iterate_polarity B (n + 1) (by omega)).1))

private theorem padded_delta (B : Set ℕ) (n : ℕ) (p : Bool) (S : Set ℕ)
    (h : Level B n p S) : Delta B (n + 1) S :=
  ⟨level_padding B n p true S h, level_padding B n p false S h⟩

theorem delta_step_proper (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    {S : Set ℕ | Delta B n S} ⊂ {S | Delta B (n + 1) S} := by
  refine ⟨fun S h => padded_delta B n true S h.1, ?_⟩
  intro h
  exact iterate_not_pi B n hn (h (padded_delta B n true _ (iterate_sigma B n))).2

noncomputable def SigmaComplete (B : Set ℕ) (n : ℕ) (H : Set ℕ) : Prop :=
  Sigma B n H ∧ ∀ S : Set ℕ, Sigma B n S → ManyOneReducible S H

theorem complete_iff_iterate (B : Set ℕ) (n : ℕ) (hn : 0 < n) (H : Set ℕ) :
    SigmaComplete B n H ↔ ManyOneEquiv H (iterate B n) := by
  cases n with
  | zero => omega
  | succ n =>
      constructor
      · intro h
        exact ⟨(sigma_iff_manyOne B n H).mp h.1, h.2 _ (iterate_sigma B _)⟩
      · intro h
        refine ⟨manyOne_preimage B (n + 1) true H _ h.1 (iterate_sigma B _), ?_⟩
        intro S hs
        exact ((sigma_iff_manyOne B n S).mp hs).trans h.2

theorem complete_boundaries (B : Set ℕ) (n : ℕ) (hn : 0 < n) (H : Set ℕ)
    (hH : SigmaComplete B n H) :
    ¬ Pi B n H ∧ ¬ Delta B n H ∧ Delta B (n + 1) H := by
  have he := (complete_iff_iterate B n hn H).mp hH
  have hp : ¬ Pi B n H := by
    intro h
    exact iterate_not_pi B n hn (manyOne_preimage B n false _ H he.2 h)
  exact ⟨hp, fun h => hp h.2, padded_delta B n true H hH.1⟩

theorem union_gap_witness (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    Delta B (n + 1) (join (iterate B n) (iterate B n)ᶜ) ∧
      ¬ Sigma B n (join (iterate B n) (iterate B n)ᶜ) ∧
      ¬ Pi B n (join (iterate B n) (iterate B n)ᶜ) := by
  let H := iterate B n
  have ho : ManyOneReducible Hᶜ (join H Hᶜ) :=
    ⟨_, (join_odd_reduction H Hᶜ).1.to_comp, (join_odd_reduction H Hᶜ).2⟩
  have he : ManyOneReducible H (join H Hᶜ) :=
    ⟨_, (join_even_reduction H Hᶜ).1.to_comp, (join_even_reduction H Hᶜ).2⟩
  refine ⟨(delta_iff_reducible B n _).mpr (join_complement_equivalent H).1, ?_, ?_⟩
  · intro h
    exact (complement_iterate_polarity B n hn).2
      (manyOne_preimage B n true Hᶜ (join H Hᶜ) ho h)
  · intro h
    exact iterate_not_pi B n hn (manyOne_preimage B n false H (join H Hᶜ) he h)

theorem union_gap_proper (B : Set ℕ) (n : ℕ) (hn : 0 < n) :
    ({S : Set ℕ | Sigma B n S} ∪ {S | Pi B n S}) ⊂ {S | Delta B (n + 1) S} := by
  refine ⟨?_, ?_⟩
  · intro S h
    rcases h with h | h
    · exact padded_delta B n true S h
    · exact padded_delta B n false S h
  · intro h
    have hw := union_gap_witness B n hn
    rcases h hw.1 with hs | hp
    · exact hw.2.1 hs
    · exact hw.2.2 hp

noncomputable def Arithmetical (S : Set ℕ) : Prop :=
  ∃ n, Sigma ∅ n S ∨ Pi ∅ n S

theorem arithmetical_iff_finite_jump (S : Set ℕ) :
    Arithmetical S ↔ ∃ m, Reducible S (iterate ∅ m) := by
  constructor
  · rintro ⟨n, hs | hp⟩
    · exact ⟨n, (delta_iff_reducible ∅ n S).mp (padded_delta ∅ n true S hs)⟩
    · exact ⟨n, (delta_iff_reducible ∅ n S).mp (padded_delta ∅ n false S hp)⟩
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, Or.inl ((delta_iff_reducible ∅ m S).mpr hm).1⟩

theorem arithmetical_iff_arithmetic_prefix (S : Set ℕ) :
    Arithmetical S ↔ ∃ n, 0 < n ∧ ∃ p : Bool,
      ArithmeticDefinability.PrefixDefinable n p (fun v : Tuple 1 => v 0 ∈ S) := by
  constructor
  · rintro ⟨n, hs | hp⟩
    · refine ⟨n + 1, by omega, true, ?_⟩
      apply (positive_level_arithmetic_iff (n + 1) (by omega) true _).mp
      exact (unary_finite_bridge ∅ (n + 1) true S).mpr
        (level_padding ∅ n true true S hs)
    · refine ⟨n + 1, by omega, false, ?_⟩
      apply (positive_level_arithmetic_iff (n + 1) (by omega) false _).mp
      exact (unary_finite_bridge ∅ (n + 1) false S).mpr
        (level_padding ∅ n false false S hp)
  · rintro ⟨n, _, p, hp⟩
    have hl := (unary_finite_bridge ∅ n p S).mp (arithmetic_prefix_to_level n p _ hp)
    cases p
    · exact ⟨n, Or.inr hl⟩
    · exact ⟨n, Or.inl hl⟩

theorem finite_arithmetical_iff_jump {k : ℕ} (P : Tuple k → Prop) :
    (∃ n, FiniteLevel ∅ n true P ∨ FiniteLevel ∅ n false P) ↔
      ∃ m, FiniteDecidable (iterate ∅ m) P := by
  constructor
  · rintro ⟨n, hs | hp⟩
    · exact ⟨n, (finite_delta_iff_decidable ∅ n P).mp
        ⟨finite_padding ∅ n true true P hs, finite_padding ∅ n true false P hs⟩⟩
    · exact ⟨n, (finite_delta_iff_decidable ∅ n P).mp
        ⟨finite_padding ∅ n false true P hp, finite_padding ∅ n false false P hp⟩⟩
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, Or.inl ((finite_delta_iff_decidable ∅ m P).mpr hm).1⟩

theorem finite_arithmetic_prefix_iff {k : ℕ} (P : Tuple k → Prop) :
    (∃ n, FiniteLevel ∅ n true P ∨ FiniteLevel ∅ n false P) ↔
      ∃ n, 0 < n ∧ ∃ p : Bool, ArithmeticDefinability.PrefixDefinable n p P := by
  constructor
  · rintro ⟨n, hs | hp⟩
    · exact ⟨n + 1, by omega, true,
        (positive_level_arithmetic_iff (n + 1) (by omega) true P).mp
          (finite_padding ∅ n true true P hs)⟩
    · exact ⟨n + 1, by omega, false,
        (positive_level_arithmetic_iff (n + 1) (by omega) false P).mp
          (finite_padding ∅ n false false P hp)⟩
  · rintro ⟨n, _, p, hp⟩
    cases p
    · exact ⟨n, Or.inr (arithmetic_prefix_to_level n false P hp)⟩
    · exact ⟨n, Or.inl (arithmetic_prefix_to_level n true P hp)⟩

theorem next_jump_arithmetical (m : ℕ) :
    Arithmetical (iterate ∅ (m + 1)) ∧ ¬ Reducible (iterate ∅ (m + 1)) (iterate ∅ m) := by
  exact ⟨⟨m + 1, Or.inl (iterate_sigma ∅ _)⟩, (jump_strict (iterate ∅ m)).2⟩

end Lemmatheca.ComputabilityTheory.PostsTheorem
