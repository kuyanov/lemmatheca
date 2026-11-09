import Lemmatheca.UniversalFiniteChangeSets.Simulator

/-! Universal bounded-change sets, their ordinary tagging reductions and diagonal escape. -/
namespace Lemmatheca.ComputabilityTheory.UniversalFiniteChangeSets

open UniversalComputation LimitComputability DifferenceEnumerable FiniteMindChanges

set_option backward.isDefEq.respectTransparency false

def universalSet (n : ℕ) : Set ℕ :=
  {z | z.unpair.2 ∈ rowSet n z.unpair.1}

def universalApproximation (n s z : ℕ) : ℕ :=
  universalGuess n z.unpair.1 s z.unpair.2

def diagonalSet (n : ℕ) : Set ℕ := {e | e ∉ rowSet n e}

def diagonalGuess (n s e : ℕ) : ℕ :=
  delayedComplement (fun s e => universalGuess n e s e) s e

private theorem universal_count (n s z : ℕ) :
    changeCount (universalApproximation n) s z =
      changeCount (universalGuess n z.unpair.1) s z.unpair.2 := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [changeCount, universalApproximation, ih]

private theorem diagonal_row_count (n s e : ℕ) :
    changeCount (fun s e => universalGuess n e s e) s e =
      changeCount (universalGuess n e) s e := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [changeCount, ih]

private theorem diagonal_row_computable (n : ℕ) :
    Computable₂ (fun s e => universalGuess n e s e) :=
  guess_computable.comp
    ((((Computable.const n).pair Computable.snd).pair Computable.fst).pair Computable.snd)

theorem universal_data (n : ℕ) :
    Computable₂ (universalApproximation n) ∧ Binary (universalApproximation n) ∧
      StartsZero (universalApproximation n) ∧ AtMostChanges (universalApproximation n) n ∧
      Converges (universalApproximation n) (universalSet n) := by
  classical
  refine ⟨?_, ?_, fun _ => rfl, ?_, ?_⟩
  · exact guess_computable.comp
      ((((Computable.const n).pair
        (Computable.fst.comp (Computable.unpair.comp Computable.snd))).pair
          Computable.fst).pair
            (Computable.snd.comp (Computable.unpair.comp Computable.snd)))
  · intro s z
    exact (simulation_invariants n z.unpair.1 z.unpair.2 s).1
  · intro s z
    rw [universal_count]
    exact (simulation_invariants n z.unpair.1 z.unpair.2 s).2.2.1 ▸
      (simulation_invariants n z.unpair.1 z.unpair.2 s).2.1
  · intro z
    exact row_converges n z.unpair.1 z.unpair.2

theorem tagging_identity (n e x : ℕ) :
    Nat.pair e x ∈ universalSet n ↔ x ∈ rowSet n e := by
  simp [universalSet]

theorem universal_complete (n : ℕ) (A : Set ℕ) (ha : NCE n A) :
    ∃ e, Computable (Nat.pair e) ∧ Function.Injective (Nat.pair e) ∧
      ∀ x, x ∈ A ↔ Nat.pair e x ∈ universalSet n := by
  obtain ⟨a, hc, hb, hl, hz, hn⟩ := ha
  obtain ⟨e, he⟩ := presents_exists a hc
  have hrow := faithful_limits n e a A he hb hz hn hl
  refine ⟨e, Primrec₂.natPair.to_comp.comp (Computable.const e) Computable.id, ?_, ?_⟩
  · intro x y h
    have := congrArg (fun z : ℕ => z.unpair.2) h
    simpa using this
  · intro x
    rw [tagging_identity, hrow]

theorem diagonal_computable :
    Computable (fun p : (ℕ × ℕ) × ℕ => diagonalGuess p.1.1 p.1.2 p.2) := by
  have hcalc : Computable (fun p : (ℕ × ℕ) × ℕ =>
      Nat.casesOn (motive := fun _ => ℕ) p.1.2 0
        (fun s => 1 - universalGuess p.1.1 p.2 s p.2)) :=
    Computable.nat_casesOn (Computable.snd.comp Computable.fst) (Computable.const 0)
      (Primrec.nat_sub.to_comp.comp (Computable.const 1)
        (guess_computable.comp
          (((((Computable.fst.comp Computable.fst).comp Computable.fst).pair
            (Computable.snd.comp Computable.fst)).pair Computable.snd).pair
              (Computable.snd.comp Computable.fst)))).to₂
  exact hcalc.of_eq (fun p => by cases p.1.2 <;> rfl)

theorem diagonal_data (n : ℕ) :
    Binary (diagonalGuess n) ∧ StartsZero (diagonalGuess n) ∧
      AtMostChanges (diagonalGuess n) (n + 1) ∧
      Converges (diagonalGuess n) (diagonalSet n) ∧
      ∀ s e, changeCount (diagonalGuess n) (s + 1) e =
        1 + changeCount (fun s e => universalGuess n e s e) s e := by
  classical
  let a : Approximation := fun s e => universalGuess n e s e
  let A : Set ℕ := {e | e ∈ rowSet n e}
  have hb : Binary a := fun s e => (simulation_invariants n e e s).1
  have hz : StartsZero a := fun _ => rfl
  have hl : Converges a A := fun e => row_converges n e e
  obtain ⟨_hc, hbb, hbz, hbl⟩ :=
    delayed_complement_data a A (diagonal_row_computable n) hb hl
  refine ⟨hbb, hbz, ?_, hbl, delayed_complement_count a hb hz⟩
  intro s e
  cases s with
  | zero => simp [changeCount]
  | succ s =>
      change changeCount (delayedComplement a) (s + 1) e ≤ n + 1
      rw [delayed_complement_count a hb hz]
      change 1 + changeCount (fun s e => universalGuess n e s e) s e ≤ n + 1
      rw [diagonal_row_count]
      have h := simulation_invariants n e e s
      omega

theorem diagonal_not_nce (n : ℕ) : ¬ NCE n (diagonalSet n) := by
  rintro ⟨a, hc, hb, hl, hz, hn⟩
  obtain ⟨e, he⟩ := presents_exists a hc
  have hrow := faithful_limits n e a (diagonalSet n) he hb hz hn hl
  have hself : (e ∈ rowSet n e) ↔ e ∉ rowSet n e := by
    conv_lhs => rw [hrow]
    rfl
  tauto

theorem universal_not_co_nce (n : ℕ) : ¬ CoNCE n (universalSet n) := by
  intro h
  have hc : Computable (fun e => Nat.pair e e) :=
    Primrec₂.natPair.to_comp.comp Computable.id Computable.id
  have hp := nce_preimage n (universalSet n)ᶜ (fun e => Nat.pair e e) h hc
  have heq : (fun e => Nat.pair e e) ⁻¹' (universalSet n)ᶜ = diagonalSet n := by
    ext e
    simp [diagonalSet, universalSet]
  rw [heq] at hp
  exact diagonal_not_nce n hp

theorem zero_sets :
    universalSet 0 = ∅ ∧ diagonalSet 0 = Set.univ ∧
      (∀ e, diagonalGuess 0 0 e = 0) ∧
      (∀ s e, diagonalGuess 0 (s + 1) e = 1) ∧
      ∀ s e, changeCount (diagonalGuess 0) (s + 1) e = 1 := by
  classical
  have hzero : ∀ e s x, universalGuess 0 e s x = 0 := by
    intro e s x
    simp [universalGuess, zero_simulation]
  have hrow : ∀ e, rowSet 0 e = ∅ := by
    intro e
    ext x
    simp only [rowSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨t, ht⟩
    have := ht t le_rfl
    simp [hzero] at this
  refine ⟨?_, ?_, fun _ => rfl, ?_, ?_⟩
  · ext z
    simp [universalSet, hrow]
  · ext e
    simp [diagonalSet, hrow]
  · intro s e
    simp [diagonalGuess, delayedComplement, hzero]
  · intro s e
    rw [(diagonal_data 0).2.2.2.2 s e]
    have hc : ∀ s, changeCount (fun s e => universalGuess 0 e s e) s e = 0 := by
      intro s
      induction s with
      | zero => rfl
      | succ s ih =>
          change changeCount (fun s e => universalGuess 0 e s e) s e +
            (if universalGuess 0 e (s + 1) e = universalGuess 0 e s e then 0 else 1) = 0
          rw [ih]
          simp [hzero]
    simp [hc]

end Lemmatheca.ComputabilityTheory.UniversalFiniteChangeSets
