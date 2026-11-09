import Lemmatheca.SacksSplitting.Priority
import Lemmatheca.LimitComputability.LimitLemma

/-! Computable jump observations for the same two pieces used in avoidance. -/
namespace Lemmatheca.ComputabilityTheory.SacksSplitting

open PostsTheorem UniversalComputation LimitComputability LowSimpleSets TuringJump TuringDegrees

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def jumpGuess (a : ℕ) (h : Approximation) (i s e : ℕ) : ℕ :=
  if 0 < finiteValue (stageCode a h s i) (s + 1) e e then 1 else 0

private theorem finite_value_computable {α : Type*} [Primcodable α]
    {u k e x : α → ℕ} (hu : Computable u) (hk : Computable k)
    (he : Computable e) (hx : Computable x) :
    Computable (fun p => finiteValue (u p) (k p) (e p) (x p)) := by
  have hp := Primrec₂.natPair.to_comp.comp hu
    (Primrec₂.natPair.to_comp.comp hk (Primrec₂.natPair.to_comp.comp he hx))
  exact (finiteValue_primitive.to_comp.comp hp).of_eq (fun _ => by
    simp only [finiteValueInput, Nat.unpair_pair])

private theorem eventual_observation (a : ℕ) (h : Approximation) (i e : ℕ)
    (he : e ∈ jump (piece a h i)) :
    ∃ t, ∀ s ≥ t, 0 < finiteValue (stageCode a h s i) (s + 1) e e := by
  obtain ⟨k, hk⟩ := (jump_certificate (piece a h i) e).mp he
  let y := OracleProgramNumberings.boundedValue (piece a h i) k e e - 1
  have hy : OracleProgramNumberings.boundedValue (piece a h i) k e e = y + 1 := by
    dsimp [y]
    omega
  obtain ⟨t, ht⟩ := prefix_settles a h i k
  refine ⟨max t k, fun s hs => ?_⟩
  let u := stageCode a h s i
  have hfinite : finiteValue u k e e = y + 1 :=
    (finiteValue_agreement (piece a h i) u k e e (ht s (by omega))).trans hy
  have hfixed : OracleProgramNumberings.bounded (finiteOracle u) k
      (OracleProgramNumberings.decodeCode e) e = some y :=
    (OracleProgramNumberings.boundedValue_output _ _ _ _ _).mp
      ((finiteValue_identity u k e e).symm.trans hfinite)
  have hle : k ≤ s + 1 := by omega
  have hlarge : OracleProgramNumberings.bounded (finiteOracle u) (s + 1)
      (OracleProgramNumberings.decodeCode e) e = some y := by
    simpa only [OracleProgramNumberings.bounded, Nat.add_sub_of_le hle] using
      OracleProgramNumberings.bounded_monotone
        (indicator (fun q => q ∈ finiteOracle u)) k (s + 1 - k)
        (OracleProgramNumberings.decodeCode e) e y hfixed
  have hout : finiteValue u (s + 1) e e = y + 1 :=
    (finiteValue_identity u (s + 1) e e).trans
      ((OracleProgramNumberings.boundedValue_output _ _ _ _ _).mpr hlarge)
  change 0 < finiteValue u (s + 1) e e
  omega

theorem diagonal_preserved (a : ℕ) (h : Approximation) (q : ℕ)
    (hhigher : HigherStable a h q) : DiagonalPreserved a h q := by
  obtain ⟨T, hT⟩ := higher_cutoff a h q hhigher
  refine ⟨T, fun s hs hval => ?_⟩
  have hq : q ≤ s := hT.1.trans hs
  have hd := observation_data s (stage a h s) q
  have hpos : 0 < leastObservation s (stage a h s) q :=
    hd.2.1.mpr ⟨s + 1, le_rfl, hval⟩
  have hk : leastObservation s (stage a h s) q ≤ restraintAt a h (s + 1) q := by
    rw [(record_update a h s q).2, nextRestraint, ite_eq_left hq]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hagree := permanent_protection a h q T s _ hT hs hk
  apply (OracleProgramNumberings.phi_domain_certificate _ _ _).mpr
  refine ⟨leastObservation s (stage a h s) q, ?_⟩
  rw [← finiteValue_agreement _ _ _ _ _ hagree]
  exact (hd.2.2 hpos).1

theorem jump_guess_data (a : ℕ) (h : Approximation) (C : Set ℕ)
    (hh : Computable₂ h) (hconv : Converges h C) (hC : ¬ ComputablePred C)
    (i : ℕ) (hi : i < 2) :
    Computable₂ (jumpGuess a h i) ∧ Binary (jumpGuess a h i) ∧
      Converges (jumpGuess a h i) (jump (piece a h i)) := by
  have hstage : Computable (stage a h) :=
    (stage_computable a h hh).1.comp (Computable.const a) Computable.id
  have hcode : Computable (fun s => stageCode a h s i) := by
    by_cases hi0 : i % 2 = 0
    · simpa only [stageCode, sideCode, ite_eq_left hi0] using Computable.fst.comp hstage
    · simpa only [stageCode, sideCode, ite_eq_right hi0] using
        Computable.fst.comp (Computable.snd.comp hstage)
  have hval : Computable (fun p : ℕ × ℕ =>
      finiteValue (stageCode a h p.1 i) (p.1 + 1) p.2 p.2) :=
    finite_value_computable (hcode.comp Computable.fst)
      (Primrec.succ.to_comp.comp Computable.fst) Computable.snd Computable.snd
  have htest : Computable (fun p : ℕ × ℕ => decide
      (0 < finiteValue (stageCode a h p.1 i) (p.1 + 1) p.2 p.2)) :=
    Primrec.nat_lt.decide.to_comp.comp (Computable.const 0) hval
  have hg : Computable₂ (jumpGuess a h i) :=
    (Computable.cond htest (Computable.const 1) (Computable.const 0)).of_eq
      (fun _ => by simp only [jumpGuess]; split_ifs with hv <;> simp [hv])
  refine ⟨hg, ?_, ?_⟩
  · intro s e
    unfold jumpGuess
    split_ifs <;> simp
  · intro e
    have hmod : (2 * e + i) % 2 = i := by omega
    have hdiv : (2 * e + i) / 2 = e := by omega
    have hhigher : HigherStable a h (2 * e + i) :=
      fun p _ => (priority_induction a h C hh hconv hC p).2.2
    obtain ⟨T, hT⟩ := diagonal_preserved a h (2 * e + i) hhigher
    by_cases he : e ∈ jump (piece a h i)
    · obtain ⟨t, ht⟩ := eventual_observation a h i e he
      refine ⟨t, fun s hs => ?_⟩
      have he' : jump (piece a h i) e := he
      simp only [jumpGuess, ite_eq_left (ht s hs), indicator, ite_eq_left he']
    · refine ⟨T, fun s hs => ?_⟩
      have hn : ¬ 0 < finiteValue (stageCode a h s i) (s + 1) e e := by
        intro hv
        have hd := hT s hs
        simp only [hmod, hdiv] at hd
        exact he (hd hv)
      have he' : ¬ jump (piece a h i) e := he
      simp only [jumpGuess, ite_eq_right hn, indicator, ite_eq_right he']

theorem pieces_low (a : ℕ) (h : Approximation) (C : Set ℕ)
    (hh : Computable₂ h) (hconv : Converges h C) (hC : ¬ ComputablePred C) :
    Low (piece a h 0) ∧ Low (piece a h 1) := by
  constructor
  · exact (low_iff_jump_below_halting _).mpr
      ((limit_lemma _).mp ⟨jumpGuess a h 0, jump_guess_data a h C hh hconv hC 0 (by decide)⟩)
  · exact (low_iff_jump_below_halting _).mpr
      ((limit_lemma _).mp ⟨jumpGuess a h 1, jump_guess_data a h C hh hconv hC 1 (by decide)⟩)

theorem sacks_constructed (a : ℕ) (h : Approximation) (C : Set ℕ)
    (hh : Computable₂ h) (_hbinary : Binary h) (hconv : Converges h C)
    (hC : ¬ ComputablePred C) :
    REPred (piece a h 0) ∧ REPred (piece a h 1) ∧
      Disjoint (piece a h 0) (piece a h 1) ∧
      piece a h 0 ∪ piece a h 1 = EffectiveEnumerations.indexSet a ∧
      Low (piece a h 0) ∧ Low (piece a h 1) ∧
      ¬ Reducible C (piece a h 0) ∧ ¬ Reducible C (piece a h 1) := by
  obtain ⟨h₀, h₁, hd, hu⟩ := effective_partition a h hh
  obtain ⟨hl₀, hl₁⟩ := pieces_low a h C hh hconv hC
  obtain ⟨hn₀, hn₁⟩ := pieces_avoid a h C hh hconv hC
  exact ⟨h₀, h₁, hd, hu, hl₀, hl₁, hn₀, hn₁⟩

theorem sacks_splitting (A C : Set ℕ) (hA : REPred A)
    (hC : ¬ ComputablePred C) (hlimit : LimitComputable C) :
    ∃ A₀ A₁ : Set ℕ, REPred A₀ ∧ REPred A₁ ∧ Disjoint A₀ A₁ ∧ A₀ ∪ A₁ = A ∧
      Low A₀ ∧ Low A₁ ∧ ¬ Reducible C A₀ ∧ ¬ Reducible C A₁ := by
  obtain ⟨a, ha⟩ := (enumerable_iff_index A).mp hA
  obtain ⟨h, hh, hb, hc⟩ := hlimit
  have hEq : EffectiveEnumerations.indexSet a = A := Set.ext (fun x => (ha x).symm)
  refine ⟨piece a h 0, piece a h 1, ?_⟩
  simpa only [hEq] using sacks_constructed a h C hh hb hc hC

end
end Lemmatheca.ComputabilityTheory.SacksSplitting
