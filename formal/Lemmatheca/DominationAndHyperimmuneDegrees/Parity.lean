import Lemmatheca.DominationAndHyperimmuneDegrees.Arrays

/-! Increasing parity coding retains exactly the original oracle's degree. -/
namespace Lemmatheca.ComputabilityTheory.HyperimmuneDegrees

open OracleComputation TuringDegrees UniversalComputation
open OracleProgramNumberings (identityCode)
open EffectiveEnumerations BusyBeaverFunctions

noncomputable section
set_option backward.isDefEq.respectTransparency false

def parityGrowth (A : Set ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec (2 * f 0 + indicator A 0)
    (fun n previous => 2 * (previous + f (n + 1) + 1) + indicator A (n + 1))

theorem parity_growth_spec (A : Set ℕ) (f : ℕ → ℕ) :
    StrictMono (parityGrowth A f) ∧ Majorizes (parityGrowth A f) f ∧
      ∀ n, parityGrowth A f n % 2 = indicator A n := by
  classical
  have hbits (n : ℕ) : indicator A n = 0 ∨ indicator A n = 1 := by
    by_cases h : A n <;> simp [indicator, h]
  refine ⟨strictMono_nat_of_lt_succ ?_, ?_, ?_⟩
  · intro n
    change parityGrowth A f n <
      2 * (parityGrowth A f n + f (n + 1) + 1) + indicator A (n + 1)
    omega
  · intro n
    cases n with
    | zero => change f 0 ≤ 2 * f 0 + indicator A 0; omega
    | succ n =>
      change f (n + 1) ≤ 2 * (parityGrowth A f n + f (n + 1) + 1) + indicator A (n + 1)
      omega
  · intro n
    cases n with
    | zero =>
      change (2 * f 0 + indicator A 0) % 2 = _
      rcases hbits 0 with h | h <;> simp [h, Nat.add_mod]
    | succ n =>
      change (2 * (parityGrowth A f n + f (n + 1) + 1) + indicator A (n + 1)) % 2 = _
      rcases hbits (n + 1) with h | h <;> simp [h, Nat.add_mod]

theorem parity_range_infinite (A : Set ℕ) (f : ℕ → ℕ) :
    (Set.range (parityGrowth A f)).Infinite := by
  exact Set.infinite_range_of_injective (parity_growth_spec A f).1.injective

theorem parity_principal (A : Set ℕ) (f : ℕ → ℕ) :
    increasingList (Set.range (parityGrowth A f)) (parity_range_infinite A f) =
      parityGrowth A f := by
  let g := parityGrowth A f
  have hg : StrictMono g := (parity_growth_spec A f).1
  let hInf := parity_range_infinite A f
  obtain ⟨hm, hmin, hnext⟩ := least_members_spec (Set.range g) hInf
  funext n
  induction n with
  | zero =>
    change firstMember (Set.range g) hInf = g 0
    apply le_antisymm (hmin (g 0) ⟨0, rfl⟩)
    obtain ⟨k, hk⟩ := hm
    rw [← hk]
    exact hg.monotone (Nat.zero_le k)
  | succ n ih =>
    change nextMember (Set.range g) hInf (increasingList (Set.range g) hInf n) = g (n + 1)
    rw [ih]
    have hn := hnext (g n)
    apply le_antisymm (hn.2.2 (g (n + 1)) ⟨n + 1, rfl⟩ (hg (Nat.lt_succ_self n)))
    obtain ⟨k, hk⟩ := hn.1
    have hnk : n < k := by
      have hlt := hn.2.1
      rw [← hk] at hlt
      by_contra h
      have hle := hg.monotone (show k ≤ n by omega)
      omega
    rw [← hk]
    exact hg.monotone (by omega)

def growthBaseValue (z : ℕ) : ℕ := 2 * z.unpair.1 + z.unpair.2

def growthStepValue (z : ℕ) : ℕ :=
  2 * (z.unpair.1 + z.unpair.2.unpair.1 + 1) + z.unpair.2.unpair.2

def parityValue (z : ℕ) : ℕ := z % 2

theorem growthBaseValue_computable : Computable growthBaseValue := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair)).to_comp

theorem growthStepValue_computable : Computable growthStepValue := by
  have hl : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (Primrec.nat_add.comp hl (hl.comp hr))))
    (hr.comp hr)).to_comp

theorem parityValue_computable : Computable parityValue := by
  exact (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)).to_comp

/-- The syntax depends only on c; queries supply the currently used oracle's bits. -/
def growthProgram (c : Code) : Code :=
  .comp
    (.prec
      (.comp (embed (ordinaryProgram growthBaseValue growthBaseValue_computable))
        (.pair (.comp c .zero) (.comp .query .zero)))
      (.comp (embed (ordinaryProgram growthStepValue growthStepValue_computable))
        (.pair (.comp .right .right)
          (.pair (.comp c (.comp .succ (.comp .left .right)))
            (.comp .query (.comp .succ (.comp .left .right)))))))
    (.pair .zero identityCode)

def rangeProgram (c : Code) : Code := boundedRangeProgram (growthProgram c)

/-- One inverse program works for all original oracles and all supplied functions. -/
def parityProgram : Code :=
  .comp (embed (ordinaryProgram parityValue parityValue_computable)) principalProgram

theorem growth_program_eval (A : Set ℕ) (f : ℕ → ℕ) (c : Code)
    (hc : ∀ n, eval A c n = Part.some (f n)) (n : ℕ) :
    eval A (growthProgram c) n = Part.some (parityGrowth A f n) := by
  let base : Code := .comp (embed (ordinaryProgram growthBaseValue growthBaseValue_computable))
    (.pair (.comp c .zero) (.comp .query .zero))
  let step : Code := .comp (embed (ordinaryProgram growthStepValue growthStepValue_computable))
    (.pair (.comp .right .right)
      (.pair (.comp c (.comp .succ (.comp .left .right)))
        (.comp .query (.comp .succ (.comp .left .right)))))
  have hb : eval A base 0 = Part.some (parityGrowth A f 0) := by
    simp [base, eval, eval_embed, ordinaryProgram_eval, growthBaseValue, hc, parityGrowth]
    rfl
  have hs (k v : ℕ) : eval A step (Nat.pair 0 (Nat.pair k v)) =
      Part.some (2 * (v + f (k + 1) + 1) + indicator A (k + 1)) := by
    simp [step, eval, eval_embed, ordinaryProgram_eval, growthStepValue, hc]
    rfl
  have hr : ∀ k, eval A (.prec base step) (Nat.pair 0 k) = Part.some (parityGrowth A f k) := by
    intro k
    induction k with
    | zero => rw [eval_prec_zero]; exact hb
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some, hs]
      rfl
  have hi : eval A (.pair .zero identityCode) n = Part.some (Nat.pair 0 n) := by
    simp [eval, OracleProgramNumberings.identity_eval]
  change (eval A (.pair .zero identityCode) n).bind (eval A (.prec base step)) = _
  rw [hi, Part.bind_some]
  exact hr n

theorem range_program_eval (A : Set ℕ) (f : ℕ → ℕ) (c : Code)
    (hc : ∀ n, eval A c n = Part.some (f n)) :
    Reduces (rangeProgram c) (Set.range (parityGrowth A f)) A := by
  exact increasing_range_program_reduces A (growthProgram c) (parityGrowth A f)
    (growth_program_eval A f c hc) (parity_growth_spec A f).1

theorem parity_program_eval (A : Set ℕ) (f : ℕ → ℕ) :
    Reduces parityProgram A (Set.range (parityGrowth A f)) := by
  intro n
  change (eval (Set.range (parityGrowth A f)) principalProgram n).bind
    (eval (Set.range (parityGrowth A f)) (embed (ordinaryProgram parityValue parityValue_computable))) = _
  rw [principal_program_eval _ (parity_range_infinite A f), Part.bind_some,
    eval_embed, ordinaryProgram_eval, parity_principal]
  exact congrArg Part.some ((parity_growth_spec A f).2.2 n)

theorem parity_degree_equivalence (A : Set ℕ) (f : ℕ → ℕ) (c : Code)
    (hc : ∀ n, eval A c n = Part.some (f n)) :
    Equivalent (Set.range (parityGrowth A f)) A := by
  exact ⟨⟨rangeProgram c, range_program_eval A f c hc⟩,
    ⟨parityProgram, parity_program_eval A f⟩⟩

theorem parity_range_hyperimmune (A : Set ℕ) (f : ℕ → ℕ) (hf : HyperimmuneFunction f) :
    HyperimmuneSet (Set.range (parityGrowth A f)) := by
  refine ⟨parity_range_infinite A f, ?_⟩
  change ¬ ComputablyDominated
    (increasingList (Set.range (parityGrowth A f)) (parity_range_infinite A f))
  rw [parity_principal]
  rintro ⟨h, hh, hb⟩
  apply hf
  exact ⟨h, hh, hb.mono (fun n hn => ((parity_growth_spec A f).2.1 n).trans hn)⟩

theorem degree_characterization (A : Set ℕ) :
    HasHyperimmuneDegree A ↔ ∃ X : Set ℕ, HyperimmuneSet X ∧ Equivalent X A := by
  constructor
  · rintro ⟨f, ⟨c, hc⟩, hf⟩
    exact ⟨Set.range (parityGrowth A f), parity_range_hyperimmune A f hf,
      parity_degree_equivalence A f c (fun n => congrFun hc n)⟩
  · rintro ⟨X, ⟨hX, hh⟩, hXA⟩
    refine ⟨increasingList X hX, ?_, hh⟩
    exact (function_computable_iff_graph_reducible A _).mpr
      (reducible_trans (principal_graph_equivalence X hX).1 hXA.1)

theorem hyperimmune_free_iff_no_representative (A : Set ℕ) :
    HyperimmuneFree A ↔ ∀ X : Set ℕ, Equivalent X A → ¬ HyperimmuneSet X := by
  classical
  constructor
  · intro hA X hXA hX
    exact (hyperimmune_or_free A).mp ((degree_characterization A).mpr ⟨X, hX, hXA⟩) hA
  · intro h
    by_contra hnot
    obtain ⟨X, hX, hXA⟩ := (degree_characterization A).mp ((hyperimmune_or_free A).mpr hnot)
    exact h X hXA hX

end
end Lemmatheca.ComputabilityTheory.HyperimmuneDegrees
