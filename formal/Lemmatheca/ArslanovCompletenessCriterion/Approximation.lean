import Lemmatheca.ArslanovCompletenessCriterion.Basic
import Lemmatheca.EffectiveEnumerations.Settling

namespace Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion

open UniversalComputation OracleComputation
open BusyBeaverFunctions (ordinaryProgram)

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

-- The actual finite word uses the entire supplied canonical stage.
def stageWord (a s : ℕ) : ℕ :=
  FiniteSequenceCoding.code ((List.range s).map (EffectiveEnumerations.stageTest a s))

theorem stage_word_primitive : Primrec₂ stageWord := by
  exact (Primrec.encode.comp (Primrec.list_map
    (Primrec.list_range.comp Primrec.snd)
    (show Primrec₂ (fun p : ℕ × ℕ => fun x => EffectiveEnumerations.stageTest p.1 p.2 x)
      from EffectiveEnumerations.stage_test_primitive.to₂))).to₂

theorem stage_word_oracle (a s : ℕ) :
    FiniteSequenceCoding.length (stageWord a s) = s ∧
      PostsTheorem.finiteOracle (stageWord a s) = EffectiveEnumerations.stage a s := by
  constructor
  · simp [stageWord, FiniteSequenceCoding.length]
  · ext q
    by_cases hq : q < s
    · have he : FiniteSequenceCoding.entry (stageWord a s) q =
          EffectiveEnumerations.stageTest a s q := by
        simp [stageWord, FiniteSequenceCoding.entry, List.getElem?_range hq]
      change FiniteSequenceCoding.entry (stageWord a s) q % 2 = 1 ↔ _
      rw [he]
      rcases (EffectiveEnumerations.stage_test_spec a s q).1 with hz | ho
      · rw [hz]; simp only [Nat.zero_mod, zero_ne_one, false_iff]
        exact fun hm => by have := (EffectiveEnumerations.stage_test_spec a s q).2.mpr hm; omega
      · rw [ho]; simp only [Nat.one_mod, true_iff]
        exact (EffectiveEnumerations.stage_test_spec a s q).2.mp ho
    · have hl : FiniteSequenceCoding.length (stageWord a s) = s := by
        simp [stageWord, FiniteSequenceCoding.length]
      have he := FiniteSequenceCoding.entry_out_of_range (stageWord a s) q (by omega)
      change FiniteSequenceCoding.entry (stageWord a s) q % 2 = 1 ↔ _
      rw [he]; simp only [Nat.zero_mod, zero_ne_one, false_iff]
      exact fun hm => hq ((EffectiveEnumerations.stage_bounds a s).1 hm)

def approximation (a e s n : ℕ) : ℕ :=
  PostsTheorem.finiteValue (stageWord a s) s e n - 1

theorem approximation_primitive :
    Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => approximation p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hw : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) => stageWord p.1.1 p.2.1) :=
    stage_word_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hp : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      PostsTheorem.pack4 (stageWord p.1.1 p.2.1) p.2.1 p.1.2 p.2.2) :=
    Primrec₂.natPair.comp hw (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))
  have hb : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      PostsTheorem.finiteValueInput (PostsTheorem.pack4 (stageWord p.1.1 p.2.1) p.2.1 p.1.2 p.2.2) - 1) :=
    Primrec.nat_sub.comp (PostsTheorem.finiteValue_primitive.comp hp) (Primrec.const 1)
  apply hb.of_eq
  intro p
  simp only [PostsTheorem.finiteValueInput, PostsTheorem.pack4, Nat.unpair_pair, approximation]

theorem approximation_bounded_identity (a e s n : ℕ) :
    approximation a e s n =
      OracleProgramNumberings.boundedValue (EffectiveEnumerations.stage a s) s e n - 1 := by
  unfold approximation
  rw [PostsTheorem.finiteValue_identity, (stage_word_oracle a s).2]

-- The prefix test input is ((a,k),s); the recursion input becomes ((a,s),k).
def prefixShuffle (w : ℕ) : ℕ :=
  Nat.pair (Nat.pair w.unpair.1.unpair.1 w.unpair.2) w.unpair.1.unpair.2

theorem prefix_shuffle_primitive : Primrec prefixShuffle := by
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))

-- The recursion-step input is ((a,s),(q,accumulator)).
def prefixOld (w : ℕ) : ℕ := w.unpair.2.unpair.2

def prefixQuery (w : ℕ) : ℕ := w.unpair.2.unpair.1

def prefixStage (w : ℕ) : ℕ :=
  EffectiveEnumerations.stageTest w.unpair.1.unpair.1 w.unpair.1.unpair.2 w.unpair.2.unpair.1

def prefixFold (w : ℕ) : ℕ :=
  w.unpair.1 * (if w.unpair.2.unpair.1 = 1 ∧ w.unpair.2.unpair.2 = 0 then 0 else 1)

theorem prefix_old_primitive : Primrec prefixOld := by
  exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem prefix_query_primitive : Primrec prefixQuery := by
  exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem prefix_stage_primitive : Primrec prefixStage := by
  exact EffectiveEnumerations.stage_test_primitive.comp
    ((Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)).pair prefix_query_primitive)

theorem prefix_fold_primitive : Primrec prefixFold := by
  have h : PrimrecPred (fun w : ℕ =>
      w.unpair.2.unpair.1 = 1 ∧ w.unpair.2.unpair.2 = 0) :=
    (Primrec.eq.comp prefix_query_primitive (Primrec.const 1)).and
      (Primrec.eq.comp prefix_old_primitive (Primrec.const 0))
  exact Primrec.nat_mul.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.ite h (Primrec.const 0) (Primrec.const 1))

def prefixStepCode : Code :=
  .comp (embed (ordinaryProgram prefixFold prefix_fold_primitive.to_comp))
    (.pair (embed (ordinaryProgram prefixOld prefix_old_primitive.to_comp))
      (.pair (.comp .query (embed (ordinaryProgram prefixQuery prefix_query_primitive.to_comp)))
        (embed (ordinaryProgram prefixStage prefix_stage_primitive.to_comp))))

def prefixTestCode : Code :=
  .comp (.prec (OracleProgramNumberings.constantCode 1) prefixStepCode)
    (embed (ordinaryProgram prefixShuffle prefix_shuffle_primitive.to_comp))

def prefixFailureCode : Code := .comp (embed zeroTest) prefixTestCode

def prefixSearchCode (a : ℕ) : Code :=
  .comp (.find' prefixFailureCode)
    (.pair (.pair (OracleProgramNumberings.constantCode a) OracleProgramNumberings.identityCode) .zero)

theorem prefix_test_eval (A : Set ℕ) (a k s : ℕ) :
    eval A prefixTestCode (Nat.pair (Nat.pair a k) s) =
      Part.some (if ∀ q < k, q ∉ A ∨ q ∈ EffectiveEnumerations.stage a s then 1 else 0) := by
  let P : ℕ → Prop := fun q => q ∉ A ∨ q ∈ EffectiveEnumerations.stage a s
  have step (q v : ℕ) :
      eval A prefixStepCode (Nat.pair (Nat.pair a s) (Nat.pair q v)) =
        Part.some (v * if P q then 1 else 0) := by
    rcases (EffectiveEnumerations.stage_test_spec a s q).1 with hz | ho
    · have hnot : q ∉ EffectiveEnumerations.stage a s := by
        intro hm
        have := (EffectiveEnumerations.stage_test_spec a s q).2.mpr hm
        omega
      by_cases hA : q ∈ A <;>
        simp [prefixStepCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
          prefixFold, prefixOld, prefixQuery, prefixStage, hz, P, hA, hnot, indicator]
    · have hm := (EffectiveEnumerations.stage_test_spec a s q).2.mp ho
      by_cases hA : q ∈ A <;>
        simp [prefixStepCode, eval, eval_embed, BusyBeaverFunctions.ordinaryProgram_eval,
          prefixFold, prefixOld, prefixQuery, prefixStage, ho, P, hA, hm, indicator]
  have rec_eval : ∀ k, eval A (.prec (OracleProgramNumberings.constantCode 1) prefixStepCode)
      (Nat.pair (Nat.pair a s) k) = Part.some (if ∀ q < k, P q then 1 else 0) := by
    intro k
    induction k with
    | zero => simp [eval_prec_zero, OracleProgramNumberings.constant_eval]
    | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_some, step]
      have hall : (∀ q < k + 1, P q) ↔ (∀ q < k, P q) ∧ P k := by
        constructor
        · intro h; exact ⟨fun q hq => h q (by omega), h k (by omega)⟩
        · rintro ⟨h, hk⟩ q hq
          by_cases he : q = k
          · simpa [he] using hk
          · exact h q (by omega)
      simp only [hall]
      by_cases hold : ∀ q < k, P q <;> by_cases hk : P k <;>
        simp only [hold, hk, and_self, and_true, and_false,
          ite_true, ite_false, Nat.mul_one, Nat.mul_zero]
  change (eval A (embed (ordinaryProgram prefixShuffle prefix_shuffle_primitive.to_comp))
    (Nat.pair (Nat.pair a k) s)).bind _ = _
  rw [eval_embed, BusyBeaverFunctions.ordinaryProgram_eval, Part.bind_some]
  simpa only [prefixShuffle, Nat.unpair_pair] using rec_eval k

theorem positive_prefix_settles (a k s : ℕ) :
    (∀ q < k, q ∉ EffectiveEnumerations.indexSet a ∨ q ∈ EffectiveEnumerations.stage a s) ↔
      EffectiveEnumerations.Settles (EffectiveEnumerations.indexSet a)
        (EffectiveEnumerations.stage a) k s := by
  constructor
  · intro h q hq
    constructor
    · intro hm
      exact (h q hq).resolve_left (not_not_intro hm)
    · intro hm
      exact (EffectiveEnumerations.stage_union a q).mpr ⟨s, hm⟩
  · intro h q hq
    by_cases hm : q ∈ EffectiveEnumerations.indexSet a
    · exact Or.inr ((h q hq).mp hm)
    · exact Or.inl hm

theorem prefix_search_eval (A : Set ℕ) (a : ℕ)
    (ha : EffectiveEnumerations.indexSet a = A) (k : ℕ) :
    eval A (prefixSearchCode a) k =
      Part.some (EffectiveEnumerations.leastSettlingStage (EffectiveEnumerations.canonicalApproximation a) k) := by
  let F := EffectiveEnumerations.canonicalApproximation a
  let u := EffectiveEnumerations.leastSettlingStage F k
  let P : ℕ → Prop := fun s => ∀ q < k, q ∉ A ∨ q ∈ EffectiveEnumerations.stage a s
  have hF : F.atStage = EffectiveEnumerations.stage a :=
    funext (fun s => (EffectiveEnumerations.canonical_stages a s).2)
  have equiv (s : ℕ) : P s ↔ EffectiveEnumerations.Settles (EffectiveEnumerations.indexSet a) F.atStage k s := by
    rw [hF]
    simpa only [P, ha] using positive_prefix_settles a k s
  have hu : P u := (equiv u).mpr ((EffectiveEnumerations.least_settling_spec F).1 k)
  have hmin (s : ℕ) (hs : P s) : u ≤ s :=
    (EffectiveEnumerations.least_settling_spec F).2.1 k s ((equiv s).mp hs)
  have test (s : ℕ) : eval A prefixFailureCode (Nat.pair (Nat.pair a k) s) =
      Part.some (if P s then 0 else 1) := by
    change (eval A prefixTestCode (Nat.pair (Nat.pair a k) s)).bind _ = _
    rw [prefix_test_eval, Part.bind_some, eval_embed, zeroTest_eval]
    change Part.some (if (if P s then 1 else 0) = 0 then 1 else 0) =
      Part.some (if P s then 0 else 1)
    by_cases hp : P s <;> simp [hp]
  have hi : eval A (.pair (.pair (OracleProgramNumberings.constantCode a)
      OracleProgramNumberings.identityCode) .zero) k = Part.some (Nat.pair (Nat.pair a k) 0) := by
    simp [eval, OracleProgramNumberings.constant_eval, OracleProgramNumberings.identity_eval]
  change (eval A (.pair (.pair (OracleProgramNumberings.constantCode a)
    OracleProgramNumberings.identityCode) .zero) k).bind _ = _
  rw [hi, Part.bind_some]
  apply Part.eq_some_iff.mpr
  rw [eval_find]
  refine ⟨Nat.zero_le _, ?_, ?_⟩
  · rw [test]
    change 0 ∈ Part.some (if P u then 0 else 1)
    rw [ite_eq_left hu]
    exact Part.mem_some 0
  · intro t _ htu
    have hnt : ¬ P t := fun h => Nat.not_le_of_gt htu (hmin t h)
    refine ⟨1, ?_, by decide⟩
    rw [test]
    rw [ite_eq_right hnt]
    exact Part.mem_some 1

def modulus (A : Set ℕ) (a e : ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom) (n : ℕ) : ℕ :=
  let k := HyperimmuneDegrees.leastAllowance A e ht n
  max k (EffectiveEnumerations.leastSettlingStage (EffectiveEnumerations.canonicalApproximation a) k)

def maxInput (w : ℕ) : ℕ := max w.unpair.1 w.unpair.2

theorem max_input_primitive : Primrec maxInput := by
  exact Primrec.nat_max.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

def modulusCode (a e : ℕ) : Code :=
  .comp (embed (ordinaryProgram maxInput max_input_primitive.to_comp))
    (.comp (.pair OracleProgramNumberings.identityCode (prefixSearchCode a))
      (HyperimmuneDegrees.allowanceProgram e))

theorem modulus_code_eval (A : Set ℕ) (a e : ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A) (n : ℕ) :
    eval A (modulusCode a e) n = Part.some (modulus A a e ht n) := by
  have hi : eval A (.pair OracleProgramNumberings.identityCode (prefixSearchCode a))
      (HyperimmuneDegrees.leastAllowance A e ht n) =
      Part.some (Nat.pair (HyperimmuneDegrees.leastAllowance A e ht n)
        (EffectiveEnumerations.leastSettlingStage (EffectiveEnumerations.canonicalApproximation a)
          (HyperimmuneDegrees.leastAllowance A e ht n))) := by
    simp [eval, OracleProgramNumberings.identity_eval, prefix_search_eval A a ha]
  change (eval A (.comp (.pair OracleProgramNumberings.identityCode (prefixSearchCode a))
    (HyperimmuneDegrees.allowanceProgram e)) n).bind _ = _
  change ((eval A (HyperimmuneDegrees.allowanceProgram e) n).bind _).bind _ = _
  rw [HyperimmuneDegrees.allowance_program_eval A e ht n, Part.bind_some, hi, Part.bind_some,
    eval_embed, BusyBeaverFunctions.ordinaryProgram_eval]
  simp only [maxInput, Nat.unpair_pair]
  rfl

theorem modulus_relative (A : Set ℕ) (a e : ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A) :
    PartialComputable A (fun n => Part.some (modulus A a e ht n)) := by
  exact ⟨modulusCode a e, funext (modulus_code_eval A a e ht ha)⟩

theorem approximation_modulus (A : Set ℕ) (a e : ℕ) (f : ℕ → ℕ)
    (ht : ∀ n, (OracleProgramNumberings.phi A e n).Dom)
    (ha : EffectiveEnumerations.indexSet a = A)
    (he : ∀ n, OracleProgramNumberings.phi A e n = Part.some (f n)) :
    ∀ n s, modulus A a e ht n ≤ s → approximation a e s n = f n := by
  intro n s hs
  let k := HyperimmuneDegrees.leastAllowance A e ht n
  let F := EffectiveEnumerations.canonicalApproximation a
  have hks : k ≤ s := (Nat.le_max_left _ _).trans hs
  have hts : EffectiveEnumerations.leastSettlingStage F k ≤ s := (Nat.le_max_right _ _).trans hs
  have hsettle : EffectiveEnumerations.Settles (EffectiveEnumerations.indexSet a)
      (EffectiveEnumerations.stage a) k s := by
    have h0 := (EffectiveEnumerations.least_settling_spec F).1 k
    have h1 := EffectiveEnumerations.settling_persists _ F.atStage
      (EffectiveEnumerations.approximation_stages F).2.1
      (EffectiveEnumerations.approximation_stages F).2.2 h0 hts
    have hF : F.atStage = EffectiveEnumerations.stage a :=
      funext (fun t => (EffectiveEnumerations.canonical_stages a t).2)
    rw [hF] at h1
    exact h1
  have hag : ∀ q < k, indicator A q = indicator (EffectiveEnumerations.stage a s) q := by
    intro q hq
    have hiff := hsettle q hq
    rw [ha] at hiff
    change (if q ∈ A then 1 else 0) = (if q ∈ EffectiveEnumerations.stage a s then 1 else 0)
    rw [hiff]
  have hk : OracleProgramNumberings.boundedValue A k e n = f n + 1 :=
    HyperimmuneDegrees.bounded_after_least A e ht n (f n) k
      (by rw [he]; exact Part.mem_some _) le_rfl
  have hbounded : OracleProgramNumberings.bounded (EffectiveEnumerations.stage a s) k
      (OracleProgramNumberings.decodeCode e) n = some (f n) := by
    change OracleProgramNumberings.boundedQ (indicator (EffectiveEnumerations.stage a s)) k
      (OracleProgramNumberings.decodeCode e) n = _
    rw [← PostsTheorem.bounded_query_dependence (indicator A)
      (indicator (EffectiveEnumerations.stage a s)) k hag]
    exact (OracleProgramNumberings.boundedValue_output A k e n (f n)).mp hk
  have hlarge := OracleProgramNumberings.bounded_monotone
    (indicator (EffectiveEnumerations.stage a s)) k (s-k)
    (OracleProgramNumberings.decodeCode e) n (f n) hbounded
  rw [Nat.add_sub_of_le hks] at hlarge
  have hv := (OracleProgramNumberings.boundedValue_output (EffectiveEnumerations.stage a s)
    s e n (f n)).mpr hlarge
  rw [approximation_bounded_identity, hv]
  omega

end
end Lemmatheca.ComputabilityTheory.ArslanovCompletenessCriterion
