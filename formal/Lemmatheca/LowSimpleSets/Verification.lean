import Lemmatheca.LowSimpleSets.Construction
import Lemmatheca.SimpleSets.Immunity
import Lemmatheca.LimitComputability.LimitLemma
import Mathlib.Order.Interval.Set.Nat

/-! Finite positive action, stable certificates, and the low simple conclusion. -/
namespace Lemmatheca.ComputabilityTheory.LowSimpleSets

open PostsTheorem UniversalComputation OracleComputation OracleProgramNumberings
  EffectiveEnumerations TuringDegrees TuringJump LimitComputability SimpleSets

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

private theorem stage_subset (s : ℕ) : stageSet s ⊆ constructedSet :=
  fun _ h => ⟨s, h⟩

private theorem stage_cover (x : ℕ) : x ∈ constructedSet ↔ ∃ s, x ∈ stageSet s := Iff.rfl

private theorem bit_indicator (s q : ℕ) :
    stageBit s q = indicator (stageSet s) q :=
  (finiteOracle_indicator (aCode (stage s)) q).symm

theorem constructed_enumerable : REPred constructedSet := by
  apply approximation_enumerable
  exact ⟨id, stageBit, Computable.id, stage_data_primitive.1.to_comp,
    fun s => (state_invariants s).2.2.2.2.1,
    fun s => (state_invariants s).2.2.1,
    fun s x hx => stage_monotone (Nat.le_succ s) hx,
    fun _ => Iff.rfl⟩

theorem prefix_settles (k : ℕ) :
    ∃ t, ∀ s ≥ t, Agreement (aCode (stage s)) k constructedSet := by
  obtain ⟨t, ht⟩ := prefix_settled_exists constructedSet stageSet stage_monotone stage_cover k
  refine ⟨t, fun s hs q hq => ?_⟩
  have hm := settling_persists constructedSet stageSet stage_monotone stage_cover ht hs q hq
  change stageBit s q = indicator constructedSet q
  rw [bit_indicator]
  change (if q ∈ stageSet s then 1 else 0) = if q ∈ constructedSet then 1 else 0
  simp only [← hm]

private theorem action_not_later {e s t : ℕ} (hs : Acts e s) (hst : s < t) : ¬ Acts e t := by
  intro ht
  obtain ⟨_, hw, _, hwW, _, hu, _⟩ := positive_action_data hs
  have hel := (attention_data t (stage t)).2 ht.1 |>.1
  rw [ht.2] at hel
  have hnom := hel.2.2.2.2.1
  have hwA : witnessAt s ∈ stageSet t := stage_monotone (show s + 1 ≤ t by omega)
    (by rw [hu]; exact Set.mem_insert _ _)
  have hwWt : witnessAt s ∈ EffectiveEnumerations.stage e (t + 1) :=
    EffectiveEnumerations.stage_monotone e (by omega) hwW
  exact hnom (witnessAt s) (by omega)
    ⟨hwA, (stage_test_spec e (t + 1) _).2.mpr hwWt⟩

theorem action_at_most_once {e s t : ℕ} (hs : Acts e s) (ht : Acts e t) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (action_not_later hs h ht)
  · exact h
  · exact False.elim (action_not_later ht h hs)

private theorem own_actions_end (e : ℕ) : ∃ t, ∀ s ≥ t, ¬ Acts e s := by
  by_cases h : ∃ t, Acts e t
  · obtain ⟨t, ht⟩ := h
    exact ⟨t + 1, fun s hs => action_not_later ht (by omega)⟩
  · exact ⟨0, fun s _ hs => h ⟨s, hs⟩⟩

theorem eventual_no_actions (e : ℕ) :
    ∃ t, ∀ s ≥ t, ∀ i ≤ e, ¬ Acts i s := by
  induction e with
  | zero =>
      obtain ⟨t, ht⟩ := own_actions_end 0
      refine ⟨t, fun s hs i hi => ?_⟩
      have he : i = 0 := by omega
      subst i
      exact ht s hs
  | succ e ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨u, hu⟩ := own_actions_end (e + 1)
      refine ⟨max t u, fun s hs i hi => ?_⟩
      by_cases he : i = e + 1
      · subst i
        exact hu s (by omega)
      · exact ht s (by omega) i (by omega)

private theorem temporary_unchanged (s i : ℕ)
    (hno : ∀ e ≤ i, ¬ Acts e s) : temporary s (stage s) i = stageRecord s i := by
  have hn : ¬(HasAction s (stage s) ∧ priority s (stage s) ≤ i) := by
    rintro ⟨ha, hp⟩
    exact hno _ hp ⟨ha, rfl⟩
  exact ite_eq_right hn

private theorem record_step_positive (s i : ℕ) (hi : i < s + 1)
    (hp : 0 < stageRecord s i) (hno : ∀ e ≤ i, ¬ Acts e s) :
    stageRecord (s + 1) i = stageRecord s i := by
  rw [record_update s i hi, fill, temporary_unchanged s i hno, ite_eq_left hp]

private theorem record_constant (i t k : ℕ) (hi : i < t)
    (hk : stageRecord t i = k) (hp : 0 < k)
    (hno : ∀ s ≥ t, ∀ e ≤ i, ¬ Acts e s) : ∀ s ≥ t, stageRecord s i = k := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact hk
  | succ s hs ih =>
      exact (record_step_positive s i (by omega) (by omega) (hno s hs)).trans ih

theorem records_stabilize (i : ℕ) :
    ∃ t k, ∀ s ≥ t, stageRecord s i = k := by
  obtain ⟨t, ht⟩ := eventual_no_actions i
  let v := max t (i + 1)
  by_cases hp : ∃ s ≥ v, 0 < stageRecord s i
  · obtain ⟨s, hs, hpos⟩ := hp
    exact ⟨s, stageRecord s i, record_constant i s _ (by omega) rfl hpos
      (fun u hu => ht u (by omega))⟩
  · refine ⟨v, 0, fun s hs => ?_⟩
    have hz : ¬ 0 < stageRecord s i := fun h => hp ⟨s, hs, h⟩
    omega

private theorem higher_records_bound (e : ℕ) :
    ∃ v, ∀ s ≥ v, ∀ i < e, stageRecord s i ≤ v := by
  induction e with
  | zero => exact ⟨0, by intro s hs i hi; omega⟩
  | succ e ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨t, k, ht⟩ := records_stabilize e
      have hk : k ≤ t := by
        have hb := (state_invariants t).2.2.2.2.2.1 e
        rw [ht t le_rfl] at hb
        exact hb
      refine ⟨max v t, fun s hs i hi => ?_⟩
      by_cases he : i = e
      · subst i
        rw [ht s (by omega)]
        omega
      · have hb := hv s (by omega) i (by omega)
        omega

theorem meets_infinite (e : ℕ) (he : (indexSet e).Infinite) :
    (indexSet e ∩ constructedSet).Nonempty := by
  by_contra hn
  obtain ⟨v, hv⟩ := higher_records_bound e
  obtain ⟨t, ht⟩ := eventual_no_actions e
  obtain ⟨x, hxW, hx⟩ := he.exists_gt (max (2 * e) v)
  obtain ⟨u, hu⟩ := (stage_union e x).mp hxW
  let s := max (max v t) (max e (max x u))
  have hvs : v ≤ s := by dsimp [s]; omega
  have hts : t ≤ s := by dsimp [s]; omega
  have hes : e ≤ s := by dsimp [s]; omega
  have hxs : x ≤ s := by dsimp [s]; omega
  have hus : u ≤ s + 1 := by dsimp [s]; omega
  have hW : stageTest e (s + 1) x = 1 :=
    (stage_test_spec e (s + 1) x).2.mpr (EffectiveEnumerations.stage_monotone e hus hu)
  have hnom : NoMeeting s (stage s) e := by
    intro y hy hym
    have hyW : y ∈ indexSet e := (stage_union e y).mpr
      ⟨s + 1, (stage_test_spec e (s + 1) y).2.mp hym.2⟩
    exact hn ⟨y, hyW, stage_subset s hym.1⟩
  have hel : Eligible s (stage s) e x :=
    ⟨hes, hxs, hW, by omega, hnom, fun i hi => (hv s hvs i hi).trans (by omega)⟩
  have ha := (attention_data s (stage s)).1.mpr ⟨e, x, hel⟩
  have hp := ((attention_data s (stage s)).2 ha).2 e x hel |>.1
  exact ht s hts _ hp ⟨ha, rfl⟩

private theorem member_produced {x : ℕ} (hx : x ∈ constructedSet) :
    ∃ e s, Acts e s ∧ witnessAt s = x := by
  obtain ⟨s, hs⟩ := hx
  induction s with
  | zero => simp [stageSet, stage, aCode, finiteOracle, beta, FiniteSequenceCoding.entry] at hs
  | succ s ih =>
      rw [stage_set_succ] at hs
      split_ifs at hs with ha
      · rcases hs with hx | hx
        · exact ⟨priority s (stage s), s, ⟨ha, rfl⟩, hx.symm⟩
        · exact ih hx
      · exact ih hs

private theorem small_producer {n x : ℕ} (hx : x ∈ constructedSet ∩ Set.Iic (2 * n)) :
    ∃ e, e < n ∧ ∃ s, Acts e s ∧ witnessAt s = x := by
  obtain ⟨e, s, he, hxw⟩ := member_produced hx.1
  have hb := (positive_action_data he).2.2.1
  rw [hxw] at hb
  exact ⟨e, by have hxn : x ≤ 2 * n := hx.2; omega, s, he, hxw⟩

private noncomputable def countingMap (n : ℕ)
    (x : ↥(constructedSet ∩ Set.Iic (2 * n))) : Fin n :=
  ⟨Nat.find (small_producer x.property), (Nat.find_spec (small_producer x.property)).1⟩

private theorem countingMap_injective (n : ℕ) : Function.Injective (countingMap n) := by
  intro x y hxy
  apply Subtype.ext
  have he : Nat.find (small_producer x.property) = Nat.find (small_producer y.property) :=
    congrArg Fin.val hxy
  obtain ⟨s, hs, hx⟩ := (Nat.find_spec (small_producer x.property)).2
  obtain ⟨t, ht, hy⟩ := (Nat.find_spec (small_producer y.property)).2
  rw [← he] at ht
  have hst := action_at_most_once hs ht
  subst t
  exact hx.symm.trans hy

theorem small_set_bound (n : ℕ) :
    (constructedSet ∩ Set.Iic (2 * n)).Finite ∧
      (constructedSet ∩ Set.Iic (2 * n)).ncard ≤ n := by
  refine ⟨(Set.finite_Iic (2 * n)).subset Set.inter_subset_right, ?_⟩
  simpa only [Nat.card_coe_set_eq, Nat.card_fin] using
    Nat.card_le_card_of_injective (countingMap n) (countingMap_injective n)

theorem complement_infinite : constructedSetᶜ.Infinite := by
  have omissions (n : ℕ) : n + 1 ≤ (constructedSetᶜ ∩ Set.Iic (2 * n)).ncard := by
    have hcard := Set.ncard_inter_add_ncard_sdiff_eq_ncard
      (Set.Iic (2 * n)) constructedSet (Set.finite_Iic (2 * n))
    have hselected := (small_set_bound n).2
    have htotal : (constructedSet ∩ Set.Iic (2 * n)).ncard +
        (constructedSetᶜ ∩ Set.Iic (2 * n)).ncard = 2 * n + 1 := by
      simpa only [Set.inter_comm, Set.sdiff_eq, Set.ncard_Iic_nat] using hcard
    omega
  intro hfin
  have hbound := omissions constructedSetᶜ.ncard
  have hle := Set.ncard_le_ncard
    (show constructedSetᶜ ∩ Set.Iic (2 * constructedSetᶜ.ncard) ⊆ constructedSetᶜ from
      Set.inter_subset_left) hfin
  omega

theorem constructed_simple : Simple constructedSet := by
  exact (simple_iff_meets constructedSet constructed_enumerable complement_infinite).mpr meets_infinite

private theorem protected_bit_step (i s k : ℕ) (hk : stageRecord s i = k)
    (hno : ∀ e ≤ i, ¬ Acts e s) : ∀ q < k, stageBit (s + 1) q = stageBit s q := by
  intro q hq
  rw [stage_bit_succ]
  have hn : ¬(HasAction s (stage s) ∧ q = witnessAt s) := by
    rintro ⟨ha, hqw⟩
    have hia : i < priority s (stage s) := by
      by_contra hn
      exact hno _ (by omega) ⟨ha, rfl⟩
    have hb := (positive_action_data (show Acts (priority s (stage s)) s from ⟨ha, rfl⟩)).2.2.2.2.2.2 i hia
    rw [hk, ← hqw] at hb
    omega
  exact ite_eq_right hn

theorem persistent_certificate (i t k : ℕ) (hi : i < t)
    (hk : stageRecord t i = k) (hpos : 0 < k)
    (hno : ∀ s ≥ t, ∀ e ≤ i, ¬ Acts e s) :
    (∀ s ≥ t, stageRecord s i = k) ∧ i ∈ jump constructedSet := by
  have hr := record_constant i t k hi hk hpos hno
  have hb : ∀ s ≥ t, ∀ q < k, stageBit s q = stageBit t q := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ s hs ih =>
        exact fun q hq => (protected_bit_step i s k (hr s hs) (hno s hs) q hq).trans (ih q hq)
  have ha : Agreement (aCode (stage t)) k constructedSet := by
    intro q hq
    change stageBit t q = indicator constructedSet q
    rw [bit_indicator]
    have he : q ∈ stageSet t ↔ q ∈ constructedSet := by
      refine ⟨fun hx => stage_subset t hx, ?_⟩
      rintro ⟨s, hs⟩
      by_cases hst : s ≤ t
      · exact stage_monotone hst hs
      · have hbit := hb s (by omega) q hq
        change stageBit s q = 1 at hs
        change stageBit t q = 1
        omega
    change (if q ∈ stageSet t then 1 else 0) = if q ∈ constructedSet then 1 else 0
    simp only [he]
  refine ⟨hr, (jump_certificate constructedSet i).mpr ⟨k, ?_⟩⟩
  rw [← finiteValue_agreement constructedSet (aCode (stage t)) k i i ha]
  have hc := (state_invariants t).2.2.2.2.2.2 i (by omega)
  rwa [hk] at hc

private theorem eventual_observation (i : ℕ) (hi : i ∈ jump constructedSet) :
    ∃ v, ∀ s ≥ v, 0 < finiteValue (aCode (stage (s + 1))) (s + 1) i i := by
  obtain ⟨k, hk⟩ := (jump_certificate constructedSet i).mp hi
  let y := boundedValue constructedSet k i i - 1
  have hy : boundedValue constructedSet k i i = y + 1 := by dsimp [y]; omega
  obtain ⟨t, ht⟩ := prefix_settles k
  refine ⟨max t k, fun s hs => ?_⟩
  let u := aCode (stage (s + 1))
  have hfinite : finiteValue u k i i = y + 1 :=
    (finiteValue_agreement constructedSet u k i i (ht (s + 1) (by omega))).trans hy
  have hfixed : bounded (finiteOracle u) k (decodeCode i) i = some y :=
    (boundedValue_output _ _ _ _ _).mp ((finiteValue_identity u k i i).symm.trans hfinite)
  have hle : k ≤ s + 1 := by omega
  have hlarge : bounded (finiteOracle u) (s + 1) (decodeCode i) i = some y := by
    simpa only [bounded, Nat.add_sub_of_le hle] using
      bounded_monotone (indicator (fun q => q ∈ finiteOracle u)) k (s + 1 - k) (decodeCode i) i y hfixed
  have hout : finiteValue u (s + 1) i i = y + 1 :=
    (finiteValue_identity u (s + 1) i i).trans ((boundedValue_output _ _ _ _ _).mpr hlarge)
  change 0 < finiteValue u (s + 1) i i
  omega

theorem jump_guess_data :
    Computable₂ jumpGuess ∧ Binary jumpGuess ∧ Converges jumpGuess (jump constructedSet) := by
  have hg : Primrec₂ jumpGuess :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) stage_data_primitive.2)
      (Primrec.const 1) (Primrec.const 0)
  refine ⟨hg.to_comp, ?_, ?_⟩
  · intro s i
    unfold jumpGuess
    split_ifs <;> simp
  · intro i
    obtain ⟨t, k, ht⟩ := records_stabilize i
    obtain ⟨u, hu⟩ := eventual_no_actions i
    let v := max (max t u) (i + 1)
    have htv : t ≤ v := by dsimp [v]; omega
    have huv : u ≤ v := by dsimp [v]; omega
    have hiv : i < v := by dsimp [v]; omega
    by_cases hk : k = 0
    · subst k
      have hnot : i ∉ jump constructedSet := by
        intro hi
        obtain ⟨w, hw⟩ := eventual_observation i hi
        let s := max v w
        have hvs : v ≤ s := Nat.le_max_left _ _
        have hs0 : stageRecord s i = 0 := ht s (by omega)
        have hn0 : stageRecord (s + 1) i = 0 := ht (s + 1) (by omega)
        have htemp : temporary s (stage s) i = 0 :=
          (temporary_unchanged s i (hu s (by omega))).trans hs0
        have hval := hw s (Nat.le_max_right _ _)
        have hv : 0 < finiteValue (nextACode s (stage s)) (s + 1) i i := hval
        rw [record_update s i (by omega), fill, htemp] at hn0
        simp [hv] at hn0
      refine ⟨v, fun s hs => ?_⟩
      have hz := ht s (by omega)
      have hfun : ¬ jump constructedSet i := hnot
      simp [jumpGuess, hz, indicator, hfun]
    · have hp : 0 < k := by omega
      have hi := (persistent_certificate i v k hiv (ht v htv) hp
        (fun s hs => hu s (by omega))).2
      refine ⟨v, fun s hs => ?_⟩
      have hz := ht s (by omega)
      have hfun : jump constructedSet i := hi
      simp [jumpGuess, hz, hp, indicator, hfun]

theorem constructed_low : Low constructedSet := by
  exact (low_iff_jump_below_halting constructedSet).mpr
    ((limit_lemma (jump constructedSet)).mp ⟨jumpGuess, jump_guess_data⟩)

end
end Lemmatheca.ComputabilityTheory.LowSimpleSets
