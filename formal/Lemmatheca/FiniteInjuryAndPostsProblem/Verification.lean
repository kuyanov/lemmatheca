import Lemmatheca.FiniteInjuryAndPostsProblem.Effectivity
import Lemmatheca.FiniteInjuryAndPostsProblem.Invariants
import Lemmatheca.TuringDegrees.Reductions

/-! Actual finite injury, preserved observations, and satisfaction of all requirements. -/
namespace Lemmatheca.ComputabilityTheory.FiniteInjury

open PostsTheorem OracleComputation OracleProgramNumberings UniversalComputation

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false


private theorem no_action_of_flag_one {i s : ℕ} (hf : flag (stage s) i = 1) : ¬ Acts i s := by
  intro h
  obtain ⟨_, _, _, hz, _, _, _⟩ := acted_witness h
  omega

private theorem data_constant (i v : ℕ) (h : ∀ s ≥ v, ∀ j ≤ i, ¬ Acts j s) :
    ∀ t ≥ v, flag (stage t) i = flag (stage v) i ∧
      restraint (stage t) i = restraint (stage v) i := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ t ht ih =>
      obtain ⟨hf, hr⟩ := preserve_data (h t ht)
      exact ⟨hf.trans ih.1, hr.trans ih.2⟩

private theorem one_data_constant (i v : ℕ) (hf : flag (stage v) i = 1)
    (h : ∀ s ≥ v, ∀ j < i, ¬ Acts j s) :
    ∀ t ≥ v, flag (stage t) i = 1 ∧
      restraint (stage t) i = restraint (stage v) i := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨hf, rfl⟩
  | succ t ht ih =>
      have hn : ∀ j ≤ i, ¬ Acts j t := by
        intro j hji
        by_cases he : j = i
        · subst j
          exact no_action_of_flag_one ih.1
        · exact h t ht j (by omega)
      obtain ⟨hflag, hr⟩ := preserve_data hn
      exact ⟨hflag.trans ih.1, hr.trans ih.2⟩

private theorem uninjured_data {i s : ℕ} (h : Acts i s)
    (hh : ∀ t, s < t → ∀ j < i, ¬ Acts j t) :
    ∀ t ≥ s + 1, flag (stage t) i = 1 ∧ restraint (stage t) i = s + 1 := by
  obtain ⟨hf, hr⟩ := acted_data h
  intro t ht
  obtain ⟨hflag, hrest⟩ := one_data_constant i (s + 1) hf
    (fun u hu j hj => hh u (by omega) j hj) t ht
  exact ⟨hflag, hrest.trans hr⟩

private theorem eventual_no_own (i v : ℕ)
    (hh : ∀ s ≥ v, ∀ j < i, ¬ Acts j s) :
    ∃ t ≥ v, ∀ s ≥ t, ¬ Acts i s := by
  by_cases ha : ∃ s ≥ v, Acts i s
  · obtain ⟨s, hs, hact⟩ := ha
    refine ⟨s + 1, by omega, ?_⟩
    intro t ht
    exact no_action_of_flag_one
      ((uninjured_data hact (fun u hu j hj => hh u (by omega) j hj) t ht).1)
  · exact ⟨v, le_rfl, fun s hs hi => ha ⟨s, hs, hi⟩⟩

private theorem oracle_code_stage (i s : ℕ) :
    finiteOracle (oracleCode (stage s) i) = oracleStage i s := by
  by_cases h : i % 2 = 0 <;> simp [oracleCode, oracleStage, leftStage, rightStage, h]

private theorem target_code_stage (i s : ℕ) :
    finiteOracle (targetCode (stage s) i) = targetStage i s := by
  by_cases h : i % 2 = 0 <;> simp [targetCode, targetStage, leftStage, rightStage, h]

private theorem oracle_beta_indicator (i s q : ℕ) :
    beta (oracleCode (stage s) i) q = indicator (fun x => x ∈ oracleStage i s) q := by
  have h := (finiteOracle_indicator (oracleCode (stage s) i) q).symm
  rwa [oracle_code_stage] at h

private theorem indicator_agreement (A B : Set ℕ) (q : ℕ) (h : q ∈ A ↔ q ∈ B) :
    indicator (fun x => x ∈ A) q = indicator (fun x => x ∈ B) q := by
  by_cases ha : q ∈ A <;> by_cases hb : q ∈ B <;> simp_all [indicator]

private theorem requirement_iff (i : ℕ) : Requirement i ↔
    ∃ x, OracleProgramNumberings.phi (oracleSet i) (i / 2) x ≠
      Part.some (indicator (targetSet i) x) := by
  rfl

private theorem small_oracle_step (i u k : ℕ)
    (hrest : k ≤ restraint (stage u) i) (hno : ∀ j ≤ i, ¬ Acts j u) :
    ∀ q < k, (q ∈ oracleStage i (u + 1) ↔ q ∈ oracleStage i u) := by
  intro q hq
  have hn : ¬(HasAction u (stage u) ∧ q = witnessAt u) := by
    rintro ⟨ha, hw⟩
    let j := priority u (stage u)
    have hj : Acts j u := (acts_iff j u).mpr ⟨ha, rfl⟩
    have hij : i < j := by
      by_contra h
      exact hno j (by omega) hj
    have hr := (acted_witness hj).2.2.2.2.2.1 i hij
    omega
  have hl : leftBit (u + 1) q = leftBit u q := by
    rw [left_bit_succ]
    have hc : ¬(HasAction u (stage u) ∧ priority u (stage u) % 2 = 0 ∧ q = witnessAt u) :=
      fun h => hn ⟨h.1, h.2.2⟩
    rw [ite_eq_right hc]
  have hr : rightBit (u + 1) q = rightBit u q := by
    rw [right_bit_succ]
    have hc : ¬(HasAction u (stage u) ∧ priority u (stage u) % 2 ≠ 0 ∧ q = witnessAt u) :=
      fun h => hn ⟨h.1, h.2.2⟩
    rw [ite_eq_right hc]
  by_cases hp : i % 2 = 0
  · simp only [oracleStage, ite_eq_left hp, rightStage, finiteOracle, Set.mem_ofPred_eq]
    change rightBit (u + 1) q = 1 ↔ rightBit u q = 1
    rw [hr]
  · simp only [oracleStage, ite_eq_right hp, leftStage, finiteOracle, Set.mem_ofPred_eq]
    change leftBit (u + 1) q = 1 ↔ leftBit u q = 1
    rw [hl]

theorem eventual_no_actions (i : ℕ) :
    ∃ v, ∀ s ≥ v, ∀ j ≤ i, ¬ Acts j s := by
  induction i with
  | zero =>
      obtain ⟨v, _, hv⟩ := eventual_no_own 0 0 (fun _ _ j hj => False.elim (Nat.not_lt_zero j hj))
      refine ⟨v, fun s hs j hj => ?_⟩
      have he : j = 0 := by omega
      subst j
      exact hv s hs
  | succ i ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨t, hvt, ht⟩ := eventual_no_own (i + 1) v
        (fun s hs j hj => hv s hs j (by omega))
      refine ⟨t, fun s hs j hj => ?_⟩
      by_cases he : j = i + 1
      · subst j
        exact ht s hs
      · exact hv s (by omega) j (by omega)

theorem eventual_data (i : ℕ) : ∃ v, ∀ s ≥ v,
    flag (stage s) i = flag (stage v) i ∧
      restraint (stage s) i = restraint (stage v) i := by
  obtain ⟨v, hv⟩ := eventual_no_actions i
  exact ⟨v, data_constant i v hv⟩

theorem after_action_data {i s : ℕ} (h : Acts i s)
    (hh : ∀ t, s < t → ∀ j < i, ¬ Acts j t) :
    ∀ t ≥ s + 1, flag (stage t) i = 1 ∧ restraint (stage t) i = s + 1 := by
  exact uninjured_data h hh

theorem acted_oracle_stable {i s : ℕ} (h : Acts i s)
    (hh : ∀ t, s < t → ∀ j < i, ¬ Acts j t) :
    (∀ t ≥ s, ∀ q < s + 1, (q ∈ oracleStage i t ↔ q ∈ oracleStage i s)) ∧
      Agreement (oracleCode (stage s) i) (s + 1) (oracleSet i) := by
  have hfinite : ∀ t ≥ s, ∀ q < s + 1,
      (q ∈ oracleStage i t ↔ q ∈ oracleStage i s) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact fun _ _ => Iff.rfl
    | succ u hu ih =>
        intro q hq
        by_cases he : u = s
        · subst u
          rw [(acted_stage_updates h).2]
        · have hsu : s + 1 ≤ u := by omega
          obtain ⟨hf, hr⟩ := after_action_data h hh u hsu
          have hn : ∀ j ≤ i, ¬ Acts j u := by
            intro j hji
            by_cases hj : j = i
            · subst j
              exact no_action_of_flag_one hf
            · exact hh u (by omega) j (by omega)
          exact (small_oracle_step i u (s + 1) (by omega) hn q hq).trans (ih q hq)
  refine ⟨hfinite, ?_⟩
  intro q hq
  have hm : q ∈ oracleStage i s ↔ q ∈ oracleSet i := by
    constructor
    · intro hs
      exact (oracle_stage_union i q).mpr ⟨s, hs⟩
    · intro hf
      obtain ⟨u, hu⟩ := (oracle_stage_union i q).mp hf
      have hmax := oracle_stage_monotone i (Nat.le_max_left u s) hu
      exact (hfinite (max u s) (Nat.le_max_right _ _) q hq).mp hmax
  exact (oracle_beta_indicator i s q).trans (indicator_agreement _ _ q hm)

theorem acted_requirement {i s : ℕ} (h : Acts i s)
    (hh : ∀ t, s < t → ∀ j < i, ¬ Acts j t) : Requirement i := by
  obtain ⟨_, _, _, _, _, _, hv⟩ := acted_witness h
  have ha := (acted_oracle_stable h hh).2
  have hout : 0 ∈ OracleProgramNumberings.phi (oracleSet i) (i / 2) (witnessAt s) :=
    (finite_certificate_output (oracleSet i) (i / 2) (witnessAt s) 0).mpr
      ⟨oracleCode (stage s) i, s + 1, hv, ha⟩
  have hmem : witnessAt s ∈ targetSet i :=
    (target_stage_union i (witnessAt s)).mpr ⟨s + 1, by rw [(acted_stage_updates h).1]; simp⟩
  have hi : indicator (targetSet i) (witnessAt s) = 1 := by
    have hm : targetSet i (witnessAt s) := hmem
    simp [indicator, hm]
  apply (requirement_iff i).mpr
  refine ⟨witnessAt s, ?_⟩
  intro heq
  have hnum : (0 : ℕ) = 1 := Part.some_injective
    ((Part.eq_some_iff.mpr hout).symm.trans (heq.trans (congrArg Part.some hi)))
  omega

theorem eventual_oracle_agreement (i k : ℕ) :
    ∃ v, ∀ s ≥ v, Agreement (oracleCode (stage s) i) k (oracleSet i) := by
  obtain ⟨v, hv⟩ := EffectiveEnumerations.prefix_settled_exists
    (oracleSet i) (oracleStage i) (oracle_stage_monotone i) (oracle_stage_union i) k
  refine ⟨v, fun s hs q hq => ?_⟩
  have hm := EffectiveEnumerations.settling_persists (oracleSet i) (oracleStage i)
    (oracle_stage_monotone i) (oracle_stage_union i) hv hs q hq
  exact (oracle_beta_indicator i s q).trans (indicator_agreement _ _ q hm.symm)

theorem eventual_zero_observation (i x : ℕ)
    (h : OracleProgramNumberings.phi (oracleSet i) (i / 2) x = Part.some 0) :
    ∃ v, ∀ s ≥ v, finiteValue (oracleCode (stage s) i) (s + 1) (i / 2) x = 1 := by
  let c := decodeCode (i / 2)
  have hval : 0 ∈ eval (oracleSet i) c x := Part.eq_some_iff.mp h
  obtain ⟨k, hk⟩ := (bounded_complete (oracleSet i) c x 0).mp hval
  have hbound : OracleProgramNumberings.boundedValue (oracleSet i) k (i / 2) x = 1 :=
    (OracleProgramNumberings.boundedValue_output _ _ _ _ _).mpr hk
  obtain ⟨v, hv⟩ := eventual_oracle_agreement i k
  refine ⟨max v k, fun s hs => ?_⟩
  let u := oracleCode (stage s) i
  have hfinite : finiteValue u k (i / 2) x = 1 :=
    (finiteValue_agreement (oracleSet i) u k (i / 2) x (hv s (by omega))).trans hbound
  have hfixed : bounded (finiteOracle u) k c x = some 0 :=
    (OracleProgramNumberings.boundedValue_output _ _ _ _ _).mp
      ((finiteValue_identity u k (i / 2) x).symm.trans hfinite)
  rw [finiteValue_identity]
  apply (OracleProgramNumberings.boundedValue_output _ _ _ _ _).mpr
  have hle : k ≤ s + 1 := by omega
  simpa only [bounded, Nat.add_sub_of_le hle] using
    bounded_monotone (indicator (fun q => q ∈ finiteOracle u)) k (s + 1 - k) c x 0 hfixed

theorem private_waiting_absence (i v : ℕ)
    (h : ∀ s ≥ v, ¬ Acts i s) : Nat.pair i (v + 1) ∉ targetSet i := by
  have hx := private_large_witness i v
  intro hm
  obtain ⟨t, ht, hw⟩ := (private_union_source hx.1).mp hm
  have htv : t < v := by
    by_contra hn
    exact h t (by omega) ht
  have hbound := (acted_witness ht).2.1
  omega

theorem waiting_data (i v : ℕ) (hd : flag (stage v) i = 0)
    (h : ∀ s ≥ v, ∀ j ≤ i, ¬ Acts j s) :
    ∀ s ≥ v, flag (stage s) i = 0 ∧ ∀ j < i, restraint (stage s) j ≤ v := by
  intro s hs
  have hc := data_constant i v h s hs
  refine ⟨hc.1.trans hd, ?_⟩
  intro j hji
  have hj := data_constant j v (fun t ht k hk => h t ht k (by omega)) s hs
  exact hj.2.trans_le (restraints_bounded v j)

theorem waiting_requirement (i v : ℕ) (hd : flag (stage v) i = 0)
    (h : ∀ s ≥ v, ∀ j ≤ i, ¬ Acts j s) : Requirement i := by
  let x := Nat.pair i (v + 1)
  have hx := private_large_witness i v
  have hnot : x ∉ targetSet i := private_waiting_absence i v (fun s hs => h s hs i le_rfl)
  apply (requirement_iff i).mpr
  refine ⟨x, ?_⟩
  have hi : indicator (targetSet i) x = 0 := by
    have hn : ¬targetSet i x := hnot
    simp [indicator, hn]
  intro heq
  have hout : OracleProgramNumberings.phi (oracleSet i) (i / 2) x = Part.some 0 :=
    heq.trans (congrArg Part.some hi)
  obtain ⟨u, hu⟩ := eventual_zero_observation i x hout
  let s := max v (max u (max i x))
  have hvs : v ≤ s := by dsimp [s]; omega
  have his : i ≤ s := by dsimp [s]; omega
  have hxs : x ≤ s := by dsimp [s]; omega
  have hflag := (waiting_data i v hd h s hvs).1
  have htarget : beta (targetCode (stage s) i) x = 0 := by
    have hm : x ∉ finiteOracle (targetCode (stage s) i) := by
      rw [target_code_stage]
      intro ht
      exact hnot ((target_stage_union i x).mpr ⟨s, ht⟩)
    have hn : beta (targetCode (stage s) i) x ≠ 1 := hm
    exact (beta_bits _ _).resolve_right hn
  have helig : Eligible s (stage s) i x :=
    ⟨his, hxs, hx.1, hflag, htarget,
      fun j hj => le_trans ((waiting_data i v hd h s hvs).2 j hj) (by dsimp [x]; omega),
      hu s (by dsimp [s]; omega)⟩
  obtain ⟨ha, hpi⟩ := priority_minimal s (stage s) i x helig
  have hacts : Acts (priority s (stage s)) s :=
    (acts_iff _ _).mpr ⟨ha, rfl⟩
  exact h s hvs _ hpi hacts

theorem all_requirements : ∀ i, Requirement i := by
  intro i
  obtain ⟨v, hv⟩ := eventual_no_actions i
  rcases flag_binary v i with hz | ho
  · exact waiting_requirement i v hz hv
  · obtain ⟨t, htv, ht, _, hbetween⟩ := flag_provenance v i ho
    apply acted_requirement ht
    intro u htu j hji
    by_cases huv : u < v
    · exact hbetween u htu huv j hji
    · exact hv u (by omega) j (by omega)

theorem requirements_imply_incomparable (A B : Set ℕ) (h : ∀ i, RequirementFor A B i) :
    ¬ TuringDegrees.Reducible A B ∧ ¬ TuringDegrees.Reducible B A := by
  constructor
  · rintro ⟨c, hc⟩
    let e := encodeCode c
    obtain ⟨x, hx⟩ := h (2 * e)
    have hmod : (2 * e) % 2 = 0 := by omega
    have hdiv : (2 * e) / 2 = e := by omega
    simp only [hmod, hdiv] at hx
    apply hx
    have he : decodeCode e = c := decode_encode c
    exact (congrArg (fun d => eval B d x) he).trans (hc x)
  · rintro ⟨c, hc⟩
    let e := encodeCode c
    obtain ⟨x, hx⟩ := h (2 * e + 1)
    have hmod : (2 * e + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * e + 1) / 2 = e := by omega
    simp only [hmod, hdiv] at hx
    apply hx
    have he : decodeCode e = c := decode_encode c
    exact (congrArg (fun d => eval A d x) he).trans (hc x)

theorem friedberg_muchnik :
    REPred leftSet ∧ REPred rightSet ∧
      ¬ TuringDegrees.Reducible leftSet rightSet ∧
      ¬ TuringDegrees.Reducible rightSet leftSet := by
  obtain ⟨hAB, hBA⟩ := requirements_imply_incomparable leftSet rightSet all_requirements
  exact ⟨constructed_enumerable.1, constructed_enumerable.2, hAB, hBA⟩

end
end Lemmatheca.ComputabilityTheory.FiniteInjury
