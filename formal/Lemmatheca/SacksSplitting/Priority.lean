import Lemmatheca.SacksSplitting.Effectivity

/-! Permanent protection and the ordinary decoder in the priority induction. -/
namespace Lemmatheca.ComputabilityTheory.SacksSplitting

open PostsTheorem UniversalComputation LimitComputability OracleProgramNumberings

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def HigherStable (a : ℕ) (h : Approximation) (q : ℕ) : Prop :=
  ∀ p < q, ∃ T u, ∀ s ≥ T, restraintAt a h s p = u

def Cutoff (a : ℕ) (h : Approximation) (q T : ℕ) : Prop :=
  q ≤ T ∧ ∀ s ≥ T, FriedbergSplitting.HasArrival a s →
    ∀ p < q, restraintAt a h (s + 1) p ≤ FriedbergSplitting.arrival a s

def expansionSearch (a : ℕ) (h : Approximation) (q T x : ℕ) : Part ℕ :=
  Nat.rfind fun n => Part.some (decide
    (Expanded a h q (T + n) ∧ x ≤ lengthAt a h (T + n) q))

def expansionDecoder (a : ℕ) (h : Approximation) (q T x : ℕ) : Part ℕ :=
  (expansionSearch a h q T x).map (fun n => h (T + n) x)

theorem higher_cutoff (a : ℕ) (h : Approximation) (q : ℕ)
    (hhigher : HigherStable a h q) : ∃ T, Cutoff a h q T := by
  revert hhigher
  induction q with
  | zero =>
      intro _
      exact ⟨0, le_rfl, fun _ _ _ p hp => by omega⟩
  | succ q ih =>
      intro hhigher
      obtain ⟨T, hT⟩ := ih (fun p hp => hhigher p (by omega))
      obtain ⟨v, u, hu⟩ := hhigher q (by omega)
      obtain ⟨w, hw⟩ := FriedbergSplitting.arrival_escape a u
      refine ⟨max (q + 1) (max T (max v w)), le_max_left _ _, ?_⟩
      intro s hs ha p hp
      by_cases hpq : p < q
      · exact hT.2 s (by omega) ha p hpq
      · have he : p = q := by omega
        subst p
        rw [hu (s + 1) (by omega)]
        exact hw s (by omega) ha

private theorem threatening_priority (a : ℕ) (h : Approximation) (q T s : ℕ)
    (hT : Cutoff a h q T) (hs : T ≤ s) (ha : FriedbergSplitting.HasArrival a s)
    (hq : FriedbergSplitting.arrival a s < restraintAt a h (s + 1) q) :
    priority a h s (stage a h s) = q := by
  have hp := priority_data a h s (stage a h s)
  have hactive : q ≤ s := le_trans hT.1 hs
  have hupdated : FriedbergSplitting.arrival a s < nextRestraint h s (stage a h s) q := by
    rwa [← (record_update a h s q).2]
  have hprio : priority a h s (stage a h s) < s + 1 := by
    by_contra hn
    have he : priority a h s (stage a h s) = s + 1 := by omega
    have hb := hp.2.2.2.mp he q (by omega)
    omega
  have hd := hp.2.2.1 hprio
  apply le_antisymm
  · by_contra hn
    have hb := hd.2 q (by omega)
    omega
  · by_contra hn
    have hb := hT.2 s hs ha (priority a h s (stage a h s)) (by omega)
    rw [(record_update a h s _).2] at hb
    omega

private theorem protected_bit_step (a : ℕ) (h : Approximation) (q T s x : ℕ)
    (hT : Cutoff a h q T) (hs : T ≤ s)
    (hx : x < restraintAt a h (s + 1) q) :
    stageBit a h (s + 1) (q % 2) x = stageBit a h s (q % 2) x := by
  rw [stage_bit_succ]
  have hn : ¬ (FriedbergSplitting.HasArrival a s ∧
      chosenSide a h s (stage a h s) = (q % 2) % 2 ∧
      x = FriedbergSplitting.arrival a s) := by
    rintro ⟨ha, hc, he⟩
    have hp := threatening_priority a h q T s hT hs ha (he ▸ hx)
    have hqs : q < s + 1 := by have := hT.1; omega
    simp only [chosenSide, hp, ite_eq_left hqs, Nat.mod_mod] at hc
    have hmod : q % 2 < 2 := Nat.mod_lt q (by omega)
    omega
  exact ite_eq_right hn

theorem expanded_data (a : ℕ) (h : Approximation) (q s : ℕ) (he : Expanded a h q s) :
    lengthAt a h (s + 1) q = lengthAt a h s q + 1 ∧
      s + 1 ≤ restraintAt a h (s + 1) q ∧
      ∀ x ≤ lengthAt a h s q,
        finiteValue (stageCode a h s (q % 2)) (s + 1) (q / 2) x = h s x + 1 := by
  have hu := record_update a h s q
  refine ⟨?_, ?_, ?_⟩
  · rw [hu.1]
    simp [nextLength, he.1, he.2, lengthAt]
  · rw [hu.2]
    simp only [nextRestraint, ite_eq_left he.1, ite_eq_left he.2]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · intro x hx
    exact he.2 x (by change x < lengthAt a h s q + 1; omega)

theorem expansion_of_length_increase (a : ℕ) (h : Approximation) (q s : ℕ)
    (hg : lengthAt a h s q < lengthAt a h (s + 1) q) : Expanded a h q s := by
  rw [(record_update a h s q).1] at hg
  change lengthRecord (stage a h s) q < nextLength h s (stage a h s) q at hg
  unfold nextLength at hg
  split_ifs at hg with hq he
  · exact ⟨hq, he⟩
  · omega
  · omega

theorem permanent_protection (a : ℕ) (h : Approximation) (q T s k : ℕ)
    (hT : Cutoff a h q T) (hs : T ≤ s)
    (hk : k ≤ restraintAt a h (s + 1) q) :
    Agreement (stageCode a h s (q % 2)) k (piece a h (q % 2)) := by
  have hb : ∀ v ≥ s, ∀ x < k,
      stageBit a h v (q % 2) x = stageBit a h s (q % 2) x := by
    intro v hv
    induction v, hv using Nat.le_induction with
    | base => exact fun _ _ => rfl
    | succ v hv ih =>
        intro x hx
        have hu := (records_monotone a h q).2 (show s + 1 ≤ v + 1 by omega)
        change restraintAt a h (s + 1) q ≤ restraintAt a h (v + 1) q at hu
        exact (protected_bit_step a h q T v x hT (by omega) (by omega)).trans (ih x hx)
  intro x hx
  have he : x ∈ stageSet a h s (q % 2) ↔ x ∈ piece a h (q % 2) := by
    refine ⟨fun hm => ⟨s, hm⟩, ?_⟩
    rintro ⟨v, hv⟩
    by_cases hvs : v ≤ s
    · exact stage_monotone a h (q % 2) hvs hv
    · have hvbit := hb v (by omega) x hx
      change stageBit a h v (q % 2) x = 1 at hv
      change stageBit a h s (q % 2) x = 1
      omega
  rw [← finiteOracle_indicator]
  change (if x ∈ stageSet a h s (q % 2) then 1 else 0) =
    if x ∈ piece a h (q % 2) then 1 else 0
  simp only [he]

theorem decoder_recursive (a : ℕ) (h : Approximation) (hh : Computable₂ h) (q T : ℕ) :
    Nat.Partrec (expansionDecoder a h q T) := by
  have hc := stage_computable a h hh
  have he : Computable (fun p : ℕ × ℕ => decide (Expanded a h q (T + p.2))) :=
    hc.2.2.2.2.decide.comp
      ((Computable.const q).pair (Primrec.nat_add.to_comp.comp (Computable.const T) Computable.snd))
  have hl : Computable (fun p : ℕ × ℕ => lengthAt a h (T + p.2) q) :=
    hc.2.2.1.comp (Primrec.nat_add.to_comp.comp (Computable.const T) Computable.snd)
      (Computable.const q)
  have hb : Computable₂ (fun x n => decide
      (Expanded a h q (T + n) ∧ x ≤ lengthAt a h (T + n) q)) := by
    simpa only [Bool.decide_and] using
      (Primrec.and.to_comp.comp he
        (Primrec.nat_le.decide.to_comp.comp Computable.fst hl)).to₂
  have hr : Computable₂ (fun x n => h (T + n) x) :=
    hh.comp (Primrec.nat_add.to_comp.comp (Computable.const T) Computable.snd) Computable.fst
  exact Partrec.nat_iff.mp (((Partrec.rfind hb.partrec₂).map hr).of_eq (fun _ => rfl))

private theorem finite_value_mono (u k j e x y : ℕ) (hkj : k ≤ j)
    (hv : finiteValue u k e x = y + 1) : finiteValue u j e x = y + 1 := by
  have hb : bounded (finiteOracle u) k (decodeCode e) x = some y :=
    (boundedValue_output _ _ _ _ _).mp ((finiteValue_identity u k e x).symm.trans hv)
  have hj : bounded (finiteOracle u) j (decodeCode e) x = some y := by
    simpa only [bounded, Nat.add_sub_of_le hkj] using
      bounded_monotone (indicator (fun z => z ∈ finiteOracle u)) k (j - k) (decodeCode e) x y hb
  exact (finiteValue_identity u j e x).trans ((boundedValue_output _ _ _ _ _).mpr hj)

private theorem final_value_eventual (a : ℕ) (h : Approximation) (i e x y : ℕ)
    (hy : y ∈ phi (piece a h i) e x) :
    ∃ T, ∀ s ≥ T, finiteValue (stageCode a h s i) (s + 1) e x = y + 1 := by
  obtain ⟨k, hk⟩ := (phi_output_certificate (piece a h i) e x y).mp hy
  obtain ⟨t, ht⟩ := prefix_settles a h i k
  refine ⟨max t k, fun s hs => ?_⟩
  have hv : finiteValue (stageCode a h s i) k e x = y + 1 :=
    (finiteValue_agreement (piece a h i) _ k e x (ht s (by omega))).trans hk
  exact finite_value_mono _ k (s + 1) e x y (by omega) hv

private theorem agreement_eventual (a : ℕ) (h : Approximation) (C : Set ℕ) (q n : ℕ)
    (hconv : Converges h C) (heq : Computes a h C q) :
    ∃ T, ∀ s ≥ T, ∀ x < n,
      finiteValue (stageCode a h s (q % 2)) (s + 1) (q / 2) x = h s x + 1 := by
  induction n with
  | zero => exact ⟨q, fun _ _ _ hx => by omega⟩
  | succ n ih =>
      obtain ⟨T, hT⟩ := ih
      obtain ⟨v, hv⟩ := hconv n
      obtain ⟨w, hw⟩ := final_value_eventual a h (q % 2) (q / 2) n (indicator C n)
        (Part.eq_some_iff.mp (heq n))
      refine ⟨max T (max v w), fun s hs x hx => ?_⟩
      by_cases hxn : x < n
      · exact hT s (by omega) x hxn
      · have he : x = n := by omega
        subst x
        rw [hw s (by omega), hv s (by omega)]

private theorem length_succ_le (a : ℕ) (h : Approximation) (q s : ℕ) :
    lengthAt a h (s + 1) q ≤ lengthAt a h s q + 1 := by
  rw [(record_update a h s q).1]
  change nextLength h s (stage a h s) q ≤ lengthRecord (stage a h s) q + 1
  unfold nextLength
  split_ifs <;> omega

private theorem expansion_above (a : ℕ) (h : Approximation) (q : ℕ)
    (hunbounded : ∀ n, ∃ s, n < lengthAt a h s q) (T x : ℕ) :
    ∃ s ≥ T, Expanded a h q s ∧ x ≤ lengthAt a h s q := by
  let b := max x (lengthAt a h T q)
  obtain ⟨v, hv⟩ := hunbounded b
  have hgrow : ∃ s ≥ T, b ≤ lengthAt a h s q ∧
      lengthAt a h s q < lengthAt a h (s + 1) q := by
    by_contra hn
    push Not at hn
    have hbound : ∀ v ≥ T, lengthAt a h v q ≤ b := by
      intro v hvT
      induction v, hvT using Nat.le_induction with
      | base => exact le_max_right _ _
      | succ v hvT ih =>
          by_cases he : lengthAt a h v q < lengthAt a h (v + 1) q
          · have hnot : ¬ b ≤ lengthAt a h v q := fun hb => not_le_of_gt he (hn v hvT hb)
            have hstep := length_succ_le a h q v
            omega
          · omega
    by_cases hvT : T ≤ v
    · have := hbound v hvT
      omega
    · have hm := (records_monotone a h q).1 (show v ≤ T by omega)
      change lengthAt a h v q ≤ lengthAt a h T q at hm
      dsimp [b] at hv
      omega
  obtain ⟨s, hs, hb, hg⟩ := hgrow
  exact ⟨s, hs, expansion_of_length_increase a h q s hg, le_trans (le_max_left _ _) hb⟩

theorem unbounded_agreement (a : ℕ) (h : Approximation) (C : Set ℕ) (q : ℕ)
    (hconv : Converges h C) (heq : Computes a h C q) :
    (∀ n, ∃ s, n < lengthAt a h s q) ∧
      ∀ T x, (expansionDecoder a h q T x).Dom := by
  have hu : ∀ n, ∃ s, n < lengthAt a h s q := by
    intro n
    by_contra hn
    push Not at hn
    obtain ⟨l, T, hT⟩ := converges_of_monotone_of_bounded (records_monotone a h q).1 hn
    obtain ⟨v, hv⟩ := agreement_eventual a h C q (l + 1) hconv heq
    let s := max q (max T v)
    have hTs : T ≤ s := by dsimp [s]; omega
    have hvs : v ≤ s := by dsimp [s]; omega
    have hq : q ≤ s := by dsimp [s]; omega
    have hE : Expanded a h q s := by
      refine ⟨hq, ?_⟩
      intro x hx
      have hlen : lengthRecord (stage a h s) q = l := hT s hTs
      exact hv s hvs x (by omega)
    have hg := (expanded_data a h q s hE).1
    rw [hT s hTs, hT (s + 1) (by omega)] at hg
    omega
  refine ⟨hu, ?_⟩
  intro T x
  obtain ⟨s, hs, he, hx⟩ := expansion_above a h q hu T x
  have hn : T + (s - T) = s := by omega
  have hw : ∃ n, Expanded a h q (T + n) ∧ x ≤ lengthAt a h (T + n) q :=
    ⟨s - T, by simpa only [hn] using And.intro he hx⟩
  obtain ⟨n, hn⟩ := hw
  have hsearch : (expansionSearch a h q T x).Dom :=
    Nat.rfind_dom.mpr ⟨n, by simpa using hn, fun {_} _ => trivial⟩
  exact hsearch

theorem decoder_correct (a : ℕ) (h : Approximation) (C : Set ℕ) (q T : ℕ)
    (hconv : Converges h C) (heq : Computes a h C q) (hT : Cutoff a h q T) :
    ∀ x, expansionDecoder a h q T x = Part.some (indicator C x) := by
  intro x
  have hdom : (expansionSearch a h q T x).Dom := (unbounded_agreement a h C q hconv heq).2 T x
  obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hdom
  have hfound : Expanded a h q (T + n) ∧ x ≤ lengthAt a h (T + n) q := by
    have hspec := Nat.rfind_spec hn
    simpa using hspec
  have hd := expanded_data a h q (T + n) hfound.1
  have ha := permanent_protection a h q T (T + n) (T + n + 1) hT (by omega) hd.2.1
  have hv : boundedValue (piece a h (q % 2)) (T + n + 1) (q / 2) x = h (T + n) x + 1 := by
    rw [← finiteValue_agreement _ _ _ _ _ ha]
    exact hd.2.2 x hfound.2
  have hout : h (T + n) x ∈ phi (piece a h (q % 2)) (q / 2) x :=
    (phi_output_certificate _ _ _ _).mpr ⟨T + n + 1, hv⟩
  have hcorrect : h (T + n) x = indicator C x :=
    Part.mem_unique hout (Part.eq_some_iff.mp (heq x))
  apply Part.eq_some_iff.mpr
  exact (Part.mem_map_iff _).mpr ⟨n, hn, hcorrect⟩

theorem avoidance (a : ℕ) (h : Approximation) (C : Set ℕ) (q : ℕ)
    (hh : Computable₂ h) (hconv : Converges h C) (hC : ¬ ComputablePred C)
    (hhigher : HigherStable a h q) : Avoids a h C q := by
  intro heq
  obtain ⟨T, hT⟩ := higher_cutoff a h q hhigher
  have hd := decoder_correct a h C q T hconv heq hT
  have hc : Computable (indicator C) :=
    (Partrec.nat_iff.mpr (decoder_recursive a h hh q T)).of_eq_tot
      (fun x => by rw [hd x]; exact Part.mem_some _)
  exact hC ((decidable_iff_characteristic C).mpr ⟨indicator C, hc, fun _ => rfl⟩)

theorem length_settles (a : ℕ) (h : Approximation) (C : Set ℕ) (q : ℕ)
    (hconv : Converges h C) (havoid : Avoids a h C q) (hhigher : HigherStable a h q) :
    ∃ T l, ∀ s ≥ T, lengthAt a h s q = l := by
  obtain ⟨T, hT⟩ := higher_cutoff a h q hhigher
  have hnot : ¬ ∀ x, phi (piece a h (q % 2)) (q / 2) x = Part.some (indicator C x) := havoid
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  obtain ⟨v, hv⟩ := hconv x
  let t := max T v
  have hno : ∀ s ≥ t, x ≤ lengthAt a h s q → ¬ Expanded a h q s := by
    intro s hs hlen he
    have hd := expanded_data a h q s he
    have ha := permanent_protection a h q T s (s + 1) hT (by dsimp [t] at hs; omega) hd.2.1
    have hout : indicator C x ∈ phi (piece a h (q % 2)) (q / 2) x := by
      apply (phi_output_certificate _ _ _ _).mpr
      refine ⟨s + 1, ?_⟩
      rw [← finiteValue_agreement _ _ _ _ _ ha, hd.2.2 x hlen, hv s (by dsimp [t] at hs; omega)]
    exact hx (Part.eq_some_iff.mpr hout)
  let b := max (lengthAt a h t q) x
  have hlate : ∀ s ≥ t, lengthAt a h s q ≤ b := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact le_max_left _ _
    | succ s hs ih =>
        by_cases hg : lengthAt a h s q < lengthAt a h (s + 1) q
        · have he := expansion_of_length_increase a h q s hg
          have hxlt : lengthAt a h s q < x := by
            by_contra hn
            exact hno s hs (by omega) he
          have hb := length_succ_le a h q s
          have hxb : x ≤ b := le_max_right _ _
          omega
        · omega
  have hbound : ∀ s, lengthAt a h s q ≤ b := by
    intro s
    by_cases hs : t ≤ s
    · exact hlate s hs
    · have hm := (records_monotone a h q).1 (show s ≤ t by omega)
      exact le_trans hm (le_max_left _ _)
  obtain ⟨l, u, hu⟩ := converges_of_monotone_of_bounded (records_monotone a h q).1 hbound
  exact ⟨u, l, hu⟩

private theorem observation_below_restraint (a : ℕ) (h : Approximation) (q s : ℕ)
    (hq : q ≤ s) : leastObservation s (stage a h s) q ≤ restraintAt a h (s + 1) q := by
  rw [(record_update a h s q).2]
  simp only [nextRestraint, ite_eq_left hq]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

private theorem observation_constant (a : ℕ) (h : Approximation) (q T v : ℕ)
    (hT : Cutoff a h q T) (hv : T ≤ v)
    (hd : 0 < leastObservation v (stage a h v) q) :
    ∀ w ≥ v, leastObservation w (stage a h w) q = leastObservation v (stage a h v) q := by
  let k := leastObservation v (stage a h v) q
  have hdata := observation_data v (stage a h v) q
  have hk : k ≤ restraintAt a h (v + 1) q :=
    observation_below_restraint a h q v (le_trans hT.1 hv)
  have ha := permanent_protection a h q T v k hT hv hk
  intro w hw
  have hu := (records_monotone a h q).2 (show v + 1 ≤ w + 1 by omega)
  have hkw : k ≤ restraintAt a h (w + 1) q := le_trans hk hu
  have hb := permanent_protection a h q T w k hT (by omega) hkw
  have hvalues (j : ℕ) (hj : j ≤ k) :
      finiteValue (stageCode a h v (q % 2)) j (q / 2) (q / 2) =
      finiteValue (stageCode a h w (q % 2)) j (q / 2) (q / 2) := by
    have haj : Agreement (stageCode a h v (q % 2)) j (piece a h (q % 2)) :=
      fun x hx => ha x (lt_of_lt_of_le hx hj)
    have hbj : Agreement (stageCode a h w (q % 2)) j (piece a h (q % 2)) :=
      fun x hx => hb x (lt_of_lt_of_le hx hj)
    rw [finiteValue_agreement _ _ _ _ _ haj, finiteValue_agreement _ _ _ _ _ hbj]
  have hpositive : 0 < finiteValue (stageCode a h w (q % 2)) k (q / 2) (q / 2) := by
    rw [← hvalues k le_rfl]
    exact (hdata.2.2 hd).1
  have hwdata := observation_data w (stage a h w) q
  have hwpositive : 0 < leastObservation w (stage a h w) q :=
    hwdata.2.1.mpr ⟨k, le_trans hdata.1 (by omega), hpositive⟩
  apply le_antisymm
  · by_contra hn
    have hz := (hwdata.2.2 hwpositive).2 k (by omega)
    change finiteValue (stageCode a h w (q % 2)) k (q / 2) (q / 2) = 0 at hz
    omega
  · by_contra hn
    have hj : leastObservation w (stage a h w) q < k := by omega
    have hz := (hdata.2.2 hd).2 _ hj
    change finiteValue (stageCode a h v (q % 2)) _ (q / 2) (q / 2) = 0 at hz
    rw [hvalues _ (by omega)] at hz
    have hp := (hwdata.2.2 hwpositive).1
    change 0 < finiteValue (stageCode a h w (q % 2)) _ (q / 2) (q / 2) at hp
    omega

private theorem restraint_step_no_expansion (a : ℕ) (h : Approximation) (q s : ℕ)
    (hq : q ≤ s) (hn : ¬ Expanded a h q s) :
    restraintAt a h (s + 1) q = max (restraintAt a h s q) (leastObservation s (stage a h s) q) := by
  rw [(record_update a h s q).2]
  have he : ¬ Expands h s (stage a h s) q := fun he => hn ⟨hq, he⟩
  simp [nextRestraint, hq, he, restraintAt]

theorem restraint_settles (a : ℕ) (h : Approximation) (q : ℕ)
    (hlength : ∃ T l, ∀ s ≥ T, lengthAt a h s q = l)
    (hhigher : HigherStable a h q) :
    ∃ T u, ∀ s ≥ T, restraintAt a h s q = u := by
  obtain ⟨T, hT⟩ := higher_cutoff a h q hhigher
  obtain ⟨v, l, hl⟩ := hlength
  let t := max T v
  have hqt : q ≤ t := le_trans hT.1 (le_max_left _ _)
  have hno : ∀ s ≥ t, ¬ Expanded a h q s := by
    intro s hs he
    have hg := (expanded_data a h q s he).1
    rw [hl s (by dsimp [t] at hs; omega), hl (s + 1) (by dsimp [t] at hs; omega)] at hg
    omega
  by_cases hex : ∃ w ≥ t, 0 < leastObservation w (stage a h w) q
  · obtain ⟨w, hw, hd⟩ := hex
    have hobs := observation_constant a h q T w hT (by dsimp [t] at hw; omega) hd
    have hkw := observation_below_restraint a h q w (by omega)
    refine ⟨w + 1, restraintAt a h (w + 1) q, ?_⟩
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => rfl
    | succ s hs ih =>
        rw [restraint_step_no_expansion a h q s (by omega) (hno s (by omega)), hobs s (by omega)]
        have hu := (records_monotone a h q).2 hs
        rw [max_eq_left (le_trans hkw hu)]
        exact ih
  · refine ⟨t, restraintAt a h t q, ?_⟩
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => rfl
    | succ s hs ih =>
        have hz : leastObservation s (stage a h s) q = 0 := by
          by_contra hn
          exact hex ⟨s, hs, by omega⟩
        rw [restraint_step_no_expansion a h q s (by omega) (hno s hs), hz, max_eq_left (Nat.zero_le _)]
        exact ih

theorem priority_induction (a : ℕ) (h : Approximation) (C : Set ℕ)
    (hh : Computable₂ h) (hconv : Converges h C) (hC : ¬ ComputablePred C) (q : ℕ) :
    Avoids a h C q ∧ (∃ T l, ∀ s ≥ T, lengthAt a h s q = l) ∧
      (∃ T u, ∀ s ≥ T, restraintAt a h s q = u) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      have hhigher : HigherStable a h q := fun p hp => (ih p hp).2.2
      have ha := avoidance a h C q hh hconv hC hhigher
      have hl := length_settles a h C q hconv ha hhigher
      exact ⟨ha, hl, restraint_settles a h q hl hhigher⟩

theorem pieces_avoid (a : ℕ) (h : Approximation) (C : Set ℕ)
    (hh : Computable₂ h) (hconv : Converges h C) (hC : ¬ ComputablePred C) :
    ¬ TuringDegrees.Reducible C (piece a h 0) ∧
      ¬ TuringDegrees.Reducible C (piece a h 1) := by
  have hn (i : ℕ) (hi : i < 2) : ¬ TuringDegrees.Reducible C (piece a h i) := by
    rintro ⟨c, hc⟩
    let e := encodeCode c
    have heq : (2 * e + i) / 2 = e ∧ (2 * e + i) % 2 = i := by omega
    apply (priority_induction a h C hh hconv hC (2 * e + i)).1
    intro x
    have hcx := hc x
    change OracleComputation.eval (piece a h i) c x = Part.some (indicator C x) at hcx
    simpa only [heq.1, heq.2, e, OracleProgramNumberings.phi, decode_encode] using hcx
  exact ⟨hn 0 (by omega), hn 1 (by omega)⟩

end
end Lemmatheca.ComputabilityTheory.SacksSplitting
