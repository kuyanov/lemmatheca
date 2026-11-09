import Lemmatheca.FriedbergSplitting.Routing

/-! Finite action and the exact ordinary decoder supplied by an alleged complement. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergSplitting

open EffectiveEnumerations UniversalComputation

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def Requirement (a q : ℕ) : Prop := indexSet (q / 2) ≠ (piece a (q % 2))ᶜ

theorem single_action (a q s t : ℕ) (hs : Acts a q s) (ht : Acts a q t) : s = t := by
  have hn (u v : ℕ) (hu : Acts a q u) (hv : Acts a q v) (huv : u < v) : False := by
    have heu := (priority_data a u (routeStage a u)).1 hu.1
    have hev := (priority_data a v (routeStage a v)).1 hv.1
    rw [hu.2] at heu
    rw [hv.2] at hev
    have hc : chosenSide a u (routeStage a u) = q % 2 := by
      simp [chosenSide, hu.1, hu.2]
    have hm : arrival a u ∈ pieceStage a (q % 2) (u + 1) :=
      (routing_transition a (q % 2) u _ (Nat.mod_lt _ (by omega))).mpr
        (Or.inr ⟨heu.2.1, hc, rfl⟩)
    have hl : arrival a u ∈ sideList (routeStage a v) q := by
      simpa [pieceStage, pieceList, sideList] using
        piece_stage_monotone a (q % 2) (by omega : u + 1 ≤ v) hm
    have hzero := hev.2.2.2 _ hl
    have hone := (stage_test_spec (q / 2) (v + 1) (arrival a u)).2.mpr
      (stage_monotone (q / 2) (by omega : u + 1 ≤ v + 1)
        ((stage_test_spec _ _ _).2.mp heu.2.2.1))
    omega
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (hn s t hs ht h)
  · exact h
  · exact False.elim (hn t s ht hs h)

theorem higher_actions_stop (a q : ℕ) :
    ∃ t, q ≤ t ∧ ∀ s ≥ t, ∀ p < q, ¬ Acts a p s := by
  induction q with
  | zero => exact ⟨0, le_rfl, by intro s hs p hp; omega⟩
  | succ q ih =>
    obtain ⟨t, hqt, ht⟩ := ih
    by_cases hex : ∃ u, Acts a q u
    · obtain ⟨u, hu⟩ := hex
      refine ⟨max t (u + 1) + 1, by omega, ?_⟩
      intro s hs p hp hact
      by_cases hpq : p < q
      · exact ht s (by omega) p hpq hact
      · have he : p = q := by omega
        subst p
        have := single_action a q u s hu hact
        omega
    · refine ⟨t + 1, by omega, ?_⟩
      intro s hs p hp hact
      by_cases hpq : p < q
      · exact ht s (by omega) p hpq hact
      · have he : p = q := by omega
        subst p
        exact hex ⟨s, hact⟩

def complementSearch (a e t x : ℕ) : Part ℕ :=
  (Nat.rfind fun j => Part.some (decide
    (processedTest a (t + j) x = 1 ∨ stageTest e (t + j) x = 1))).map (fun j => t + j)

def complementDecoder (a e t x : ℕ) : Part ℕ :=
  (complementSearch a e t x).map (fun s => processedTest a s x)

theorem complement_decoder_recursive (a e t : ℕ) :
    Nat.Partrec (complementDecoder a e t) := by
  have hp : Computable (fun p : ℕ × ℕ => processedTest a (t + p.2) p.1) :=
    scheduler_primitive.2.2.to_comp.comp (show Primrec (fun p : ℕ × ℕ => ((a, t + p.2), p.1)) by fun_prop).to_comp
  have hw : Computable (fun p : ℕ × ℕ => stageTest e (t + p.2) p.1) :=
    stage_test_primitive.to_comp.comp (show Primrec (fun p : ℕ × ℕ => ((e, t + p.2), p.1)) by fun_prop).to_comp
  have hb : Computable₂ (fun x j => decide
      (processedTest a (t + j) x = 1 ∨ stageTest e (t + j) x = 1)) :=
    (by
      simpa only [Bool.decide_or] using
        Primrec.or.to_comp.comp
          (Primrec.eq.decide.to_comp.comp hp (Computable.const 1))
          (Primrec.eq.decide.to_comp.comp hw (Computable.const 1)) |>.to₂)
  have hs := (Partrec.rfind hb.partrec₂).map
    (show Primrec (fun p : ℕ × ℕ => t + p.2) by fun_prop).to₂.to_comp
  have hd := hs.map (show Computable₂ (fun x s => processedTest a s x) from
    scheduler_primitive.2.2.to_comp.comp
      (show Primrec (fun p : ℕ × ℕ => ((a, p.2), p.1)) by fun_prop).to_comp)
  exact Partrec.nat_iff.mp (hd.of_eq (fun _ => rfl))

private theorem processing_event (a x s : ℕ) (hx : x ∈ indexSet a)
    (hn : x ∉ processedSet a s) :
    ∃ v ≥ s, HasArrival a v ∧ x = arrival a v := by
  obtain ⟨u, hu⟩ := (scheduler_exhaustive a x).mp hx
  have hm : ∀ u, x ∈ processedSet a u → ∃ v < u, HasArrival a v ∧ x = arrival a v := by
    intro u
    induction u with
    | zero => simp [processedSet, processedList]
    | succ u ih =>
      intro hu
      rcases (scheduler_transition a u x).mp hu with hp | hp
      · obtain ⟨v, hv, hh⟩ := ih hp
        exact ⟨v, by omega, hh⟩
      · exact ⟨u, by omega, hp⟩
  obtain ⟨v, hv, ha, he⟩ := hm u hu
  refine ⟨v, ?_, ha, he⟩
  by_contra h
  exact hn (scheduler_monotone a (by omega : v + 1 ≤ s)
    ((scheduler_transition a v x).mpr (Or.inr ⟨ha, he⟩)))

theorem complement_decoder_correct (a e i t : ℕ) (hi : i < 2)
    (hq : 2 * e + i ≤ t)
    (hstop : ∀ s ≥ t, ∀ p < 2 * e + i, ¬ Acts a p s)
    (he : indexSet e = (piece a i)ᶜ) :
    ∀ x, complementDecoder a e t x = Part.some (indicator (indexSet a) x) := by
  intro x
  have hpart := routed_partition a
  have hsub : piece a i ⊆ indexSet a := by
    intro y hy
    rw [← hpart.2.2.2]
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact Or.inl hy
    · exact Or.inr hy
  have heq : (2 * e + i) / 2 = e ∧ (2 * e + i) % 2 = i := by omega
  have hdis (y : ℕ) : y ∈ indexSet e → y ∉ piece a i := by
    rw [he]
    exact id
  have correct (s : ℕ) (hs : t ≤ s)
      (hfound : processedTest a s x = 1 ∨ stageTest e s x = 1) :
      processedTest a s x = indicator (indexSet a) x := by
    by_cases hp : x ∈ processedSet a s
    · have hA := (scheduler_invariants a s).2.2 hp
      have hAx : indexSet a x := hA
      change x ∈ processedList a s at hp
      simp [processedTest, hp, indicator, hAx]
    · have hz : processedTest a s x = 0 := by simpa [processedTest, processedSet] using hp
      have hw : stageTest e s x = 1 := hfound.resolve_left (by omega)
      have hwe : x ∈ indexSet e := (stage_union e x).mpr
        ⟨s, (stage_test_spec _ _ _).2.mp hw⟩
      have hnA : x ∉ indexSet a := by
        intro hA
        obtain ⟨v, hsv, hv, hxv⟩ := processing_event a x s hA hp
        have hwv : stageTest e (v + 1) (arrival a v) = 1 := by
          apply (stage_test_spec _ _ _).2.mpr
          rw [← hxv]
          exact stage_monotone e (by omega) ((stage_test_spec _ _ _).2.mp hw)
        have hel : Eligible a v (routeStage a v) (2 * e + i) := by
          refine ⟨by omega, hv, ?_, ?_⟩
          · simpa [heq.1] using hwv
          · intro y hy
            have hyi : y ∈ piece a i := by
              refine ⟨v, ?_⟩
              simpa [pieceStage, pieceList, sideList, heq.2, Nat.mod_eq_of_lt hi] using hy
            have hny : y ∉ stage e (v + 1) := fun h =>
              hdis y ((stage_union e y).mpr ⟨v + 1, h⟩) hyi
            have hb := (stage_test_spec e (v + 1) y).1
            have hone : stageTest e (v + 1) y ≠ 1 := fun h => hny ((stage_test_spec _ _ _).2.mp h)
            simpa [heq.1] using hb.resolve_right hone
        obtain ⟨hact, hpri⟩ := (priority_data a v (routeStage a v)).2 _ hel
        have hprieq : priority a v (routeStage a v) = 2 * e + i := by
          by_contra hne
          exact hstop v (by omega) _ (by omega) ⟨hact, rfl⟩
        have hside : chosenSide a v (routeStage a v) = i := by
          simp [chosenSide, hact, hprieq, heq.2]
        have hmem : x ∈ piece a i := ⟨v + 1,
          (routing_transition a i v x hi).mpr (Or.inr ⟨hv, hside, hxv⟩)⟩
        exact hdis x hwe hmem
      have hnAx : ¬ indexSet a x := hnA
      simp [hz, indicator, hnAx]
  let Q (j : ℕ) := processedTest a (t + j) x = 1 ∨ stageTest e (t + j) x = 1
  have hex : ∃ j, Q j := by
    by_cases hx : x ∈ indexSet a
    · obtain ⟨u, hu⟩ := (scheduler_exhaustive a x).mp hx
      refine ⟨max t u - t, Or.inl ?_⟩
      have hm := scheduler_monotone a (Nat.le_max_right t u) hu
      have ht : t + (max t u - t) = max t u := Nat.add_sub_of_le (Nat.le_max_left _ _)
      simpa [processedSet, processedTest, ht] using hm
    · have hwe : x ∈ indexSet e := by
        rw [he]
        exact fun h => hx (hsub h)
      obtain ⟨u, hu⟩ := (stage_union e x).mp hwe
      refine ⟨max t u - t, Or.inr ?_⟩
      have ht : t + (max t u - t) = max t u := Nat.add_sub_of_le (Nat.le_max_left _ _)
      rw [ht]
      exact (stage_test_spec _ _ _).2.mpr (stage_monotone e (Nat.le_max_right _ _) hu)
  let j := Nat.find hex
  have hj : j ∈ Nat.rfind (fun k => Part.some (decide (Q k))) := by
    apply Nat.mem_rfind.mpr
    exact ⟨by simpa using Nat.find_spec hex,
      fun {k} hk => by simpa using Nat.find_min hex hk⟩
  apply Part.eq_some_iff.mpr
  apply (Part.mem_map_iff _).mpr
  refine ⟨t + j, ?_, correct (t + j) (by omega) (Nat.find_spec hex)⟩
  exact (Part.mem_map_iff _).mpr ⟨j, hj, rfl⟩

theorem all_requirements (a : ℕ)
    (ha : ¬ ComputablePred (indexSet a)) : ∀ q, Requirement a q := by
  intro q he
  obtain ⟨t, hqt, ht⟩ := higher_actions_stop a q
  let e := q / 2
  let i := q % 2
  have heq : 2 * e + i = q := by dsimp [e, i]; omega
  have hc := complement_decoder_correct a e i t (Nat.mod_lt _ (by omega))
    (by omega) (by simpa [heq] using ht) he
  have hcomp : Computable (indicator (indexSet a)) :=
    (Partrec.nat_iff.mpr (complement_decoder_recursive a e t)).of_eq_tot
      (fun x => by rw [hc x]; exact Part.mem_some _)
  exact ha ((decidable_iff_characteristic _).mpr ⟨_, hcomp, fun _ => rfl⟩)

theorem friedberg_index (a : ℕ) (ha : ¬ ComputablePred (indexSet a)) :
    ¬ ComputablePred (piece a 0) ∧ ¬ ComputablePred (piece a 1) := by
  have hn (i : ℕ) (hi : i < 2) : ¬ ComputablePred (piece a i) := by
    intro hc
    have hce : REPred (piece a i)ᶜ := hc.not.to_re
    obtain ⟨e, he⟩ := (enumerable_iff_index _).mp hce
    have hq := all_requirements a ha (2 * e + i)
    apply hq
    have heq : (2 * e + i) / 2 = e ∧ (2 * e + i) % 2 = i := by omega
    simp only [heq.1, heq.2]
    exact Set.ext (fun x => (he x).symm)
  exact ⟨hn 0 (by omega), hn 1 (by omega)⟩

theorem friedberg_splitting (A : Set ℕ) (hA : REPred A)
    (ha : ¬ ComputablePred A) :
    ∃ a, indexSet a = A ∧ REPred (piece a 0) ∧ REPred (piece a 1) ∧
      Disjoint (piece a 0) (piece a 1) ∧ piece a 0 ∪ piece a 1 = A ∧
      ¬ ComputablePred (piece a 0) ∧ ¬ ComputablePred (piece a 1) := by
  obtain ⟨a, hindex⟩ := (enumerable_iff_index A).mp hA
  have he : indexSet a = A := Set.ext (fun x => (hindex x).symm)
  have hna : ¬ ComputablePred (indexSet a) := by simpa [he] using ha
  obtain ⟨h0, h1, hd, hu⟩ := routed_partition a
  obtain ⟨hn0, hn1⟩ := friedberg_index a hna
  exact ⟨a, he, h0, h1, hd, hu.trans he, hn0, hn1⟩

end
end Lemmatheca.ComputabilityTheory.FriedbergSplitting
