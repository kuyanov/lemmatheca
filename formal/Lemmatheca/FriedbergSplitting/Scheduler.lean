import Lemmatheca.EffectiveEnumerations.Settling
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursiveAutomation

/-! One fresh member per stage, with an explicit idle sentinel. -/
namespace Lemmatheca.ComputabilityTheory.FriedbergSplitting

open EffectiveEnumerations PrimitiveRecursion PrimitiveRecursiveAutomation UniversalComputation

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def chooseArrival (a s : ℕ) (l : List ℕ) : ℕ :=
  boundedSearch (fun p : (ℕ × ℕ) × List ℕ => fun x =>
    stageTest p.1.1 (p.1.2 + 1) x = 1 ∧ x ∉ p.2) ((a, s), l) (s + 1)

def schedulerNext (a s : ℕ) (l : List ℕ) : List ℕ :=
  if chooseArrival a s l < s + 1 then chooseArrival a s l :: l else l

def processedList (a : ℕ) : ℕ → List ℕ
  | 0 => []
  | s + 1 => schedulerNext a s (processedList a s)

def processedSet (a s : ℕ) : Set ℕ := {x | x ∈ processedList a s}

def processedTest (a s x : ℕ) : ℕ := if x ∈ processedList a s then 1 else 0

def arrival (a s : ℕ) : ℕ := chooseArrival a s (processedList a s)

def HasArrival (a s : ℕ) : Prop := arrival a s < s + 1

private theorem choose_spec (a s : ℕ) (l : List ℕ) :
    chooseArrival a s l ≤ s + 1 ∧
    (chooseArrival a s l < s + 1 →
      chooseArrival a s l ∈ stage a (s + 1) ∧ chooseArrival a s l ∉ l ∧
      ∀ x < s + 1, x ∈ stage a (s + 1) → x ∉ l → chooseArrival a s l ≤ x) ∧
    (chooseArrival a s l = s + 1 ↔ ∀ x < s + 1, ¬ (x ∈ stage a (s + 1) ∧ x ∉ l)) := by
  unfold chooseArrival
  have h := boundedSearch_spec (fun p : (ℕ × ℕ) × List ℕ => fun x =>
    stageTest p.1.1 (p.1.2 + 1) x = 1 ∧ x ∉ p.2) ((a, s), l) (s + 1)
  refine ⟨h.1, ?_, ?_⟩
  · intro hs
    have hm := h.2.1 hs
    refine ⟨(stage_test_spec _ _ _).2.mp hm.1.1, hm.1.2, ?_⟩
    intro x hx hxs hxl
    by_contra hn
    exact hm.2 x (by omega) ⟨(stage_test_spec _ _ _).2.mpr hxs, hxl⟩
  · simpa only [(stage_test_spec a (s + 1) _).2] using h.2.2

private theorem choose_primitive :
    Primrec (fun p : (ℕ × ℕ) × List ℕ => chooseArrival p.1.1 p.1.2 p.2) := by
  have hs : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ℕ =>
      stageTest p.1.1.1 (p.1.1.2 + 1) p.2) :=
    stage_test_primitive.comp (show Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ℕ =>
      ((p.1.1.1, p.1.1.2 + 1), p.2)) by fun_prop)
  have hm : Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => decide (p.2 ∉ p.1.2)) := by
    simpa only [decide_not] using PrimitiveRecursiveAutomation.not
      (show Primrec (fun p : ((ℕ × ℕ) × List ℕ) × ℕ => decide (p.2 ∈ p.1.2)) by fun_prop)
  have hp := andPred (PrimitiveRecursiveAutomation.eq hs (Primrec.const 1)) hm
  exact (boundedSearch_primrec (R := fun p : (ℕ × ℕ) × List ℕ => fun x =>
    stageTest p.1.1 (p.1.2 + 1) x = 1 ∧ x ∉ p.2) hp.primrecPred).comp Primrec.id (by fun_prop)

theorem scheduler_primitive :
    Primrec₂ processedList ∧ Primrec₂ arrival ∧
      Primrec (fun p : (ℕ × ℕ) × ℕ => processedTest p.1.1 p.1.2 p.2) := by
  have hn : Primrec (fun p : (ℕ × ℕ) × List ℕ => schedulerNext p.1.1 p.1.2 p.2) := by
    unfold schedulerNext
    exact PrimitiveRecursiveAutomation.ite
      (PrimitiveRecursiveAutomation.lt choose_primitive (by fun_prop))
      (PrimitiveRecursiveAutomation.listCons choose_primitive (by fun_prop)) (by fun_prop)
  have hh : Primrec₂ (fun a (p : ℕ × List ℕ) => schedulerNext a p.1 p.2) :=
    hn.comp (show Primrec (fun p : ℕ × (ℕ × List ℕ) => ((p.1, p.2.1), p.2.2)) by fun_prop)
  have hl : Primrec₂ processedList :=
    (Primrec.nat_rec (Primrec.const []) hh).of_eq (by
      intro a n
      induction n with
      | zero => rfl
      | succ n ih => simp only [processedList, ih])
  have ha : Primrec₂ arrival := by
    unfold arrival
    exact choose_primitive.comp ((Primrec.fst.pair Primrec.snd).pair hl)
  refine ⟨hl, ha, ?_⟩
  unfold processedTest
  exact PrimitiveRecursiveAutomation.ite
    (PrimitiveRecursiveAutomation.listMem Primrec.snd (Primrec.comp hl Primrec.fst))
    (Primrec.const 1) (Primrec.const 0)

theorem scheduler_invariants (a s : ℕ) :
    (processedList a s).Nodup ∧ processedSet a s ⊆ Set.Iio s ∧
      processedSet a s ⊆ indexSet a := by
  induction s with
  | zero => simp [processedList, processedSet]
  | succ s ih =>
    have hc := choose_spec a s (processedList a s)
    by_cases h : chooseArrival a s (processedList a s) < s + 1
    · obtain ⟨hm, hf, _⟩ := hc.2.1 h
      refine ⟨?_, ?_, ?_⟩
      · simpa [processedList, schedulerNext, h] using List.nodup_cons.mpr ⟨hf, ih.1⟩
      · intro x hx
        simp only [processedSet, processedList, schedulerNext, h, ↓reduceIte,
          Set.mem_ofPred, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (stage_bounds a (s + 1)).1 hm
        · exact lt_trans (ih.2.1 hx) (Nat.lt_succ_self s)
      · intro x hx
        simp only [processedSet, processedList, schedulerNext, h, ↓reduceIte,
          Set.mem_ofPred, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (stage_union a _).mpr ⟨s + 1, hm⟩
        · exact ih.2.2 hx
    · simpa [processedList, schedulerNext, h, processedSet] using
        (show (processedList a s).Nodup ∧
          processedSet a s ⊆ Set.Iio (s + 1) ∧ processedSet a s ⊆ indexSet a from
          ⟨ih.1, fun x hx => lt_trans (ih.2.1 hx) (Nat.lt_succ_self s), ih.2.2⟩)

theorem scheduler_transition (a s x : ℕ) :
    x ∈ processedSet a (s + 1) ↔
      x ∈ processedSet a s ∨ HasArrival a s ∧ x = arrival a s := by
  by_cases h : HasArrival a s
  · have hc : chooseArrival a s (processedList a s) < s + 1 := h
    simp [processedSet, processedList, schedulerNext, hc, h, arrival, or_comm]
  · have hc : ¬ chooseArrival a s (processedList a s) < s + 1 := h
    simp [processedSet, processedList, schedulerNext, hc, h]

theorem scheduler_monotone (a : ℕ) : Monotone (processedSet a) := by
  apply monotone_nat_of_le_succ
  intro s x hx
  exact (scheduler_transition a s x).mpr (Or.inl hx)

theorem arrival_data (a s : ℕ) :
    arrival a s ≤ s + 1 ∧
      (HasArrival a s ↔ ∃ x < s + 1, x ∈ stage a (s + 1) ∧ x ∉ processedSet a s) ∧
      (HasArrival a s → arrival a s ∈ stage a (s + 1) ∧
        arrival a s ∉ processedSet a s ∧
        ∀ x < s + 1, x ∈ stage a (s + 1) → x ∉ processedSet a s → arrival a s ≤ x) ∧
      (¬ HasArrival a s ↔ arrival a s = s + 1) := by
  have hc := choose_spec a s (processedList a s)
  change arrival a s ≤ s + 1 ∧ _ at hc
  refine ⟨hc.1, ?_, hc.2.1, ?_⟩
  · constructor
    · intro h
      exact ⟨arrival a s, h, (hc.2.1 h).1, (hc.2.1 h).2.1⟩
    · rintro ⟨x, hx, hm, hf⟩
      by_contra hn
      have he : arrival a s = s + 1 := by unfold HasArrival at hn; omega
      exact hc.2.2.mp he x hx ⟨hm, hf⟩
  · unfold HasArrival
    omega

theorem arrivals_distinct (a s t : ℕ) (hs : HasArrival a s) (ht : HasArrival a t)
    (hst : s < t) : arrival a s ≠ arrival a t := by
  intro he
  have hm : arrival a s ∈ processedSet a (s + 1) :=
    (scheduler_transition a s _).mpr (Or.inr ⟨hs, rfl⟩)
  exact (arrival_data a t).2.2.1 ht |>.2.1
    (he ▸ scheduler_monotone a (by omega : s + 1 ≤ t) hm)

theorem scheduler_exhaustive (a x : ℕ) :
    x ∈ indexSet a ↔ ∃ s, x ∈ processedSet a s := by
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    obtain ⟨v, hv⟩ := (stage_union a x).mp hx
    let v₀ := max v (x + 1)
    have hpend (j : ℕ) : HasArrival a (v₀ + j) := by
      apply (arrival_data a _).2.1.mpr
      exact ⟨x, by dsimp [v₀]; omega,
        stage_monotone a (by dsimp [v₀]; omega) hv, hn _⟩
    let f : ℕ → ℕ := fun j => arrival a (v₀ + j)
    have hi : Function.Injective f := by
      intro j k hjk
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact arrivals_distinct a _ _ (hpend j) (hpend k) (by omega) hjk
      · exact arrivals_distinct a _ _ (hpend k) (hpend j) (by omega) hjk.symm
    have hb : ∀ j, f j ≤ x := by
      intro j
      exact (arrival_data a _).2.2.1 (hpend j) |>.2.2 x
        (by dsimp [v₀]; omega) (stage_monotone a (by dsimp [v₀]; omega) hv) (hn _)
    have hf : (Set.range f).Finite := (Set.finite_Iic x).subset (by
      rintro _ ⟨j, rfl⟩
      exact hb j)
    exact Set.infinite_range_of_injective hi hf
  · rintro ⟨s, hs⟩
    exact (scheduler_invariants a s).2.2 hs

theorem arrival_escape (a u : ℕ) :
    ∃ t, ∀ s ≥ t, HasArrival a s → u ≤ arrival a s := by
  obtain ⟨t, ht⟩ := prefix_settled_exists (indexSet a) (processedSet a)
    (scheduler_monotone a) (scheduler_exhaustive a) u
  refine ⟨t, ?_⟩
  intro s hts hs
  by_contra hn
  have hx := (arrival_data a s).2.2.1 hs
  have hm := (settling_persists (indexSet a) (processedSet a)
    (scheduler_monotone a) (scheduler_exhaustive a) ht hts _ (by omega)).mp
      ((stage_union a _).mpr ⟨s + 1, hx.1⟩)
  exact hx.2.1 hm

end
end Lemmatheca.ComputabilityTheory.FriedbergSplitting
