import Lemmatheca.EffectiveEnumerations.Stages

/-! Specified least-member and record-high algorithms, with computability bridges. -/
namespace Lemmatheca.ComputabilityTheory.EffectiveEnumerations

open UniversalComputation

theorem computable_bounded_forall {α : Type*} [Primcodable α] {R : α → ℕ → Prop}
    (hR : ComputablePred (fun p : α × ℕ => R p.1 p.2)) :
    ComputablePred (fun p : α × ℕ => ∀ i < p.2, R p.1 i) := by
  classical
  apply Computable.computablePred
  have hh : Computable₂ (fun p : α × ℕ => fun z : ℕ × Bool => z.2 && decide (R p.1 z.1)) :=
    Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (hR.decide.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)))
  apply (Computable.nat_rec Computable.snd (Computable.const true) hh).of_eq
  intro p
  induction p.2 with
  | zero => simp
  | succ n ih =>
    simp only [ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩


theorem computable_bounded_exists {α : Type*} [Primcodable α] {R : α → ℕ → Prop}
    (hR : ComputablePred (fun p : α × ℕ => R p.1 p.2)) :
    ComputablePred (fun p : α × ℕ => ∃ i < p.2, R p.1 i) := by
  classical
  exact (computable_bounded_forall (R := fun a i => ¬ R a i) hR.not).not.of_eq (fun _ => by simp)

private theorem indicator_computable (A : ℕ → Prop) (h : ComputablePred A) :
    Computable (indicator A) := by
  obtain ⟨f, hf, he⟩ := (decidable_iff_characteristic A).mp h
  exact hf.of_eq he


def IsIncreasingEnumeration (A : Set ℕ) (f : ℕ → ℕ) : Prop :=
  StrictMono f ∧ Set.range f = A

noncomputable def increasingRangeTest (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  indicator (fun x => ∃ n ≤ x, f n = x) x

theorem increasing_range_bounded {f : ℕ → ℕ} (hf : StrictMono f) (x : ℕ) :
    x ∈ Set.range f ↔ ∃ n ≤ x, f n = x := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, hf.le_apply, rfl⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

theorem increasing_range_decidable {f : ℕ → ℕ} (hc : Computable f)
    (hf : StrictMono f) :
    Computable (increasingRangeTest f) ∧
      (∀ x, increasingRangeTest f x = indicator (Set.range f) x) ∧
      ComputablePred (Set.range f) := by
  classical
  have hR : ComputablePred (fun p : ℕ × ℕ => f p.2 = p.1) := by
    apply Computable.computablePred
    exact Primrec.eq.decide.to_comp.comp (hc.comp Computable.snd) Computable.fst
  have hB := computable_bounded_exists (R := fun x n => f n = x) hR
  have hP : ComputablePred (fun x => ∃ n ≤ x, f n = x) :=
    ((hB.decide.comp (Computable.id.pair Computable.succ)).computablePred).of_eq
      (fun x => by simp)
  have heq : (fun x => ∃ n ≤ x, f n = x) = Set.range f :=
    funext (fun x => propext (increasing_range_bounded hf x).symm)
  refine ⟨indicator_computable _ hP, ?_, ?_⟩
  · intro x
    simp only [increasingRangeTest, heq]
  · exact hP.of_eq (fun x => (increasing_range_bounded hf x).symm)

noncomputable def firstMember (A : Set ℕ) (hA : A.Infinite) : ℕ := by
  classical
  exact Nat.find hA.nonempty

noncomputable def nextMember (A : Set ℕ) (hA : A.Infinite) (y : ℕ) : ℕ :=
  @Nat.find (fun x => x ∈ A ∧ y < x) (Classical.decPred _) (hA.exists_gt y)

noncomputable def increasingList (A : Set ℕ) (hA : A.Infinite) : ℕ → ℕ :=
  Nat.rec (firstMember A hA) (fun _ y => nextMember A hA y)

theorem least_members_spec (A : Set ℕ) (hA : A.Infinite) :
    firstMember A hA ∈ A ∧
      (∀ x ∈ A, firstMember A hA ≤ x) ∧
      (∀ y, nextMember A hA y ∈ A ∧ y < nextMember A hA y ∧
        ∀ x ∈ A, y < x → nextMember A hA y ≤ x) := by
  classical
  refine ⟨Nat.find_spec hA.nonempty, ?_, ?_⟩
  · intro x hx
    exact Nat.find_min' _ hx
  · intro y
    let : DecidablePred (fun x => x ∈ A ∧ y < x) := Classical.decPred _
    exact ⟨(Nat.find_spec (hA.exists_gt y)).1, (Nat.find_spec (hA.exists_gt y)).2,
      fun x hx hy => Nat.find_min' _ ⟨hx, hy⟩⟩

theorem next_member_computable (A : Set ℕ) (hA : A.Infinite)
    (hc : ComputablePred A) : Computable (nextMember A hA) := by
  classical
  let : DecidablePred A := Classical.decPred _
  let : DecidableRel (fun y x => x ∈ A ∧ y < x) := fun _ => Classical.decPred _
  have hP : ComputablePred (fun p : ℕ × ℕ => p.2 ∈ A ∧ p.1 < p.2) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun p => decide (A p.2) && decide (p.1 < p.2),
      Primrec.and.to_comp.comp (hc.decide.comp Computable.snd)
        (Primrec.nat_lt.decide.to_comp.comp Computable.fst Computable.snd), ?_⟩
    funext p
    apply propext
    simp
    intro _
    rfl
  exact Computable.find hP (hA.exists_gt)

theorem increasing_list_correct (A : Set ℕ) (hA : A.Infinite) :
    IsIncreasingEnumeration A (increasingList A hA) ∧
      (∀ n x, x ∈ A → x ≤ increasingList A hA n →
        ∃ j ≤ n, increasingList A hA j = x) := by
  let f := increasingList A hA
  obtain ⟨hfirst, hmin, hnext⟩ := least_members_spec A hA
  have hmem : ∀ n, f n ∈ A := by
    intro n
    cases n with
    | zero => exact hfirst
    | succ n => exact (hnext (f n)).1
  have hstrict : StrictMono f := strictMono_nat_of_lt_succ (fun n => (hnext (f n)).2.1)
  have hinv : ∀ n x, x ∈ A → x ≤ f n → ∃ j ≤ n, f j = x := by
    intro n
    induction n with
    | zero =>
      intro x hx hle
      exact ⟨0, le_rfl, le_antisymm (hmin x hx) hle⟩
    | succ n ih =>
      intro x hx hle
      by_cases hxn : x ≤ f n
      · obtain ⟨j, hj, heq⟩ := ih x hx hxn
        exact ⟨j, hj.trans (Nat.le_succ n), heq⟩
      · refine ⟨n + 1, le_rfl, le_antisymm ?_ hle⟩
        exact (hnext (f n)).2.2 x hx (lt_of_not_ge hxn)
  refine ⟨⟨hstrict, ?_⟩, hinv⟩
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact hmem n
  · intro hx
    obtain ⟨j, _, hj⟩ := hinv x x hx hstrict.le_apply
    exact ⟨j, hj⟩

theorem increasing_list_computable (A : Set ℕ) (hA : A.Infinite)
    (hc : ComputablePred A) : Computable (increasingList A hA) := by
  have hh : Computable₂ (fun (_ : ℕ) (z : ℕ × ℕ) => nextMember A hA z.2) :=
    (next_member_computable A hA hc).comp (Computable.snd.comp Computable.snd)
  exact Computable.nat_rec Computable.id (Computable.const (firstMember A hA)) hh

theorem infinite_decidable_iff (A : Set ℕ) (hA : A.Infinite) :
    ComputablePred A ↔ ∃ f, Computable f ∧ IsIncreasingEnumeration A f := by
  constructor
  · intro hc
    exact ⟨increasingList A hA, increasing_list_computable A hA hc,
      (increasing_list_correct A hA).1⟩
  · rintro ⟨f, hc, hf, hrange⟩
    simpa only [hrange] using (increasing_range_decidable hc hf).2.2

def stageStream {A : Set ℕ} (F : ComputableApproximation A) (a₀ : ℕ) (z : ℕ) : ℕ :=
  if F.test z.unpair.1 z.unpair.2 = 1 then z.unpair.2 else a₀

theorem stage_stream_correct {A : Set ℕ} (F : ComputableApproximation A)
    (a₀ : ℕ) (ha : a₀ ∈ A) :
    Computable (stageStream F a₀) ∧ Set.range (stageStream F a₀) = A ∧
      (∀ s x, stageStream F a₀ (Nat.pair s x) =
        (by classical exact if x ∈ F.atStage s then x else a₀)) := by
  classical
  have hp : ComputablePred (fun z : ℕ => F.test z.unpair.1 z.unpair.2 = 1) := by
    apply Computable.computablePred
    exact Primrec.eq.decide.to_comp.comp
      (F.test_computable.comp (Computable.fst.comp Computable.unpair)
        (Computable.snd.comp Computable.unpair)) (Computable.const 1)
  refine ⟨ComputablePred.ite (Computable.snd.comp Computable.unpair) (Computable.const a₀) hp,
    ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      unfold stageStream
      split_ifs with h
      · exact (F.exhaustive _).mpr ⟨_, h⟩
      · exact ha
    · intro hx
      obtain ⟨s, hs⟩ := (F.exhaustive x).mp hx
      exact ⟨Nat.pair s x, by simp [stageStream, hs]⟩
  · intro s x
    simp only [stageStream, Nat.unpair_pair, ComputableApproximation.atStage,
      Set.mem_ofPred_eq]
    split_ifs <;> simp_all

theorem stream_above (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (y : ℕ) :
    ∃ j, y < q j := by
  obtain ⟨x, ⟨j, rfl⟩, h⟩ := hq.exists_gt y
  exact ⟨j, h⟩

noncomputable def recordIndex (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (y : ℕ) : ℕ :=
  Nat.find (stream_above q hq y)

noncomputable def recordHigh (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (y : ℕ) : ℕ :=
  q (recordIndex q hq y)

noncomputable def recordSequence (q : ℕ → ℕ) (hq : (Set.range q).Infinite) : ℕ → ℕ :=
  Nat.rec (q 0) (fun _ y => recordHigh q hq y)

theorem record_index_spec (q : ℕ → ℕ) (hq : (Set.range q).Infinite) (y : ℕ) :
    y < q (recordIndex q hq y) ∧
      ∀ j < recordIndex q hq y, q j ≤ y := by
  refine ⟨Nat.find_spec (stream_above q hq y), ?_⟩
  intro j hj
  exact le_of_not_gt (Nat.find_min (stream_above q hq y) hj)

theorem record_algorithms_computable (q : ℕ → ℕ) (hq : (Set.range q).Infinite)
    (hc : Computable q) :
    Computable (recordIndex q hq) ∧ Computable (recordHigh q hq) ∧
      Computable (recordSequence q hq) := by
  have hk : Computable (recordIndex q hq) := by
    apply Computable.find (P := fun y j => y < q j)
    apply Computable.computablePred
    exact Primrec.nat_lt.decide.to_comp.comp Computable.fst (hc.comp Computable.snd)
  have hH : Computable (recordHigh q hq) := hc.comp hk
  have hh : Computable₂ (fun (_ : ℕ) (z : ℕ × ℕ) => recordHigh q hq z.2) :=
    hH.comp (Computable.snd.comp Computable.snd)
  exact ⟨hk, hH, Computable.nat_rec Computable.id (Computable.const (q 0)) hh⟩

theorem record_sequence_correct (q : ℕ → ℕ) (hq : (Set.range q).Infinite)
    (hc : Computable q) :
    StrictMono (recordSequence q hq) ∧
      Set.range (recordSequence q hq) ⊆ Set.range q ∧
      (Set.range (recordSequence q hq)).Infinite ∧
      ComputablePred (Set.range (recordSequence q hq)) := by
  have hcomp := (record_algorithms_computable q hq hc).2.2
  have hstrict : StrictMono (recordSequence q hq) :=
    strictMono_nat_of_lt_succ (fun n => (record_index_spec q hq (recordSequence q hq n)).1)
  refine ⟨hstrict, ?_, Set.infinite_range_of_injective hstrict.injective,
    (increasing_range_decidable hcomp hstrict).2.2⟩
  rintro x ⟨n, rfl⟩
  cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n => exact ⟨recordIndex q hq (recordSequence q hq n), rfl⟩

theorem specified_records_from_index (e : ℕ) (he : (indexSet e).Infinite)
    (a₀ : ℕ) (ha : a₀ ∈ indexSet e) :
    let q := stageStream (canonicalApproximation e) a₀
    ∃ hq : (Set.range q).Infinite,
      Computable q ∧ Set.range q = indexSet e ∧
      Computable (recordSequence q hq) ∧ StrictMono (recordSequence q hq) ∧
      Set.range (recordSequence q hq) ⊆ indexSet e ∧
      (Set.range (recordSequence q hq)).Infinite ∧
      ComputablePred (Set.range (recordSequence q hq)) := by
  dsimp only
  let q := stageStream (canonicalApproximation e) a₀
  obtain ⟨hcomp, hrange, _⟩ := stage_stream_correct (canonicalApproximation e) a₀ ha
  have hq : (Set.range q).Infinite := hrange.symm ▸ he
  obtain ⟨hstrict, hsub, hinf, hdec⟩ := record_sequence_correct q hq hcomp
  have hsub' : Set.range (recordSequence q hq) ⊆ indexSet e := fun x hx =>
    Eq.mp (congrArg (fun S : Set ℕ => x ∈ S) hrange) (hsub hx)
  exact ⟨hq, hcomp, hrange, (record_algorithms_computable q hq hcomp).2.2,
    hstrict, hsub', hinf, hdec⟩

theorem infinite_enumerable_decidable_subset (A : Set ℕ)
    (hc : REPred A) (hA : A.Infinite) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ ComputablePred B := by
  obtain ⟨e, he⟩ := (enumerable_iff_index A).mp hc
  have hEq : A = indexSet e := Set.ext he
  subst A
  obtain ⟨a₀, ha⟩ := hA.nonempty
  obtain ⟨hq, _, _, _, _, hsub, hinf, hdec⟩ := specified_records_from_index e hA a₀ ha
  exact ⟨_, hsub, hinf, hdec⟩

end Lemmatheca.ComputabilityTheory.EffectiveEnumerations
