import Lemmatheca.ThirdLevelIndexSets.Rows

/-! The actual parity-tagged row and diagonal-halting discovery schedule. -/
namespace Lemmatheca.ComputabilityTheory.ComputableDomainIndices
open EffectiveEnumerations UniversalComputation

def rowCode (y z : ℕ) : ℕ := 2 * Nat.pair y z

def haltingCode (y : ℕ) : ℕ := 2 * y + 1

def taggedLabel (c : ℕ) : ℕ :=
  if c % 2 = 0 then (c / 2).unpair.1 else c / 2

noncomputable def taggedEvent (g : ℕ → ℕ → ℕ) (x s c : ℕ) : Bool :=
  decide (c < s) && if c % 2 = 0 then
    decide (stageTest (g x (c / 2).unpair.1) s (c / 2).unpair.2 = 1)
  else decide (stageTest (c / 2) s (c / 2) = 1)

theorem rowCode_primitive : Primrec₂ rowCode := by
  exact Primrec.nat_mul.comp (Primrec.const 2) Primrec₂.natPair

theorem haltingCode_primitive : Primrec haltingCode := by
  exact Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)

theorem taggedLabel_primitive : Primrec taggedLabel := by
  have hh : Primrec (fun c : ℕ => c / 2) := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    (Primrec.fst.comp (Primrec.unpair.comp hh)) hh

theorem tagged_codes (y z : ℕ) :
    taggedLabel (rowCode y z) = y ∧ taggedLabel (haltingCode y) = y ∧
      rowCode y z ≠ haltingCode y := by
  have hrow : taggedLabel (rowCode y z) = y := by
    simp [taggedLabel,rowCode]
  have hhalt : taggedLabel (haltingCode y) = y := by
    have hd : (2*y+1)/2 = y := by omega
    simp [taggedLabel,haltingCode,hd]
  exact ⟨hrow,hhalt,by unfold rowCode haltingCode; omega⟩

theorem rowCode_injective : Function.Injective (fun p : ℕ × ℕ => rowCode p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  change 2 * Nat.pair a b = 2 * Nat.pair c d at h
  have he : Nat.pair a b = Nat.pair c d := by omega
  simpa only [Nat.pair_eq_pair,Prod.mk.injEq] using he

theorem haltingCode_injective : Function.Injective haltingCode := by
  intro a b h
  unfold haltingCode at h
  omega

theorem tags_disjoint (y z i : ℕ) : rowCode y z ≠ haltingCode i := by
  unfold rowCode haltingCode
  omega

private theorem tagged_event_raw (g : ℕ → ℕ → ℕ) (x s c : ℕ) :
    taggedEvent g x s c = true ↔ c < s ∧
      (if c % 2 = 0 then (c/2).unpair.2 ∈ stage (g x (c/2).unpair.1) s
        else c/2 ∈ stage (c/2) s) := by
  by_cases he : c % 2 = 0
  · simp only [taggedEvent,he,ite_true,Bool.and_eq_true,decide_eq_true_eq]
    rw [(stage_test_spec _ _ _).2]
  · simp only [taggedEvent,he,ite_false,Bool.and_eq_true,decide_eq_true_eq]
    rw [(stage_test_spec _ _ _).2]

theorem taggedEvent_primitive (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => taggedEvent g p.1.1 p.1.2 p.2) := by
  have hh : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2 / 2) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hh)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hh)
  have hrow := EffectiveEnumerations.stage_test_primitive.comp
    (((hg.comp (Primrec.fst.comp Primrec.fst) hl).pair
      (Primrec.snd.comp Primrec.fst)).pair hr)
  have hhalt := EffectiveEnumerations.stage_test_primitive.comp
    ((hh.pair (Primrec.snd.comp Primrec.fst)).pair hh)
  have he : PrimrecPred (fun p : (ℕ × ℕ) × ℕ => p.2 % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  exact Primrec.and.comp
    ((Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide)
    (Primrec.ite he ((Primrec.eq.comp hrow (Primrec.const 1)).decide)
      ((Primrec.eq.comp hhalt (Primrec.const 1)).decide))

theorem taggedEvent_bound (g : ℕ → ℕ → ℕ) (x s c : ℕ)
    (h : taggedEvent g x s c = true) : c < s := by
  exact ((tagged_event_raw g x s c).mp h).1

theorem taggedEvent_increasing (g : ℕ → ℕ → ℕ) (x s c : ℕ)
    (h : taggedEvent g x s c = true) : taggedEvent g x (s+1) c = true := by
  obtain ⟨hb,hm⟩ := (tagged_event_raw g x s c).mp h
  apply (tagged_event_raw g x (s+1) c).mpr
  refine ⟨by omega,?_⟩
  by_cases he : c % 2 = 0
  · simp only [he,ite_true] at hm ⊢
    exact stage_monotone _ (Nat.le_succ s) hm
  · simp only [he,ite_false] at hm ⊢
    exact stage_monotone _ (Nat.le_succ s) hm

noncomputable def taggedSchedule (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : ThirdLevelIndexSets.Schedule where
  event := taggedEvent g
  label := taggedLabel
  event_primitive := taggedEvent_primitive g hg
  label_primitive := taggedLabel_primitive
  bounded := taggedEvent_bound g
  increasing := taggedEvent_increasing g

noncomputable abbrev taggedStages (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) :=
  ThirdLevelIndexSets.stages (taggedSchedule g hg)

noncomputable abbrev taggedOutput (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) :=
  ThirdLevelIndexSets.output (taggedSchedule g hg)

theorem tagged_row_spec (g : ℕ → ℕ → ℕ) (x s y z : ℕ) :
    taggedEvent g x s (rowCode y z) = true ↔
      rowCode y z < s ∧ z ∈ stage (g x y) s := by
  simpa [rowCode] using tagged_event_raw g x s (rowCode y z)

theorem tagged_halting_spec (g : ℕ → ℕ → ℕ) (x s y : ℕ) :
    taggedEvent g x s (haltingCode y) = true ↔
      haltingCode y < s ∧ y ∈ stage y s := by
  have hd : (2*y+1)/2 = y := by omega
  simpa [haltingCode,hd] using tagged_event_raw g x s (haltingCode y)

theorem tagged_row_union (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y z : ℕ) :
    rowCode y z ∈ ThirdLevelIndexSets.events (taggedSchedule g hg) x ↔
      z ∈ indexSet (g x y) := by
  constructor
  · rintro ⟨s,hs⟩
    exact (stage_union _ _).mpr ⟨s,((tagged_row_spec g x s y z).mp hs).2⟩
  · intro hz
    obtain ⟨s,hs⟩ := (stage_union _ _).mp hz
    refine ⟨max s (rowCode y z+1), (tagged_row_spec g x _ y z).mpr ⟨?_, ?_⟩⟩
    · omega
    · exact stage_monotone _ (le_max_left _ _) hs

theorem tagged_halting_union (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ) :
    haltingCode y ∈ ThirdLevelIndexSets.events (taggedSchedule g hg) x ↔
      y ∈ haltingDiagonal := by
  constructor
  · rintro ⟨s,hs⟩
    exact (stage_union y y).mpr ⟨s,((tagged_halting_spec g x s y).mp hs).2⟩
  · intro hy
    obtain ⟨s,hs⟩ := (stage_union y y).mp hy
    refine ⟨max s (haltingCode y+1), (tagged_halting_spec g x _ y).mpr ⟨?_, ?_⟩⟩
    · omega
    · exact stage_monotone _ (le_max_left _ _) hs

private theorem tagged_event_monotone (g : ℕ → ℕ → ℕ) (x c : ℕ)
    {s t : ℕ} (hst : s ≤ t) (h : taggedEvent g x s c = true) :
    taggedEvent g x t c = true := by
  induction hst with
  | refl => exact h
  | step ht ih => exact taggedEvent_increasing g x _ c ih

theorem tagged_processed_through_stage (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g)
    (x s c : ℕ) :
    taggedEvent g x s c = true ↔
      ∃ t < s, ThirdLevelIndexSets.fresh (taggedSchedule g hg) x t c = true := by
  constructor
  · intro hs
    induction s with
    | zero => have := taggedEvent_bound g x 0 c hs; omega
    | succ s ih =>
      by_cases ho : taggedEvent g x s c = true
      · obtain ⟨t,ht,hf⟩ := ih ho
        exact ⟨t,by omega,hf⟩
      · exact ⟨s,by omega,by simp [ThirdLevelIndexSets.fresh,taggedSchedule,hs,ho]⟩
  · rintro ⟨t,ht,hf⟩
    have he : taggedEvent g x (t+1) c = true ∧ taggedEvent g x t c = false := by
      simpa only [ThirdLevelIndexSets.fresh,taggedSchedule,Bool.and_eq_true,
        Bool.not_eq_true'] using hf
    exact tagged_event_monotone g x c (by omega) he.1

theorem tagged_label_events (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ) :
    ThirdLevelIndexSets.labelEvents (taggedSchedule g hg) x y =
      ((fun z => rowCode y z) '' indexSet (g x y)) ∪
        {c | c = haltingCode y ∧ y ∈ haltingDiagonal} := by
  ext c
  constructor
  · rintro ⟨hc,hl⟩
    change taggedLabel c = y at hl
    by_cases hp : c % 2 = 0
    · have hlabel : (c/2).unpair.1 = y := by simpa only [taggedLabel,hp,ite_true] using hl
      have he : rowCode y (c/2).unpair.2 = c := by
        unfold rowCode
        rw [← hlabel,Nat.pair_unpair]
        omega
      refine Or.inl ⟨(c/2).unpair.2, ?_, he⟩
      have hc' : rowCode y (c/2).unpair.2 ∈ ThirdLevelIndexSets.events (taggedSchedule g hg) x := by
        rw [he]
        exact hc
      exact (tagged_row_union g hg x y _).mp hc'
    · have hlabel : c/2 = y := by simpa only [taggedLabel,hp,ite_false] using hl
      have he : c = haltingCode y := by unfold haltingCode; omega
      refine Or.inr ⟨he,?_⟩
      apply (tagged_halting_union g hg x y).mp
      rw [← he]
      exact hc
  · rintro (⟨z,hz,rfl⟩ | ⟨rfl,hy⟩)
    · exact ⟨(tagged_row_union g hg x y z).mpr hz,(tagged_codes y z).1⟩
    · exact ⟨(tagged_halting_union g hg x y).mpr hy,(tagged_codes y 0).2.1⟩

theorem tagged_low_finite (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x n : ℕ)
    (hrows : ∀ y, (indexSet (g x y)).Finite) :
    (ThirdLevelIndexSets.lowEvents (taggedSchedule g hg) x n).Finite := by
  have hlabel (y : ℕ) : (ThirdLevelIndexSets.labelEvents (taggedSchedule g hg) x y).Finite := by
    rw [tagged_label_events]
    apply ((hrows y).image (fun z => rowCode y z)).union
    exact (Set.finite_singleton (haltingCode y)).subset (fun _ hc => hc.1)
  have hf : (⋃ y ∈ Set.Iic n, ThirdLevelIndexSets.labelEvents (taggedSchedule g hg) x y).Finite :=
    (Set.finite_Iic n).biUnion (fun y _ => hlabel y)
  apply hf.subset
  intro c hc
  exact Set.mem_iUnion.mpr ⟨(taggedSchedule g hg).label c,
    Set.mem_iUnion.mpr ⟨hc.2,hc.1,rfl⟩⟩

theorem tagged_row_infinite_events (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ)
    (hrow : (indexSet (g x y)).Infinite) :
    (ThirdLevelIndexSets.labelEvents (taggedSchedule g hg) x y).Infinite := by
  have hinj : Function.Injective (fun z => rowCode y z) := by
    intro a b h
    have he : (y,a) = (y,b) := rowCode_injective h
    exact congrArg Prod.snd he
  have hi := hrow.image hinj.injOn
  apply hi.mono
  rw [tagged_label_events]
  exact Set.subset_union_left

theorem tagged_output_cofinite (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ)
    (hrow : (indexSet (g x y)).Infinite) : (taggedOutput g hg x)ᶜ.Finite := by
  exact ThirdLevelIndexSets.output_cofinite_of_infinite_label (taggedSchedule g hg) x y
    (tagged_row_infinite_events g hg x y hrow)

theorem tagged_prefix_stabilization (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x n : ℕ)
    (hrows : ∀ y, (indexSet (g x y)).Finite) :
    ∃ S, (∀ t ≥ S, ∀ i ≤ n,
      ThirdLevelIndexSets.marker (taggedStages g hg x t) i = ThirdLevelIndexSets.marker (taggedStages g hg x S) i) ∧
      ∀ i ≤ n, ThirdLevelIndexSets.marker (taggedStages g hg x S) i ∉ taggedOutput g hg x := by
  exact ThirdLevelIndexSets.bounded_label_stabilization (taggedSchedule g hg) x n
    (tagged_low_finite g hg x n hrows)

theorem tagged_output_coinfinite (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ)
    (hrows : ∀ y, (indexSet (g x y)).Finite) : (taggedOutput g hg x)ᶜ.Infinite := by
  exact ThirdLevelIndexSets.output_coinfinite_of_finite_low (taggedSchedule g hg) x
    (fun n => tagged_low_finite g hg x n hrows)

/-- The new q_g is the old actual ordinary compiler applied to this new schedule. -/
noncomputable abbrev taggedIndex (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : ℕ → ℕ :=
  ThirdLevelIndexSets.index (taggedSchedule g hg)

end Lemmatheca.ComputabilityTheory.ComputableDomainIndices
