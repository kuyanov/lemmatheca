import Lemmatheca.ThirdLevelIndexSets.Engine
import Lemmatheca.IndexSetCompleteness.Classification

/-! Uniform rows and their actual bounded cumulative event schedule. -/
namespace Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets
open EffectiveEnumerations ArithmeticalHierarchy UniversalComputation

/-- One jointly primitive-recursive row compiler, before either parameter varies. -/
theorem uniform_infinite_rows (A : Set ℕ) (hA : Sigma ∅ 3 A) :
    ∃ g : ℕ → ℕ → ℕ, Primrec₂ g ∧
      ∀ x, x ∈ A ↔ ∃ y, (indexSet (g x y)).Infinite := by
  obtain ⟨R,hR,he⟩ := (sigma_succ_iff ∅ 2 A).mp hA
  obtain ⟨r,hr,hp,hg⟩ := IndexSetCompleteness.infinitude_primitive_hardness
    {w | R w.unpair.1 w.unpair.2} hR
  let g : ℕ → ℕ → ℕ := fun x y => IndexSetCompleteness.finiteMap r hr (Nat.pair x y)
  refine ⟨g, hp.comp Primrec₂.natPair, fun x => ?_⟩
  apply (he x).trans
  apply exists_congr
  intro y
  simpa only [Nat.unpair_pair, Set.mem_ofPred_eq, IndexSetCompleteness.Infinitude, g]
    using hg (Nat.pair x y)

noncomputable def rowEvent (g : ℕ → ℕ → ℕ) (x s c : ℕ) : Bool :=
  decide (c < s) && decide (stageTest (g x c.unpair.1) s c.unpair.2 = 1)

def rowLabel (c : ℕ) : ℕ := c.unpair.1

private theorem row_event_raw (g : ℕ → ℕ → ℕ) (x s c : ℕ) :
    rowEvent g x s c = true ↔ c < s ∧ c.unpair.2 ∈ stage (g x c.unpair.1) s := by
  simp only [rowEvent, Bool.and_eq_true, decide_eq_true_eq]
  rw [(stage_test_spec _ _ _).2]

theorem rowEvent_primitive (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => rowEvent g p.1.1 p.1.2 p.2) := by
  have hl : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hr : Primrec (fun p : (ℕ × ℕ) × ℕ => p.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hg' := hg.comp (Primrec.fst.comp Primrec.fst) hl
  exact Primrec.and.comp
    ((Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide)
    ((Primrec.eq.comp
      (EffectiveEnumerations.stage_test_primitive.comp ((hg'.pair (Primrec.snd.comp Primrec.fst)).pair hr))
      (Primrec.const 1)).decide)

theorem rowEvent_bound (g : ℕ → ℕ → ℕ) (x s c : ℕ)
    (h : rowEvent g x s c = true) : c < s := by
  exact ((row_event_raw g x s c).mp h).1

theorem rowEvent_increasing (g : ℕ → ℕ → ℕ) (x s c : ℕ)
    (h : rowEvent g x s c = true) : rowEvent g x (s+1) c = true := by
  obtain ⟨hb,hm⟩ := (row_event_raw g x s c).mp h
  exact (row_event_raw g x (s+1) c).mpr
    ⟨by omega, stage_monotone _ (Nat.le_succ s) hm⟩

noncomputable def rowSchedule (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : Schedule where
  event := rowEvent g
  label := rowLabel
  event_primitive := rowEvent_primitive g hg
  label_primitive := Primrec.fst.comp Primrec.unpair
  bounded := rowEvent_bound g
  increasing := rowEvent_increasing g

theorem row_event_spec (g : ℕ → ℕ → ℕ) (x s y z : ℕ) :
    rowEvent g x s (Nat.pair y z) = true ↔
      Nat.pair y z < s ∧ z ∈ stage (g x y) s := by
  simpa only [Nat.unpair_pair] using row_event_raw g x s (Nat.pair y z)

theorem row_event_union (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y z : ℕ) :
    Nat.pair y z ∈ events (rowSchedule g hg) x ↔ z ∈ indexSet (g x y) := by
  constructor
  · rintro ⟨s,hs⟩
    exact (stage_union _ _).mpr ⟨s,((row_event_spec g x s y z).mp hs).2⟩
  · intro hz
    obtain ⟨s,hs⟩ := (stage_union _ _).mp hz
    refine ⟨max s (Nat.pair y z+1), (row_event_spec g x _ y z).mpr ⟨?_, ?_⟩⟩
    · omega
    · exact stage_monotone _ (le_max_left _ _) hs

theorem row_label_events (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ) :
    labelEvents (rowSchedule g hg) x y =
      (fun z => Nat.pair y z) '' indexSet (g x y) := by
  ext c
  constructor
  · rintro ⟨hc,hl⟩
    change c.unpair.1 = y at hl
    have he : Nat.pair y c.unpair.2 = c := by
      simpa only [← hl] using Nat.pair_unpair c
    refine ⟨c.unpair.2, ?_, he⟩
    have hc' : Nat.pair y c.unpair.2 ∈ events (rowSchedule g hg) x := by
      rw [he]
      exact hc
    exact (row_event_union g hg x y _).mp hc'
  · rintro ⟨z,hz,rfl⟩
    refine ⟨(row_event_union g hg x y z).mpr hz, ?_⟩
    change (Nat.pair y z).unpair.1 = y
    simp only [Nat.unpair_pair]

theorem row_label_finite_iff (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ) :
    (labelEvents (rowSchedule g hg) x y).Finite ↔ (indexSet (g x y)).Finite := by
  rw [row_label_events]
  exact Set.finite_image_iff (show Function.Injective (fun z => Nat.pair y z) by
    intro a b h
    simpa using h).injOn

theorem row_label_infinite_iff (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x y : ℕ) :
    (labelEvents (rowSchedule g hg) x y).Infinite ↔ (indexSet (g x y)).Infinite := by
  exact not_congr (row_label_finite_iff g hg x y)

theorem row_low_finite (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x n : ℕ)
    (h : ∀ y, (indexSet (g x y)).Finite) :
    (lowEvents (rowSchedule g hg) x n).Finite := by
  have hf : (⋃ y ∈ Set.Iic n, labelEvents (rowSchedule g hg) x y).Finite :=
    (Set.finite_Iic n).biUnion (fun y _ => (row_label_finite_iff g hg x y).mpr (h y))
  apply hf.subset
  intro c hc
  exact Set.mem_iUnion.mpr ⟨(rowSchedule g hg).label c,
    Set.mem_iUnion.mpr ⟨hc.2, hc.1, rfl⟩⟩

theorem row_output_cofinite_iff (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ) :
    ((output (rowSchedule g hg) x)ᶜ).Finite ↔
      ∃ y, (indexSet (g x y)).Infinite := by
  classical
  constructor
  · intro hco
    by_contra hnone
    have hall : ∀ y, (indexSet (g x y)).Finite := by
      simpa only [not_exists, Set.Infinite, not_not] using hnone
    exact (output_coinfinite_of_finite_low (rowSchedule g hg) x
      (fun n => row_low_finite g hg x n hall)) hco
  · rintro ⟨y,hy⟩
    exact output_cofinite_of_infinite_label (rowSchedule g hg) x y
      ((row_label_infinite_iff g hg x y).mpr hy)

theorem row_output_coinfinite (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) (x : ℕ)
    (h : ∀ y, (indexSet (g x y)).Finite) :
    ((output (rowSchedule g hg) x)ᶜ).Infinite := by
  exact output_coinfinite_of_finite_low (rowSchedule g hg) x
    (fun n => row_low_finite g hg x n h)

/-- The one paired-input stage-search recognizer, usable with every supplied schedule. -/
def recognize (σ : Schedule) (x z : ℕ) : Part ℕ :=
  (Nat.rfind (fun s => Part.some ((stages σ x s).contains z))).map (fun _ => 0)

theorem recognize_partial (σ : Schedule) :
    Nat.Partrec (Nat.unpaired (recognize σ)) := by
  have horder : Primrec (fun p : (ℕ × ℕ) × ℕ => ((p.1.1,p.2),p.1.2)) :=
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
      (Primrec.snd.comp Primrec.fst)
  have hpr : Primrec (fun p : (ℕ × ℕ) × ℕ => (stages σ p.1.1 p.2).contains p.1.2) :=
    Primrec.comp (Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets.stage_test_primitive σ) horder
  have hb : Computable₂ (fun (p : ℕ × ℕ) s => (stages σ p.1 s).contains p.2) := hpr.to_comp
  have hp : Partrec₂ (fun (p : ℕ × ℕ) s => Part.some ((stages σ p.1 s).contains p.2)) := hb
  have hz : Computable₂ (fun (_ : ℕ × ℕ) (_ : ℕ) => (0 : ℕ)) := Computable.const 0
  have hrec : Partrec₂ (recognize σ) :=
    (Partrec.map (g := fun (_ : ℕ × ℕ) (_ : ℕ) => (0 : ℕ)) (Partrec.rfind hp) hz).to₂
  exact Partrec₂.unpaired'.mpr hrec

theorem recognize_domain (σ : Schedule) (x z : ℕ) :
    (recognize σ x z).Dom ↔ z ∈ output σ x := by
  change (Nat.rfind (fun s => Part.some ((stages σ x s).contains z))).Dom ↔ _
  constructor
  · intro h
    obtain ⟨s,hs,_⟩ := Nat.rfind_dom.mp h
    exact ⟨s, List.contains_iff_mem.mp ((Part.mem_some_iff.mp hs).symm)⟩
  · rintro ⟨s,hs⟩
    exact Nat.rfind_dom.mpr ⟨s, Part.mem_some_iff.mpr
      (List.contains_iff_mem.mpr hs).symm, fun {_} _ => trivial⟩

theorem recognize_output (σ : Schedule) (x z v : ℕ) :
    v ∈ recognize σ x z ↔ v = 0 ∧ z ∈ output σ x := by
  constructor
  · intro hv
    obtain ⟨s,hs,he⟩ := (Part.mem_map_iff _).mp hv
    exact ⟨he.symm, (recognize_domain σ x z).mp hv.1⟩
  · rintro ⟨rfl,hz⟩
    exact ⟨(recognize_domain σ x z).mpr hz,rfl⟩

noncomputable def program (σ : Schedule) : ℕ :=
  Classical.choose (phi_complete (recognize_partial σ))

noncomputable def index (σ : Schedule) (x : ℕ) : ℕ := specialize (program σ) x

theorem program_eval (σ : Schedule) : phi (program σ) = Nat.unpaired (recognize σ) := by
  exact Classical.choose_spec (phi_complete (recognize_partial σ))

theorem index_primitive (σ : Schedule) : Primrec (index σ) := by
  exact specialize_primitive.comp (Primrec.const _) Primrec.id

theorem index_eval (σ : Schedule) (x z : ℕ) :
    phi (index σ x) z = recognize σ x z := by
  rw [index, specialize_eval, program_eval]
  simp only [Nat.unpaired, Nat.unpair_pair]

theorem index_domain (σ : Schedule) (x : ℕ) : indexSet (index σ x) = output σ x := by
  ext z
  change (phi (index σ x) z).Dom ↔ _
  rw [index_eval, recognize_domain]

/-- The displayed h_g is precisely specialization of the one fixed stage program. -/
noncomputable abbrev rowIndex (g : ℕ → ℕ → ℕ) (hg : Primrec₂ g) : ℕ → ℕ :=
  index (rowSchedule g hg)

end Lemmatheca.ComputabilityTheory.ThirdLevelIndexSets
