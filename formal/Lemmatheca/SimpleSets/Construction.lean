import Lemmatheca.SimpleSets.Immunity
import Mathlib.Order.Interval.Set.Nat

/-! Post's one-output-per-index threshold construction, with its exact counting map. -/
namespace Lemmatheca.ComputabilityTheory.SimpleSets

open UniversalComputation EffectiveEnumerations

def thresholdTest (e w : ℕ) : Prop :=
  2 * e < w.unpair.1 ∧ certificate e w.unpair.1 w.unpair.2

noncomputable def searchStage (e : ℕ) : Part ℕ := by
  classical
  exact Nat.rfind (fun w => Part.some (decide (thresholdTest e w)))

noncomputable def selector (e : ℕ) : Part ℕ :=
  (searchStage e).map (fun w => w.unpair.1)

theorem threshold_test_primitive :
    PrimrecPred (fun p : ℕ × ℕ => thresholdTest p.1 p.2) := by
  have hu := Primrec.unpair.comp (Primrec.snd : Primrec (@Prod.snd ℕ ℕ))
  exact (Primrec.nat_lt.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.fst.comp hu)).and
    (certificate_primitive.comp
      ((Primrec.fst.pair (Primrec.fst.comp hu)).pair (Primrec.snd.comp hu)))

theorem search_stage_partial : Nat.Partrec searchStage := by
  classical
  exact Partrec.nat_iff.mp (Partrec.rfind threshold_test_primitive.computablePred.decide.partrec)

theorem search_stage_spec (e w : ℕ) :
    w ∈ searchStage e ↔ thresholdTest e w ∧ ∀ v < w, ¬ thresholdTest e v := by
  classical
  change (w ∈ Nat.rfind (fun v => Part.some (decide (thresholdTest e v)))) ↔ _
  constructor
  · intro hw
    exact ⟨by simpa using Nat.rfind_spec hw,
      fun v hv => by simpa using Nat.rfind_min hw hv⟩
  · rintro ⟨hw, hmin⟩
    exact Nat.mem_rfind.mpr ⟨by simpa using hw, fun {v} hv => by simpa using hmin v hv⟩

theorem search_stage_domain (e : ℕ) :
    (searchStage e).Dom ↔ ∃ w, thresholdTest e w := by
  classical
  change (Nat.rfind (fun w => Part.some (decide (thresholdTest e w)))).Dom ↔ _
  constructor
  · intro hd
    obtain ⟨w, hw, _⟩ := Nat.rfind_dom.mp hd
    exact ⟨w, by simpa using hw⟩
  · rintro ⟨w, hw⟩
    exact Nat.rfind_dom.mpr ⟨w, by simpa using hw, fun _ => trivial⟩

theorem selector_partial : Nat.Partrec selector := by
  exact (Nat.Partrec.left.comp search_stage_partial).of_eq (fun e => by
    change (searchStage e).bind (fun w => Part.some w.unpair.1) =
      (searchStage e).map (fun w => w.unpair.1)
    exact Part.bind_some_eq_map _ _)

theorem selector_domain (e : ℕ) :
    (selector e).Dom ↔ ∃ x, 2 * e < x ∧ x ∈ indexSet e := by
  change (searchStage e).Dom ↔ _
  rw [search_stage_domain]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.unpair.1, hw.1, (phi_domain e w.unpair.1).mpr ⟨w.unpair.2, hw.2⟩⟩
  · rintro ⟨x, hx, hxe⟩
    obtain ⟨k, hk⟩ := (phi_domain e x).mp hxe
    exact ⟨Nat.pair x k, by simpa [thresholdTest] using And.intro hx hk⟩

theorem selector_sound {e x : ℕ} (hx : x ∈ selector e) :
    2 * e < x ∧ x ∈ indexSet e := by
  obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).mp hx
  have ht := ((search_stage_spec e w).mp hw).1
  exact ⟨ht.1, (phi_domain e w.unpair.1).mpr ⟨w.unpair.2, ht.2⟩⟩

def postSet : Set ℕ := {x | ∃ e, x ∈ selector e}

theorem post_enumerable : REPred postSet := by
  exact (enumerable_iff_partial_range postSet).mpr ⟨selector, selector_partial, fun _ => Iff.rfl⟩

theorem post_member_witness {x : ℕ} (hx : x ∈ postSet) :
    ∃ e, x ∈ selector e ∧ 2 * e < x ∧ x ∈ indexSet e := by
  obtain ⟨e, he⟩ := hx
  exact ⟨e, he, selector_sound he⟩

theorem zero_not_post : 0 ∉ postSet := by
  intro hz
  obtain ⟨e, _, hlt, _⟩ := post_member_witness hz
  omega

def smallSelected (n : ℕ) : Set ℕ := postSet ∩ Set.Iic (2 * n)

theorem small_producing_index {n x : ℕ} (hx : x ∈ smallSelected n) :
    ∃ e, e < n ∧ x ∈ selector e := by
  obtain ⟨e, he, hlt, _⟩ := post_member_witness hx.1
  exact ⟨e, by have hle : x ≤ 2 * n := hx.2; omega, he⟩

noncomputable def leastProducer (n : ℕ) (x : smallSelected n) : ℕ := by
  classical
  exact Nat.find (small_producing_index x.property)

theorem least_producer_spec (n : ℕ) (x : smallSelected n) :
    leastProducer n x < n ∧ x.val ∈ selector (leastProducer n x) ∧
      ∀ e < leastProducer n x, ¬ (e < n ∧ x.val ∈ selector e) := by
  classical
  exact ⟨(Nat.find_spec (small_producing_index x.property)).1,
    (Nat.find_spec (small_producing_index x.property)).2,
    fun _ he => Nat.find_min (small_producing_index x.property) he⟩

noncomputable def countingMap (n : ℕ) (x : smallSelected n) : Fin n :=
  ⟨leastProducer n x, (least_producer_spec n x).1⟩

theorem counting_map_injective (n : ℕ) : Function.Injective (countingMap n) := by
  intro x y he
  apply Subtype.ext
  have hi : leastProducer n x = leastProducer n y := congrArg Fin.val he
  have hx := (least_producer_spec n x).2.1
  have hy := (least_producer_spec n y).2.1
  rw [← hi] at hy
  exact Part.mem_unique hx hy

theorem small_selected_bound (n : ℕ) :
    (smallSelected n).Finite ∧ (smallSelected n).ncard ≤ n := by
  refine ⟨(Set.finite_Iic (2 * n)).subset Set.inter_subset_right, ?_⟩
  simpa only [Nat.card_coe_set_eq, Nat.card_fin] using
    Nat.card_le_card_of_injective (countingMap n) (counting_map_injective n)

theorem small_zero : smallSelected 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hzero : x = 0 := by have hle : x ≤ 0 := hx.2; omega
  subst x
  exact zero_not_post hx.1

theorem omission_bound (n : ℕ) :
    (postSetᶜ ∩ Set.Iic (2 * n)).Finite ∧
      n + 1 ≤ (postSetᶜ ∩ Set.Iic (2 * n)).ncard := by
  refine ⟨(Set.finite_Iic (2 * n)).subset Set.inter_subset_right, ?_⟩
  have hcard := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (Set.Iic (2 * n)) postSet (Set.finite_Iic (2 * n))
  have hselected := (small_selected_bound n).2
  have htotal : (smallSelected n).ncard +
      (postSetᶜ ∩ Set.Iic (2 * n)).ncard = 2 * n + 1 := by
    simpa only [smallSelected, Set.inter_comm, Set.sdiff_eq, Set.ncard_Iic_nat] using hcard
  omega

theorem post_complement_infinite : postSetᶜ.Infinite := by
  intro hfin
  have hbound := (omission_bound postSetᶜ.ncard).2
  have hle := Set.ncard_le_ncard
    (show postSetᶜ ∩ Set.Iic (2 * postSetᶜ.ncard) ⊆ postSetᶜ from Set.inter_subset_left) hfin
  omega

theorem infinite_requirement (e : ℕ) (he : (indexSet e).Infinite) :
    ∃ x, x ∈ selector e ∧ x ∈ postSet ∩ indexSet e := by
  obtain ⟨x, hx, hlt⟩ := he.exists_gt (2 * e)
  have hd := (selector_domain e).mpr ⟨x, hlt, hx⟩
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
  exact ⟨y, hy, ⟨e, hy⟩, (selector_sound hy).2⟩

theorem post_simple : Simple postSet := by
  apply (simple_iff_meets postSet post_enumerable post_complement_infinite).mpr
  intro e he
  obtain ⟨x, _, hxA, hxe⟩ := infinite_requirement e he
  exact ⟨x, hxe, hxA⟩

end Lemmatheca.ComputabilityTheory.SimpleSets
