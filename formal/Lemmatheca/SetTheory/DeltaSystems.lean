import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Lemmatheca.SetTheory.Clubs

namespace Lemmatheca.SetTheory.DeltaSystems

open Set
universe u
variable {α : Type u}

def IsDeltaSystem (A : Set (Set α)) (r : Set α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → a ∩ b = r

theorem root_subset_of_two {A : Set (Set α)} {r : Set α} (hA : IsDeltaSystem A r)
    {a b : Set α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) : r ⊆ a := by
  rw [← hA a ha b hb hab]
  exact inter_subset_left

theorem petals_disjoint {A : Set (Set α)} {r : Set α} (hA : IsDeltaSystem A r) :
    A.Pairwise (fun a b => Disjoint (a \ r) (b \ r)) := by
  intro a ha b hb hab
  rw [Set.disjoint_left]
  intro x hxa hxb
  have hx : x ∈ r := (hA a ha b hb hab) ▸ (show x ∈ a ∩ b from ⟨hxa.1, hxb.1⟩)
  exact hxa.2 hx

theorem of_disjoint_petals {A : Set (Set α)} {r : Set α}
    (hr : ∀ a ∈ A, r ⊆ a) (hA : A.Pairwise (fun a b => Disjoint (a \ r) (b \ r))) :
    IsDeltaSystem A r := by
  intro a ha b hb hab
  ext x
  constructor
  · intro hx
    by_contra hxr
    exact Set.disjoint_left.mp (hA ha hb hab) ⟨hx.1, hxr⟩ ⟨hx.2, hxr⟩
  · intro hx
    exact ⟨hr a ha hx, hr b hb hx⟩

theorem root_finite_of_two {A : Set (Set α)} {r : Set α} (hA : IsDeltaSystem A r)
    {a b : Set α} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hfa : a.Finite) :
    r.Finite := by
  exact hfa.subset (root_subset_of_two hA ha hb hab)

theorem disjoint_is_delta {A : Set (Set α)} (hA : A.Pairwise Disjoint) :
    IsDeltaSystem A ∅ := by
  intro a ha b hb hab
  exact Set.disjoint_iff_inter_eq_empty.mp (hA ha hb hab)

theorem small_family_vacuous {A : Set (Set α)} (hA : A.Subsingleton) (r : Set α) :
    IsDeltaSystem A r := by
  intro a ha b hb hab
  exact False.elim (hab (hA ha hb))

private abbrev delta_Omega : Type u := Clubs.Carrier (Cardinal.aleph 1)

private theorem delta_indexed (F : delta_Omega.{u} → Set delta_Omega.{u})
    (hfinite : ∀ i, (F i).Finite) :
    ∃ S : Set delta_Omega.{u}, ¬ S.Countable ∧ ∃ r, r.Finite ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → F i ∩ F j = r := by
  classical
  have hreg : Fact (Cardinal.aleph 1).IsRegular := ⟨Cardinal.isRegular_aleph_one⟩
  let : Fact (Cardinal.aleph 1).IsRegular := hreg
  let : OrderBot delta_Omega.{u} := WellFoundedLT.toOrderBot _
  have hcof : Cardinal.aleph0 < Order.cof delta_Omega.{u} := by
    simpa only [delta_Omega, Clubs.Carrier, Ordinal.cof_toType,
      Cardinal.isRegular_aleph_one.cof_ord] using Cardinal.aleph0_lt_aleph_one
  let initial (i : delta_Omega.{u}) : Finset delta_Omega.{u} :=
    (hfinite i).toFinset.filter (· < i)
  let f (i : delta_Omega.{u}) := (initial i).sup id
  have hinitial (i x : delta_Omega.{u}) : x ∈ initial i ↔ x ∈ F i ∧ x < i := by
    simp [initial]
  have hregressive : ∀ i ∈ Ioi (⊥ : delta_Omega.{u}), f i < i := by
    intro i hi
    apply (Finset.sup_lt_iff hi).mpr
    intro x hx
    exact (hinitial i x).mp hx |>.2
  have htail : IsStationary (Ioi (⊥ : delta_Omega.{u})) :=
    (Clubs.tail_club _).isStationary hcof.ne'
  obtain ⟨γ, hS⟩ := exists_isStationary_preimage_singleton hcof.ne' htail hregressive
  let S := Ioi (⊥ : delta_Omega.{u}) ∩ f ⁻¹' {γ}
  have hbound (i : delta_Omega.{u}) (hi : i ∈ S) : F i ∩ Iio i ⊆ Iic γ := by
    intro x hx
    have hx' : x ∈ initial i := (hinitial i x).mpr hx
    have hfi : f i = γ := hi.2
    exact hfi ▸ (Finset.le_sup (f := id) hx')
  have hcount : (Iic γ).Countable := by
    have hc : Cardinal.mk (Iio (Order.succ γ)) < Cardinal.aleph 1 := by
      simpa only [delta_Omega, Clubs.Carrier, Cardinal.mk_toType, Cardinal.card_ord] using
        Cardinal.mk_Iio_lt (Order.succ γ) (by simp)
    have hc' := Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lt_aleph_one_iff.mp hc)
    exact hc'.mono (fun x hx => (Order.lt_succ_iff (a := x) (b := γ)).mpr hx)
  let P := {r : Set delta_Omega.{u} | r.Finite ∧ r ⊆ Iic γ}
  have hP : P.Countable := Set.countable_ofPred_finite_subset hcount
  let g (i : delta_Omega.{u}) : P :=
    if hi : i ∈ S then ⟨F i ∩ Iio i, (hfinite i).inter_of_left _, hbound i hi⟩
    else ⟨∅, finite_empty, empty_subset _⟩
  have hcardP : Cardinal.lift (Cardinal.mk P) < Cardinal.lift (Order.cof delta_Omega.{u}) := by
    exact Cardinal.lift_lt.mpr
      ((Cardinal.le_aleph0_iff_set_countable.mpr hP).trans_lt hcof)
  obtain ⟨r, hS'⟩ := Clubs.stationary_small_fiber hcof hcardP hS g
  let S' := S ∩ g ⁻¹' {r}
  have hroot (i : delta_Omega.{u}) (hi : i ∈ S') : F i ∩ Iio i = r := by
    have hg : g i = r := hi.2
    simpa only [g, dite_eq_left hi.1, Subtype.mk.injEq] using congrArg Subtype.val hg
  let h (i : delta_Omega.{u}) := Order.succ ((hfinite i).toFinset.sup id)
  have hlt (i x : delta_Omega.{u}) (hx : x ∈ F i) : x < h i := by
    exact (Finset.le_sup (f := id) ((hfinite i).mem_toFinset.mpr hx)).trans_lt (Order.lt_succ _)
  let T := S' ∩ Clubs.closurePoints h
  have hT : IsStationary T := Clubs.stationary_inter_club hcof hS' (Clubs.closurePoints_club hcof h)
  have hunc : ¬ T.Countable := by
    intro hc
    have hcard := Clubs.stationary_cardinality hcof hT
    have hm : Cardinal.mk delta_Omega.{u} = Cardinal.aleph 1 := by
      simp only [delta_Omega, Clubs.Carrier, Cardinal.mk_toType, Cardinal.card_ord]
    have := Cardinal.le_aleph0_iff_set_countable.mpr hc
    rw [hcard, hm] at this
    exact Cardinal.aleph0_lt_aleph_one.not_ge this
  refine ⟨T, hunc, r, r.2.1, ?_⟩
  have hpair (i j : delta_Omega.{u}) (hi : i ∈ T) (hj : j ∈ T) (hij : i < j) :
      F i ∩ F j = r := by
    ext x
    constructor
    · intro hx
      have hxj : x < j := (hlt i x hx.1).trans (hj.2.2 i hij)
      exact (hroot j hj.1) ▸ (show x ∈ F j ∩ Iio j from ⟨hx.2, hxj⟩)
    · intro hx
      exact ⟨((hroot i hi.1).symm ▸ hx : x ∈ F i ∩ Iio i).1,
        ((hroot j hj.1).symm ▸ hx : x ∈ F j ∩ Iio j).1⟩
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hpair i j hi hj hij
  · rw [inter_comm]
    exact hpair j i hj hi hji

theorem uncountable_delta_system {A : Set (Set α)} (hA : ¬ A.Countable)
    (hfinite : ∀ a ∈ A, a.Finite) :
    ∃ B ⊆ A, ¬ B.Countable ∧ ∃ r, r.Finite ∧ IsDeltaSystem B r := by
  classical
  have hm : Cardinal.mk delta_Omega.{u} = Cardinal.aleph 1 := by
    simp only [delta_Omega, Clubs.Carrier, Cardinal.mk_toType, Cardinal.card_ord]
  have hcardA : Cardinal.aleph 1 ≤ Cardinal.mk A := by
    apply Cardinal.aleph_one_le_iff.mpr
    exact lt_of_not_ge (fun h => hA (Cardinal.le_aleph0_iff_set_countable.mp h))
  obtain ⟨e⟩ : Nonempty (delta_Omega.{u} ↪ A) :=
    (Cardinal.le_def _ _).mp (hm ▸ hcardA)
  let F (i : delta_Omega.{u}) : Set α := (e i).1
  have hF (i : delta_Omega.{u}) : (F i).Finite := hfinite _ (e i).2
  have hFinj : Function.Injective F := Subtype.val_injective.comp e.injective
  let U : Set α := ⋃ i, F i
  have hU : Cardinal.mk U ≤ Cardinal.mk delta_Omega.{u} := by
    calc
      Cardinal.mk U ≤ Cardinal.mk delta_Omega.{u} * ⨆ i, Cardinal.mk (F i) :=
        Cardinal.mk_iUnion_le F
      _ ≤ Cardinal.mk delta_Omega.{u} * Cardinal.aleph0 :=
        mul_le_mul' le_rfl (ciSup_le' fun i =>
          Cardinal.le_aleph0_iff_set_countable.mpr (hF i).countable)
      _ = Cardinal.mk delta_Omega.{u} := by
        rw [hm]
        exact Cardinal.mul_eq_left Cardinal.aleph0_lt_aleph_one.le
          Cardinal.aleph0_lt_aleph_one.le Cardinal.aleph0_ne_zero
  obtain ⟨j⟩ : Nonempty (U ↪ delta_Omega.{u}) := (Cardinal.le_def _ _).mp hU
  let G (i : delta_Omega.{u}) : Set delta_Omega.{u} :=
    j '' {x : U | (x : α) ∈ F i}
  have hG (i : delta_Omega.{u}) : (G i).Finite :=
    ((hF i).preimage Subtype.val_injective.injOn).image j
  obtain ⟨S, hS, r, hr, hdelta⟩ := delta_indexed G hG
  let B := F '' S
  let root : Set α := Subtype.val '' (j ⁻¹' r)
  refine ⟨B, ?_, ?_, root, ?_, ?_⟩
  · rintro a ⟨i, _, rfl⟩
    exact (e i).2
  · exact fun hc => hS (countable_of_injective_of_countable_image hFinj.injOn hc)
  · exact (hr.preimage j.injective.injOn).image Subtype.val
  · rintro a ⟨i, hi, rfl⟩ b ⟨k, hk, rfl⟩ hik
    have hik' : i ≠ k := fun heq => hik (congrArg F heq)
    have hg := hdelta i hi k hk hik'
    ext x
    constructor
    · intro hx
      let xU : U := ⟨x, mem_iUnion.mpr ⟨i, hx.1⟩⟩
      have hxi : j xU ∈ G i := ⟨xU, hx.1, rfl⟩
      have hxk : j xU ∈ G k := ⟨xU, hx.2, rfl⟩
      exact ⟨xU, hg ▸ (show j xU ∈ G i ∩ G k from ⟨hxi, hxk⟩), rfl⟩
    · rintro ⟨xU, hxU, rfl⟩
      have hxG : j xU ∈ G i ∩ G k := hg.symm ▸ hxU
      obtain ⟨xi, hxi, hji⟩ := hxG.1
      obtain ⟨xk, hxk, hjk⟩ := hxG.2
      have hxi' : xi = xU := j.injective hji
      have hxk' : xk = xU := j.injective hjk
      exact ⟨hxi' ▸ hxi, hxk' ▸ hxk⟩

theorem initial_segments_no_three [LinearOrder α] {a b c : α}
    (hab : a < b) (hbc : b < c) (r : Set α) :
    ¬ IsDeltaSystem ({Iio a, Iio b, Iio c} : Set (Set α)) r := by
  intro h
  have hab' : Iio a ≠ Iio b := by
    intro heq
    have haa : a ∈ Iio a := heq.symm ▸ (show a ∈ Iio b from hab)
    exact (lt_irrefl a) haa
  have hbc' : Iio b ≠ Iio c := by
    intro heq
    have hbb : b ∈ Iio b := heq.symm ▸ (show b ∈ Iio c from hbc)
    exact (lt_irrefl b) hbb
  have h₁ := h (Iio a) (by simp) (Iio b) (by simp) hab'
  have h₂ := h (Iio b) (by simp) (Iio c) (by simp) hbc'
  have har : a ∈ r := h₂ ▸ (show a ∈ Iio b ∩ Iio c from ⟨hab, hab.trans hbc⟩)
  have haa : a ∈ Iio a := (h₁.symm ▸ har : a ∈ Iio a ∩ Iio b).1
  exact (lt_irrefl a) haa

/-- A family of strict initial segments cannot have three distinct members in a Δ-system. -/
theorem initial_segment_delta_small [LinearOrder α] {B : Set (Set α)}
    (hB : B ⊆ Set.range (fun a : α => Iio a)) {r : Set α} (hdelta : IsDeltaSystem B r) :
    B.Finite ∧ B.ncard ≤ 2 := by
  classical
  have hordered (a b c : α) (ha : Iio a ∈ B) (hb : Iio b ∈ B) (hc : Iio c ∈ B)
      (hab : a < b) (hbc : b < c) : False := by
    apply initial_segments_no_three hab hbc r
    have hsub : ({Iio a, Iio b, Iio c} : Set (Set α)) ⊆ B := by
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    exact fun x hx y hy hxy => hdelta x (hsub hx) y (hsub hy) hxy
  have hthree (a b c : Set α) (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
    obtain ⟨i, rfl⟩ := hB ha
    obtain ⟨j, rfl⟩ := hB hb
    obtain ⟨k, rfl⟩ := hB hc
    have hij : i ≠ j := fun h => hab (congrArg Iio h)
    have hik : i ≠ k := fun h => hac (congrArg Iio h)
    have hjk : j ≠ k := fun h => hbc (congrArg Iio h)
    rcases lt_or_gt_of_ne hij with hij | hji
    · rcases lt_or_gt_of_ne hik with hik | hki
      · rcases lt_or_gt_of_ne hjk with hjk | hkj
        · exact hordered i j k ha hb hc hij hjk
        · exact hordered i k j ha hc hb hik hkj
      · exact hordered k i j hc ha hb hki hij
    · rcases lt_or_gt_of_ne hjk with hjk | hkj
      · rcases lt_or_gt_of_ne hik with hik | hki
        · exact hordered j i k hb ha hc hji hik
        · exact hordered j k i hb hc ha hjk hki
      · exact hordered k j i hc hb ha hkj hji
  by_cases hs : B.Subsingleton
  · have hf := hs.finite
    exact ⟨hf, (Set.ncard_le_one_iff hf).mpr (fun ha hb => hs ha hb) |>.trans (by decide)⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hs
    have hsub : B ⊆ {a, b} := by
      intro c hc
      simp only [mem_insert_iff, mem_singleton_iff]
      by_contra h
      obtain ⟨hca, hcb⟩ := not_or.mp h
      exact hthree a b c ha hb hc hab (fun h => hca h.symm) (fun h => hcb h.symm)
    have hf := (Set.toFinite {a, b}).subset hsub
    refine ⟨hf, ?_⟩
    simpa only [Set.ncard_pair hab] using Set.ncard_le_ncard hsub (Set.toFinite {a, b})

end Lemmatheca.SetTheory.DeltaSystems
