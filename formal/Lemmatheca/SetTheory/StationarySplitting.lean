import Lemmatheca.SetTheory.Clubs
import Mathlib.SetTheory.Cardinal.Regular

/-! Ulam matrices at infinite successor cardinals. The small ordinal carrier
represents the ordinals below the cardinal without a universe change. -/

noncomputable section
namespace Lemmatheca.SetTheory.StationarySplitting

open Set Order Cardinal Ordinal
universe u

abbrev Carrier (κ : Cardinal.{u}) := Clubs.Carrier κ

structure UlamMatrix (κ : Cardinal.{u}) where
  encode : ∀ β : Carrier (Order.succ κ), Set.Iio β ↪ Carrier κ

def UlamMatrix.cell {κ : Cardinal.{u}} (M : UlamMatrix κ)
    (i : Carrier κ) (α : Carrier (Order.succ κ)) : Set (Carrier (Order.succ κ)) :=
  {β | ∃ h : α < β, M.encode β ⟨α, h⟩ = i}

theorem matrix_exists (κ : Cardinal.{u}) : Nonempty (UlamMatrix κ) := by
  classical
  have he (β : Carrier (Order.succ κ)) : Nonempty (Set.Iio β ↪ Carrier κ) := by
    apply (Cardinal.le_def _ _).mp
    have hb := Cardinal.mk_Iio_lt β (by simp [Carrier, Clubs.Carrier])
    have hb' : Cardinal.mk (Set.Iio β) < Order.succ κ := by
      simpa [Carrier, Clubs.Carrier] using hb
    simpa [Carrier, Clubs.Carrier] using (Order.lt_succ_iff.mp hb')
  exact ⟨⟨fun β => Classical.choice (he β)⟩⟩

theorem cell_identities {κ : Cardinal.{u}} (M : UlamMatrix κ) :
    (∀ α, Pairwise (fun i j => Disjoint (M.cell i α) (M.cell j α))) ∧
    (∀ i, Pairwise (fun α β => Disjoint (M.cell i α) (M.cell i β))) ∧
    ∀ α, (⋃ i, M.cell i α) = Set.Ioi α := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro α i j hij
    rw [Set.disjoint_left]
    rintro β ⟨hi, hbi⟩ ⟨hj, hbj⟩
    exact hij (hbi.symm.trans hbj)
  · intro i α β hab
    rw [Set.disjoint_left]
    rintro γ ⟨ha, hai⟩ ⟨hb, hbi⟩
    have he := M.encode γ |>.injective (hai.trans hbi.symm)
    exact hab (congrArg Subtype.val he)
  · intro α
    ext β
    simp only [Set.mem_iUnion, UlamMatrix.cell, Set.mem_ofPred_eq, Set.mem_Ioi]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨M.encode β ⟨α, h⟩, h, rfl⟩⟩

theorem stationary_cell {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (M : UlamMatrix κ) (S : Set (Carrier (Order.succ κ))) (hS : IsStationary S)
    (α : Carrier (Order.succ κ)) :
    ∃ i, IsStationary (S ∩ M.cell i α) := by
  classical
  have hr := Cardinal.isRegular_succ hκ
  let : Fact (Order.succ κ).IsRegular := ⟨hr⟩
  have hcof : cof (Carrier (Order.succ κ)) = Order.succ κ := by
    simp [Carrier, Clubs.Carrier]
  have hu : ℵ₀ < cof (Carrier (Order.succ κ)) := by
    rw [hcof]
    exact hκ.trans_lt (Order.lt_succ κ)
  have hi : Nonempty (Carrier κ) := Ordinal.nonempty_toType_iff.mpr
    (Cardinal.ord_pos.mpr (Cardinal.aleph0_pos.trans_le hκ)).ne'
  let f : Carrier (Order.succ κ) → Carrier κ := fun β =>
    if h : α ∈ Set.Iio β then M.encode β ⟨α, h⟩ else Classical.choice hi
  have hs := Clubs.stationary_inter_club hu hS (Clubs.tail_club α)
  obtain ⟨i, hi⟩ := Clubs.stationary_small_fiber hu
    (β := Carrier κ) (by simp [Carrier, Clubs.Carrier]) hs f
  refine ⟨i, hi.mono ?_⟩
  rintro β ⟨⟨hbS, hbα⟩, hbi⟩
  refine ⟨hbS, hbα, ?_⟩
  change f β = i at hbi
  dsimp only [f] at hbi
  have hb : α ∈ Set.Iio β := hbα
  rwa [dite_eq_left hb] at hbi

theorem ulam_disjoint {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (S : Set (Carrier (Order.succ κ))) (hS : IsStationary S) :
    ∃ P : Carrier (Order.succ κ) → Set (Carrier (Order.succ κ)),
      (∀ i, P i ⊆ S ∧ IsStationary (P i)) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) := by
  classical
  let M := Classical.choice (matrix_exists κ)
  choose g hg using stationary_cell hκ M S hS
  let F : Carrier κ → Set (Carrier (Order.succ κ)) := fun i => {α | g α = i}
  have hlarge : ∃ i, Cardinal.mk (F i) = Order.succ κ := by
    by_contra h
    have hsmall : ∀ i, Cardinal.mk (F i) < Order.succ κ := by
      intro i
      have hle : Cardinal.mk (F i) ≤ Order.succ κ := by
        have hm : Cardinal.mk (Carrier (Order.succ κ)) = Order.succ κ := by simp [Carrier, Clubs.Carrier]
        exact (Cardinal.mk_subtype_le (F i)).trans_eq hm
      exact lt_of_le_of_ne hle (fun he => h ⟨i, he⟩)
    have hu : (⋃ i, F i) = Set.univ := by ext α; simp [F]
    have hc := (Cardinal.card_iUnion_lt_iff_forall_of_isRegular
      (Cardinal.isRegular_succ hκ)
      (by simp [Carrier, Clubs.Carrier])).mpr hsmall
    rw [hu] at hc
    simp [Carrier, Clubs.Carrier] at hc
  obtain ⟨i, hi⟩ := hlarge
  obtain ⟨e⟩ : Nonempty (Carrier (Order.succ κ) ↪ F i) := by
    apply (Cardinal.le_def _ _).mp
    simp [Carrier, Clubs.Carrier, hi]
  refine ⟨fun ξ => S ∩ M.cell i (e ξ).val, ?_, ?_⟩
  · intro ξ
    refine ⟨inter_subset_left, ?_⟩
    have hgi : g (e ξ).val = i := (e ξ).property
    simpa only [hgi] using hg (e ξ).val
  · intro ξ η hne
    apply Disjoint.mono inter_subset_right inter_subset_right
    apply (cell_identities M).2.1 i
    intro he
    exact hne (e.injective (Subtype.ext he))

theorem ulam_partition {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (S : Set (Carrier (Order.succ κ))) (hS : IsStationary S) :
    ∃ P : Carrier (Order.succ κ) → Set (Carrier (Order.succ κ)),
      (∀ i, IsStationary (P i)) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
        (⋃ i, P i) = S := by
  classical
  obtain ⟨P, hP, hd⟩ := ulam_disjoint hκ S hS
  have hr := Cardinal.isRegular_succ hκ
  let : Fact (Order.succ κ).IsRegular := ⟨hr⟩
  let z : Carrier (Order.succ κ) := Classical.arbitrary _
  let R := S \ ⋃ i, P i
  let Q : Carrier (Order.succ κ) → Set (Carrier (Order.succ κ)) :=
    fun i => if i = z then P i ∪ R else P i
  have hPQ (i) : P i ⊆ Q i := by simp [Q]; split_ifs <;> simp
  refine ⟨Q, fun i => (hP i).2.mono (hPQ i), ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hR (k) : Disjoint R (P k) := by
      rw [Set.disjoint_left]
      exact fun _ hx hk => hx.2 (mem_iUnion.mpr ⟨k, hk⟩)
    by_cases hiz : i = z <;> by_cases hjz : j = z
    · exact hij (hiz.trans hjz.symm) |>.elim
    · rcases (by simpa [Q, hiz] using hxi : x ∈ P i ∪ R) with hx | hx
      · exact Set.disjoint_left.mp (hd hij) hx (by simpa [Q, hjz] using hxj)
      · exact Set.disjoint_left.mp (hR j) hx (by simpa [Q, hjz] using hxj)
    · rcases (by simpa [Q, hjz] using hxj : x ∈ P j ∪ R) with hx | hx
      · exact Set.disjoint_left.mp (hd hij) (by simpa [Q, hiz] using hxi) hx
      · exact Set.disjoint_left.mp (hR i) hx (by simpa [Q, hiz] using hxi)
    · exact Set.disjoint_left.mp (hd hij) (by simpa [Q, hiz] using hxi)
        (by simpa [Q, hjz] using hxj)
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      by_cases hiz : i = z
      · rcases (by simpa [Q, hiz] using hi : x ∈ P i ∪ R) with hx | hx
        · exact (hP i).1 hx
        · exact hx.1
      · exact (hP i).1 (by simpa [Q, hiz] using hi)
    · intro hx
      by_cases hm : x ∈ ⋃ i, P i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hm
        exact mem_iUnion.mpr ⟨i, hPQ i hi⟩
      · exact mem_iUnion.mpr ⟨z, by simp [Q, R, hx, hm]⟩

theorem disjoint_stationary_no_club {κ : Cardinal.{u}} (_hκ : κ.IsRegular)
    (_hu : ℵ₀ < κ) {S T : Set (Carrier κ)} (hT : IsStationary T)
    (hd : Disjoint S T) : ¬ ∃ C, C ⊆ S ∧ IsClub C := by
  rintro ⟨C, hCS, hC⟩
  obtain ⟨x, hxT, hxC⟩ := hT hC
  exact Set.disjoint_left.mp hd (hCS hxC) hxT

theorem disjoint_nonempty_cardinality {α ι : Type u} (P : ι → Set α)
    (hn : ∀ i, (P i).Nonempty) (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Cardinal.mk ι ≤ Cardinal.mk (⋃ i, P i) := by
  classical
  choose x hx using hn
  let e : ι → (⋃ i, P i) := fun i => ⟨x i, Set.mem_iUnion.mpr ⟨i, hx i⟩⟩
  apply Cardinal.mk_le_of_injective (f := e)
  intro i j he
  by_contra hij
  have he' : x i = x j := congrArg Subtype.val he
  exact Set.disjoint_left.mp (hd hij) (hx i) (he' ▸ hx j)

end Lemmatheca.SetTheory.StationarySplitting
