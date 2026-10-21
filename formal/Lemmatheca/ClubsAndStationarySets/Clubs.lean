import Mathlib.SetTheory.Cardinal.Cofinality.Club
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Ideal
import Mathlib.Order.Interval.Finset.Nat

/-! Clubs, the club filter and its normality on regular uncountable well-orders.
`IsClub` uses nonempty directed suprema; `closed_iff` connects this to nonzero limits.
-/

namespace Lemmatheca.SetTheory.Clubs

open Set Order Cardinal Ordinal
universe u v

abbrev Carrier (κ : Cardinal.{u}) := κ.ord.ToType

theorem regular_order (κ : Cardinal.{u}) (hκ : κ.IsRegular) :
    IsRegularCardinalOrder (Carrier κ) := by
  constructor
  change typeLT κ.ord.ToType ≤ (cof κ.ord.ToType).ord
  simp only [Ordinal.type_toType, Ordinal.cof_toType, hκ.cof_ord]
  exact le_rfl

instance (κ : Cardinal.{u}) [hκ : Fact κ.IsRegular] :
    IsRegularCardinalOrder (Carrier κ) := regular_order κ hκ.out

instance (κ : Cardinal.{u}) [hκ : Fact κ.IsRegular] : NoMaxOrder (Carrier κ) :=
  Cardinal.noMaxOrder hκ.out.aleph0_le

instance (κ : Cardinal.{u}) [hκ : Fact κ.IsRegular] : Nonempty (Carrier κ) :=
  Ordinal.nonempty_toType_iff.mpr hκ.out.ord_pos.ne'

variable {α : Type u} [LinearOrder α]

private theorem nonempty_of_cof (hα : ℵ₀ < cof α) : Nonempty α := by
  cases isEmpty_or_nonempty α
  · simp at hα
  · assumption

private theorem noMax_of_cof (hα : ℵ₀ < cof α) : NoMaxOrder α := by
  have := nonempty_of_cof hα
  exact (noTopOrder_iff_noMaxOrder α).mp
    (one_lt_cof_iff.mp (one_lt_aleph0.trans hα))

def IsUnbounded (C : Set α) : Prop := ∀ a, ∃ b ∈ C, a < b

def IsOrdinalClosed (C : Set α) : Prop :=
  ∀ δ, Order.IsSuccLimit δ →
    (∀ β < δ, ∃ γ ∈ C, β < γ ∧ γ < δ) → δ ∈ C

theorem unbounded_iff [NoMaxOrder α] (C : Set α) : IsUnbounded C ↔ IsCofinal C := by
  constructor
  · exact fun h a => let ⟨b, hb, hab⟩ := h a; ⟨b, hb, hab.le⟩
  · intro h a
    obtain ⟨b, hab⟩ := exists_gt a
    obtain ⟨c, hc, hbc⟩ := h b
    exact ⟨c, hc, hab.trans_le hbc⟩

theorem closed_iff [WellFoundedLT α] (C : Set α) :
    IsOrdinalClosed C ↔ DirSupClosed C := by
  constructor
  · intro h D hDC hD _ δ hδ
    by_cases hmem : δ ∈ D
    · exact hDC hmem
    apply h δ (hδ.isSuccLimit_of_notMem hD hmem)
    intro β hβ
    obtain ⟨γ, hγ, hβγ, hγδ⟩ := hδ.exists_between hβ
    exact ⟨γ, hDC hγ, hβγ, hγδ.lt_of_ne (fun heq => hmem (heq ▸ hγ))⟩
  · intro h δ hδ hC
    have hne : (C ∩ Iio δ).Nonempty := by
      obtain ⟨β, hβ⟩ := hδ.nonempty_Iio
      obtain ⟨γ, hγ, _, hγδ⟩ := hC β hβ
      exact ⟨γ, hγ, hγδ⟩
    apply h inter_subset_left hne (.of_linearOrder _) ⟨?_, ?_⟩
    · exact fun γ hγ => hγ.2.le
    · intro β hβ
      by_contra hn
      obtain ⟨γ, hγ, hβγ, hγδ⟩ := hC β (lt_of_not_ge hn)
      exact hβγ.not_ge (hβ ⟨hγ, hγδ⟩)

theorem club_iff [WellFoundedLT α] [NoMaxOrder α] (C : Set α) :
    IsClub C ↔ IsOrdinalClosed C ∧ IsUnbounded C := by
  rw [isClub_iff, closed_iff, unbounded_iff]

def limitOrdinals (α : Type u) [LinearOrder α] : Set α := {a | Order.IsSuccLimit a}

def successorPoints (α : Type u) [LinearOrder α] : Set α :=
  {a | ∃ b, b ⋖ a}

theorem tail_club [WellFoundedLT α] [NoMaxOrder α] (a : α) : IsClub (Ioi a) := by
  refine ⟨(isUpperSet_Ioi a).dirSupClosed, ?_⟩
  intro b
  obtain ⟨c, hc⟩ := exists_gt (max a b)
  exact ⟨c, (le_max_left a b).trans_lt hc, ((le_max_right a b).trans_lt hc).le⟩

theorem limits_club [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    IsClub (limitOrdinals α) := by
  classical
  have : NoMaxOrder α := noMax_of_cof hα
  have : Nonempty α := nonempty_of_cof hα
  let : OrderBot α := WellFoundedLT.toOrderBot α
  let : ConditionallyCompleteLinearOrderBot α :=
    WellFoundedLT.conditionallyCompleteLinearOrderBot α
  let : SuccOrder α := SuccOrder.ofLinearWellFoundedLT α
  refine ⟨(closed_iff _).mp (fun δ hδ _ => hδ), ?_⟩
  intro a
  let f : ℕ → α := Nat.rec a (fun _ b => succ b)
  have hf : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    change f n < succ (f n)
    exact Order.lt_succ _
  have hb : BddAbove (range f) := by
    apply BddAbove.of_not_isCofinal
    intro hc
    apply (cof_le hc).not_gt
    exact hα.trans_le' (by simpa using mk_range_le_lift (f := f))
  have hlu : IsLUB (range f) (sSup (range f)) := isLUB_csSup (range_nonempty _) hb
  have hn : sSup (range f) ∉ range f := by
    rintro ⟨n, hn⟩
    exact (hf (Nat.lt_succ_self n)).not_ge (hn ▸ hlu.1 ⟨n + 1, rfl⟩)
  exact ⟨_, hlu.isSuccLimit_of_notMem (range_nonempty _) hn, le_csSup hb ⟨0, rfl⟩⟩

theorem successors_unbounded_not_closed [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    IsUnbounded (successorPoints α) ∧ ¬ IsOrdinalClosed (successorPoints α) := by
  classical
  have : NoMaxOrder α := noMax_of_cof hα
  have : Nonempty α := nonempty_of_cof hα
  let : SuccOrder α := SuccOrder.ofLinearWellFoundedLT α
  constructor
  · intro a
    exact ⟨succ a, ⟨a, covBy_succ a⟩, Order.lt_succ a⟩
  · intro h
    obtain ⟨δ, hδ, _⟩ := (limits_club hα).isCofinal (Classical.choice ‹Nonempty α›)
    obtain ⟨b, hb⟩ := h δ hδ (fun β hβ =>
      ⟨succ β, ⟨β, covBy_succ β⟩, Order.lt_succ β, hδ.succ_lt hβ⟩)
    exact hδ.isSuccPrelimit b hb

/-- Sets containing a club generate the club filter; the membership theorem gives the explicit carrier. -/
def clubFilter (α : Type u) [LinearOrder α] : Filter α := Filter.generate {C | IsClub C}

theorem mem_clubFilter [WellFoundedLT α] (hα : ℵ₀ < cof α) (A : Set α) :
    A ∈ clubFilter α ↔ ∃ C, IsClub C ∧ C ⊆ A := by
  let B : FilterBasis α :=
    { sets := {C | IsClub C}
      nonempty := ⟨univ, IsClub.univ⟩
      inter_sets := fun hC hD => ⟨_, hC.inter hα.ne' hD, Subset.rfl⟩ }
  change A ∈ Filter.generate B.sets ↔ _
  rw [B.generate]
  exact B.mem_filter_iff

theorem clubFilter_neBot [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    Filter.NeBot (clubFilter α) := by
  cases isEmpty_or_nonempty α
  · simp at hα
  · refine Filter.neBot_iff.mpr ?_
    intro h
    obtain ⟨C, hC, hCe⟩ := (mem_clubFilter hα ∅).mp (Filter.empty_mem_iff_bot.mpr h)
    exact hC.nonempty.ne_empty (subset_empty_iff.mp hCe)

theorem clubFilter_complete [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {ι : Type v} (hι : lift.{u} #ι < lift.{v} (cof α)) (A : ι → Set α)
    (hA : ∀ i, A i ∈ clubFilter α) : (⋂ i, A i) ∈ clubFilter α := by
  classical
  choose C hC hCA using fun i => (mem_clubFilter hα (A i)).mp (hA i)
  exact (mem_clubFilter hα _).mpr ⟨_, IsClub.iInter hα.ne' hι hC,
    iInter_mono hCA⟩

theorem nonstationary_iff_compl_mem [WellFoundedLT α] (hα : ℵ₀ < cof α) (S : Set α) :
    ¬ IsStationary S ↔ Sᶜ ∈ clubFilter α := by
  rw [not_isStationary_iff, mem_clubFilter hα]
  constructor
  · rintro ⟨C, hC, hd⟩
    exact ⟨C, hC, disjoint_left.mp hd.symm⟩
  · rintro ⟨C, hC, hsub⟩
    exact ⟨C, hC, disjoint_left.mpr fun _ hS hC => hsub hC hS⟩

theorem stationary_unbounded [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {S : Set α} (hS : IsStationary S) : IsUnbounded S := by
  have : NoMaxOrder α := noMax_of_cof hα
  intro a
  obtain ⟨b, hb, hab⟩ := hS (tail_club a)
  exact ⟨b, hb, hab⟩

theorem stationary_inter_club [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {S C : Set α} (hS : IsStationary S) (hC : IsClub C) : IsStationary (S ∩ C) := by
  intro D hD
  obtain ⟨a, haS, haCD⟩ := hS (hC.inter hα.ne' hD)
  exact ⟨a, ⟨haS, haCD.1⟩, haCD.2⟩

theorem stationary_delete_bounded [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {S A : Set α} (hS : IsStationary S) (hA : BddAbove A) : IsStationary (S \ A) := by
  have : NoMaxOrder α := noMax_of_cof hα
  obtain ⟨a, ha⟩ := hA
  apply (stationary_inter_club hα hS (tail_club a)).mono
  exact fun b hb => ⟨hb.1, fun hbA => hb.2.not_ge (ha hbA)⟩

theorem stationary_restrict_limits [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {S : Set α} (hS : IsStationary S) : IsStationary (S ∩ limitOrdinals α) := by
  exact stationary_inter_club hα hS (limits_club hα)

theorem stationary_cardinality [WellFoundedLT α] [IsRegularCardinalOrder α]
    (hα : ℵ₀ < cof α) {S : Set α} (hS : IsStationary S) : #S = #α := by
  have : NoMaxOrder α := noMax_of_cof hα
  apply (Cardinal.mk_subtype_le S).antisymm
  rw [← cof_eq_cardinalMk]
  exact cof_le ((unbounded_iff S).mp (stationary_unbounded hα hS))

def nonstationaryIdeal (α : Type u) [LinearOrder α] : Set (Set α) := {S | ¬ IsStationary S}

theorem nonstationary_ideal [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    Order.IsIdeal (nonstationaryIdeal α) ∧ (univ : Set α) ∉ nonstationaryIdeal α := by
  have : Nonempty α := nonempty_of_cof hα
  refine ⟨⟨?_, ⟨∅, not_isStationary_empty⟩, ?_⟩, ?_⟩
  · intro S T hTS hS hT
    exact hS (hT.mono hTS)
  · intro S hS T hT
    exact ⟨S ∪ T, fun h => ((isStationary_union_iff hα.ne').mp h).elim hS hT,
      subset_union_left, subset_union_right⟩
  · exact fun h => h IsStationary.univ

theorem stationary_small_fiber [WellFoundedLT α] (hα : ℵ₀ < cof α)
    {β : Type v} (hβ : lift.{u} #β < lift.{v} (cof α))
    {S : Set α} (hS : IsStationary S) (f : α → β) :
    ∃ b, IsStationary (S ∩ f ⁻¹' {b}) := by
  have heq : (⋃ b, S ∩ f ⁻¹' {b}) = S := by
    ext a
    simp
  apply (isStationary_iUnion_iff hα.ne' hβ).mp
  rwa [heq]

def closurePoints (f : α → α) : Set α :=
  {δ | Order.IsSuccLimit δ ∧ ∀ β < δ, f β < δ}

theorem closurePoints_club [WellFoundedLT α] [IsRegularCardinalOrder α]
    (hα : ℵ₀ < cof α) (f : α → α) : IsClub (closurePoints f) := by
  have : NoMaxOrder α := noMax_of_cof hα
  exact (limits_club hα).inter hα.ne' (IsClub.diag hα.ne' (fun β => tail_club (f β)))

def diagonalIntersection (A : α → Set α) : Set α := {δ | ∀ ξ < δ, δ ∈ A ξ}

theorem diagonal_minimum [OrderBot α] (A : α → Set α) : ⊥ ∈ diagonalIntersection A := by
  intro ξ hξ
  exact False.elim (not_lt_bot hξ)

def IsNormalFilter (F : Filter α) : Prop :=
  ∀ A : α → Set α, (∀ i, A i ∈ F) → diagonalIntersection A ∈ F

theorem clubFilter_normal [WellFoundedLT α] [IsRegularCardinalOrder α]
    (hα : ℵ₀ < cof α) : IsNormalFilter (clubFilter α) := by
  intro A hA
  classical
  choose C hC hCA using fun i => (mem_clubFilter hα (A i)).mp (hA i)
  exact (mem_clubFilter hα _).mpr ⟨_, IsClub.diag hα.ne' hC,
    fun δ hδ ξ hξ => hCA ξ (hδ ξ hξ)⟩

theorem tails_intersections :
    (⋂ a : α, Ioi a) = ∅ ∧ diagonalIntersection (fun a : α => Ioi a) = Set.univ := by
  constructor
  · ext a
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false]
    exact fun h => lt_irrefl a (h a)
  · ext a
    simp [diagonalIntersection]

theorem successors_nonstationary [WellFoundedLT α] (hα : ℵ₀ < cof α) :
    ¬ IsStationary (successorPoints α) := by
  intro hS
  obtain ⟨δ, ⟨b, hb⟩, hδ⟩ := hS (limits_club hα)
  exact hδ.isSuccPrelimit b hb

theorem nat_club_iff_infinite (C : Set ℕ) : IsClub C ↔ C.Infinite := by
  rw [club_iff]
  have hclosed : IsOrdinalClosed C := by
    intro δ hδ
    exact False.elim (not_isSuccLimit_of_isSuccArchimedean hδ)
  simp only [hclosed, true_and]
  constructor
  · intro h
    exact Set.infinite_of_forall_exists_gt h
  · intro h a
    exact h.exists_gt a

end Lemmatheca.SetTheory.Clubs
