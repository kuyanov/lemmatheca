import Lemmatheca.SetTheory.SmallFamilies
import Mathlib.Order.Interval.Finset.Nat

/-! Splitting and reaping infinite subsets of the natural numbers. -/

namespace Lemmatheca.SetTheory.SplittingReaping

open Set Filter Cardinal
open FiniteErrors BoundingAndDominating SmallFamilies

def Splits (S X : Set ℕ) : Prop :=
  (X ∩ S).Infinite ∧ (X \ S).Infinite

def IsSplittingFamily (F : Set (Set ℕ)) : Prop :=
  (∀ S ∈ F, S.Infinite) ∧ ∀ X : Set ℕ, X.Infinite → ∃ S ∈ F, Splits S X

def IsReapingFamily (F : Set (Set ℕ)) : Prop :=
  (∀ X ∈ F, X.Infinite) ∧ ∀ S : Set ℕ, ∃ X ∈ F, ¬ Splits S X

noncomputable def splittingNumber : Cardinal :=
  ⨅ F : {F : Set (Set ℕ) // IsSplittingFamily F}, Cardinal.mk F.val

noncomputable def reapingNumber : Cardinal :=
  ⨅ F : {F : Set (Set ℕ) // IsReapingFamily F}, Cardinal.mk F.val

noncomputable def nextPoint (X : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if h : X.Infinite then Nat.find (h.exists_gt n) else n + 1

def intervalEndpoint (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (intervalEndpoint g n + 1) (g (intervalEndpoint g n) + 1)

def alternatingIntervals (g : ℕ → ℕ) : Set ℕ :=
  ⋃ n, Ico (intervalEndpoint g (2 * n)) (intervalEndpoint g (2 * n + 1))

theorem not_splits_iff (S X : Set ℕ) :
    ¬ Splits S X ↔ X ≤ᶠ[cofinite] S ∨ X ≤ᶠ[cofinite] Sᶜ := by
  rw [Splits, not_and_or, almostSubset_iff_finite_sdiff,
    almostSubset_iff_finite_sdiff]
  simp only [Set.not_infinite, Set.sdiff_compl]
  exact or_comm

theorem splits_compl_iff (S X : Set ℕ) : Splits Sᶜ X ↔ Splits S X := by
  change (X \ S).Infinite ∧ (X \ Sᶜ).Infinite ↔ Splits S X
  simp only [Splits, Set.sdiff_compl]
  exact and_comm

theorem nextPoint_spec (X : Set ℕ) (hX : X.Infinite) (n : ℕ) :
    nextPoint X n ∈ X ∧ n < nextPoint X n ∧
      ∀ m ∈ X, n < m → nextPoint X n ≤ m := by
  classical
  simp only [nextPoint, dite_eq_left hX]
  exact ⟨(Nat.find_spec (hX.exists_gt n)).1,
    (Nat.find_spec (hX.exists_gt n)).2,
    fun m hm hnm => Nat.find_min' _ ⟨hm, hnm⟩⟩

private theorem endpoint_strict (g : ℕ → ℕ) : StrictMono (intervalEndpoint g) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

private theorem endpoint_ge (g : ℕ → ℕ) (n : ℕ) : n ≤ intervalEndpoint g n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact (Nat.succ_le_succ ih).trans (le_max_left _ _)

private theorem interval_index_unique (g : ℕ → ℕ) {x i j : ℕ}
    (hi : x ∈ Ico (intervalEndpoint g i) (intervalEndpoint g (i + 1)))
    (hj : x ∈ Ico (intervalEndpoint g j) (intervalEndpoint g (j + 1))) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := (endpoint_strict g).monotone (Nat.succ_le_of_lt h)
    exact False.elim (hi.2.not_ge (this.trans hj.1))
  · exact h
  · have := (endpoint_strict g).monotone (Nat.succ_le_of_lt h)
    exact False.elim (hj.2.not_ge (this.trans hi.1))

private theorem odd_interval_outside (g : ℕ → ℕ) {x n : ℕ}
    (hx : x ∈ Ico (intervalEndpoint g (2 * n + 1))
      (intervalEndpoint g (2 * n + 2))) : x ∉ alternatingIntervals g := by
  intro h
  obtain ⟨m, hm⟩ := mem_iUnion.mp h
  have he := interval_index_unique g hm hx
  omega

theorem interval_properties (g : ℕ → ℕ) :
    StrictMono (intervalEndpoint g) ∧ (∀ n, n ≤ intervalEndpoint g n) ∧
      (⋃ n, Ico (intervalEndpoint g n) (intervalEndpoint g (n + 1))) = Set.univ ∧
      (alternatingIntervals g).Infinite ∧ (alternatingIntervals g)ᶜ.Infinite := by
  refine ⟨endpoint_strict g, endpoint_ge g, ?_, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    have hex : ∃ n, x < intervalEndpoint g (n + 1) :=
      ⟨x, lt_of_lt_of_le (Nat.lt_succ_self x) (endpoint_ge g (x + 1))⟩
    let n := Nat.find hex
    have hn : x < intervalEndpoint g (n + 1) := Nat.find_spec hex
    have hlow : intervalEndpoint g n ≤ x := by
      cases hn0 : n with
      | zero => simp [intervalEndpoint]
      | succ k =>
        have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
        exact le_of_not_gt (by simpa [hn0] using hmin)
    exact mem_iUnion.mpr ⟨n, hlow, hn⟩
  · apply infinite_of_injective_forall_mem (f := fun n => intervalEndpoint g (2 * n))
    · intro m n h
      have := (endpoint_strict g).injective h
      omega
    · intro n
      exact mem_iUnion.mpr ⟨n, le_rfl, endpoint_strict g (by omega)⟩
  · apply infinite_of_injective_forall_mem (f := fun n => intervalEndpoint g (2 * n + 1))
    · intro m n h
      have := (endpoint_strict g).injective h
      omega
    · intro n
      exact odd_interval_outside g ⟨le_rfl, endpoint_strict g (by omega)⟩

theorem bound_splits (g : ℕ → ℕ) (X : Set ℕ) (hX : X.Infinite)
    (hbound : nextPoint X ≤ᶠ[atTop] g) : Splits (alternatingIntervals g) X := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hpoint (k : ℕ) (hk : N ≤ k) :
      nextPoint X (intervalEndpoint g k) ∈ X ∧
      nextPoint X (intervalEndpoint g k) ∈
        Ico (intervalEndpoint g k) (intervalEndpoint g (k + 1)) := by
    have hp := nextPoint_spec X hX (intervalEndpoint g k)
    refine ⟨hp.1, hp.2.1.le, ?_⟩
    exact (hN _ (hk.trans (endpoint_ge g k))).trans_lt
      ((Nat.lt_succ_self _).trans_le (le_max_right _ _))
  have hinj (k l : ℕ) (hk : N ≤ k) (hl : N ≤ l)
      (he : nextPoint X (intervalEndpoint g k) = nextPoint X (intervalEndpoint g l)) : k = l := by
    exact interval_index_unique g (hpoint k hk).2 (he ▸ (hpoint l hl).2)
  constructor
  · apply infinite_of_injective_forall_mem
      (f := fun n => nextPoint X (intervalEndpoint g (2 * (n + N))))
    · intro m n h
      have := hinj _ _ (by omega) (by omega) h
      omega
    · intro n
      exact ⟨(hpoint _ (by omega)).1, mem_iUnion.mpr ⟨n + N, (hpoint _ (by omega)).2⟩⟩
  · apply infinite_of_injective_forall_mem
      (f := fun n => nextPoint X (intervalEndpoint g (2 * (n + N) + 1)))
    · intro m n h
      have := hinj _ _ (by omega) (by omega) h
      omega
    · intro n
      exact ⟨(hpoint _ (by omega)).1, odd_interval_outside g (hpoint _ (by omega)).2⟩

theorem every_infinite_set_has_splitter (X : Set ℕ) (hX : X.Infinite) :
    ∃ S, S.Infinite ∧ Splits S X := by
  exact ⟨alternatingIntervals (nextPoint X), (interval_properties _).2.2.2.1,
    bound_splits _ X hX (Filter.Eventually.of_forall fun _ => le_rfl)⟩

theorem witnesses_exist :
    IsSplittingFamily {X : Set ℕ | X.Infinite} ∧
      IsReapingFamily {X : Set ℕ | X.Infinite} := by
  constructor
  · refine ⟨fun _ h => h, ?_⟩
    intro X hX
    obtain ⟨S, hS, hsplit⟩ := every_infinite_set_has_splitter X hX
    exact ⟨S, hS, hsplit⟩
  · refine ⟨fun _ h => h, ?_⟩
    intro S
    by_cases hS : S.Infinite
    · exact ⟨S, hS, by simp [Splits]⟩
    · exact ⟨Sᶜ, (Set.not_infinite.mp hS).infinite_compl, by simp [Splits]⟩

theorem splittingNumber_spec :
    (∃ F, IsSplittingFamily F ∧ Cardinal.mk F = splittingNumber) ∧
    (∀ F, IsSplittingFamily F → splittingNumber ≤ Cardinal.mk F) := by
  classical
  have : Nonempty {F : Set (Set ℕ) // IsSplittingFamily F} :=
    ⟨⟨_, witnesses_exist.1⟩⟩
  obtain ⟨F, hF⟩ := ciInf_mem
    (fun F : {F : Set (Set ℕ) // IsSplittingFamily F} => Cardinal.mk F.val)
  refine ⟨⟨F.val, F.property, hF⟩, ?_⟩
  intro G hG
  exact ciInf_le'
    (fun F : {F : Set (Set ℕ) // IsSplittingFamily F} => Cardinal.mk F.val) ⟨G, hG⟩

theorem reapingNumber_spec :
    (∃ F, IsReapingFamily F ∧ Cardinal.mk F = reapingNumber) ∧
    (∀ F, IsReapingFamily F → reapingNumber ≤ Cardinal.mk F) := by
  classical
  have : Nonempty {F : Set (Set ℕ) // IsReapingFamily F} :=
    ⟨⟨_, witnesses_exist.2⟩⟩
  obtain ⟨F, hF⟩ := ciInf_mem
    (fun F : {F : Set (Set ℕ) // IsReapingFamily F} => Cardinal.mk F.val)
  refine ⟨⟨F.val, F.property, hF⟩, ?_⟩
  intro G hG
  exact ciInf_le'
    (fun F : {F : Set (Set ℕ) // IsReapingFamily F} => Cardinal.mk F.val) ⟨G, hG⟩

theorem number_upper_bounds : splittingNumber ≤ continuum ∧ reapingNumber ≤ continuum := by
  have hupper (F : Set (Set ℕ)) : Cardinal.mk F ≤ continuum := by
    calc
      Cardinal.mk F ≤ Cardinal.mk (Set ℕ) := Cardinal.mk_subtype_le _
      _ = continuum := by rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  obtain ⟨S, _, hS⟩ := splittingNumber_spec.1
  obtain ⟨R, _, hR⟩ := reapingNumber_spec.1
  exact ⟨hS ▸ hupper S, hR ▸ hupper R⟩

theorem small_family_has_splitter (F : Set (Set ℕ))
    (hi : ∀ X ∈ F, X.Infinite) (hc : Cardinal.mk F < boundingNumber) :
    ∃ S, ∀ X ∈ F, Splits S X := by
  have hcard : Cardinal.mk (nextPoint '' F) < boundingNumber :=
    Cardinal.mk_image_le.trans_lt hc
  obtain ⟨g, hg⟩ := BoundingAndDominating.boundingNumber_spec.2.2 _ hcard
  refine ⟨alternatingIntervals g, ?_⟩
  intro X hXF
  exact bound_splits g X (hi X hXF) (hg (nextPoint X) ⟨X, hXF, rfl⟩)

theorem small_family_has_unsplit_set (F : Set (Set ℕ))
    (hc : Cardinal.mk F < pseudointersectionNumber) :
    ∃ P, P.Infinite ∧ ∀ S ∈ F, ¬ Splits S P := by
  classical
  let U := Filter.hyperfilter ℕ
  have hU : ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ) :=
    (FiltersAndUltrafilters.nonprincipal_iff_cofinite U).mpr Filter.hyperfilter_le_cofinite
  have hmem (A : Set ℕ) (hA : A ∈ (U : Filter ℕ)) : A.Infinite := by
    intro hfin
    obtain ⟨x, _, hx⟩ := U.eq_pure_of_finite_mem hfin hA
    exact hU ((FiltersAndUltrafilters.principal_ultrafilter_iff U).mpr ⟨x, hx⟩)
  let side (A : Set ℕ) : Set ℕ := if A ∈ U then A else Aᶜ
  have hsidemem (A : Set ℕ) : side A ∈ (U : Filter ℕ) := by
    by_cases hA : A ∈ U
    · simp [side, hA]
    · simpa [side, hA] using (U.mem_or_compl_mem A).resolve_left hA
  have hstrong : HasStrongFiniteIntersectionProperty (side '' F) := by
    intro E hEF hE
    apply hmem
    apply (Filter.sInter_mem hE).mpr
    intro A hAE
    obtain ⟨B, _, rfl⟩ := hEF hAE
    exact hsidemem B
  have hcard : Cardinal.mk (side '' F) < pseudointersectionNumber :=
    Cardinal.mk_image_le.trans_lt hc
  obtain ⟨P, hP⟩ := SmallFamilies.pseudointersectionNumber_spec.2.2 _ hcard hstrong
  refine ⟨P, hP.1, ?_⟩
  intro S hSF
  have hside := hP.2 (side S) ⟨S, hSF, rfl⟩
  apply (not_splits_iff S P).mpr
  by_cases hS : S ∈ U
  · exact Or.inl (by simpa [side, hS] using hside)
  · exact Or.inr (by simpa [side, hS] using hside)

theorem countable_families :
    (∀ F : Set (Set ℕ), F.Countable → (∀ X ∈ F, X.Infinite) →
      ∃ S, ∀ X ∈ F, Splits S X) ∧
    (∀ F : Set (Set ℕ), F.Countable → ∃ P, P.Infinite ∧ ∀ S ∈ F, ¬ Splits S P) := by
  constructor
  · intro F hF hi
    apply small_family_has_splitter F hi
    exact hF.le_aleph0.trans_lt
      (Cardinal.aleph0_lt_aleph_one.trans_le BoundingAndDominating.aleph_one_le_boundingNumber)
  · intro F hF
    apply small_family_has_unsplit_set F
    exact hF.le_aleph0.trans_lt (Cardinal.aleph0_lt_aleph_one.trans_le SmallFamilies.bounds.1.1)

theorem dominating_gives_splitting (D : Set (ℕ → ℕ)) (hD : IsDominating D) :
    IsSplittingFamily (alternatingIntervals '' D) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact (interval_properties g).2.2.2.1
  · intro X hX
    obtain ⟨g, hgD, hbound⟩ := hD (nextPoint X)
    exact ⟨alternatingIntervals g, ⟨g, hgD, rfl⟩, bound_splits g X hX hbound⟩

theorem splittingNumber_le_dominatingNumber : splittingNumber ≤ dominatingNumber := by
  obtain ⟨D, hD, hcard⟩ := BoundingAndDominating.dominatingNumber_spec.1
  rw [← hcard]
  exact (splittingNumber_spec.2 _ (dominating_gives_splitting D hD)).trans
    Cardinal.mk_image_le

theorem boundingNumber_le_reapingNumber : boundingNumber ≤ reapingNumber := by
  obtain ⟨F, hF, hcard⟩ := reapingNumber_spec.1
  rw [← hcard]
  by_contra h
  obtain ⟨S, hS⟩ := small_family_has_splitter F hF.1 (lt_of_not_ge h)
  obtain ⟨X, hXF, hnot⟩ := hF.2 S
  exact hnot (hS X hXF)

theorem pseudointersectionNumber_le_splittingNumber :
    pseudointersectionNumber ≤ splittingNumber := by
  obtain ⟨F, hF, hcard⟩ := splittingNumber_spec.1
  rw [← hcard]
  by_contra h
  obtain ⟨P, hP, hunsplit⟩ := small_family_has_unsplit_set F (lt_of_not_ge h)
  obtain ⟨S, hSF, hsplit⟩ := hF.2 P hP
  exact hunsplit S hSF hsplit

theorem free_base_is_reaping (B : Set (Set ℕ)) (hB : IsFreeUltrafilterBase B) :
    IsReapingFamily B := by
  obtain ⟨U, hU, hb⟩ := hB
  have hmem (A : Set ℕ) (hA : A ∈ (U : Filter ℕ)) : A.Infinite := by
    intro hfin
    obtain ⟨x, _, hx⟩ := U.eq_pure_of_finite_mem hfin hA
    exact hU ((FiltersAndUltrafilters.principal_ultrafilter_iff U).mpr ⟨x, hx⟩)
  refine ⟨?_, ?_⟩
  · intro X hXB
    exact hmem X (hb.mem_iff.mpr ⟨X, hXB, Subset.rfl⟩)
  · intro S
    rcases U.mem_or_compl_mem S with hS | hS
    · obtain ⟨X, hXB, hXS⟩ := hb.mem_iff.mp hS
      refine ⟨X, hXB, (not_splits_iff S X).mpr (Or.inl ?_)⟩
      exact Filter.Eventually.of_forall fun _ hx => hXS hx
    · obtain ⟨X, hXB, hXS⟩ := hb.mem_iff.mp hS
      refine ⟨X, hXB, (not_splits_iff S X).mpr (Or.inr ?_)⟩
      exact Filter.Eventually.of_forall fun _ hx => hXS hx

theorem reapingNumber_le_ultrafilterNumber : reapingNumber ≤ ultrafilterNumber := by
  obtain ⟨B, hB, hcard⟩ := SmallFamilies.ultrafilterNumber_spec.1
  rw [← hcard]
  exact reapingNumber_spec.2 B (free_base_is_reaping B hB)

theorem singleton_not_reaping (X : Set ℕ) (hX : X.Infinite) : ¬ IsReapingFamily {X} := by
  intro h
  obtain ⟨S, _, hsplit⟩ := every_infinite_set_has_splitter X hX
  obtain ⟨Y, hY, hnot⟩ := h.2 S
  have hYX : Y = X := Set.mem_singleton_iff.mp hY
  exact hnot (hYX ▸ hsplit)

theorem numbers_of_continuum_hypothesis (hCH : (continuum : Cardinal.{0}) = ℵ₁) :
    splittingNumber = ℵ₁ ∧ reapingNumber = ℵ₁ := by
  have hslo : ℵ₁ ≤ splittingNumber :=
    SmallFamilies.bounds.1.1.trans pseudointersectionNumber_le_splittingNumber
  have hrlo : ℵ₁ ≤ reapingNumber :=
    BoundingAndDominating.aleph_one_le_boundingNumber.trans boundingNumber_le_reapingNumber
  have hshi : splittingNumber ≤ ℵ₁ := by simpa [hCH] using number_upper_bounds.1
  have hrhi : reapingNumber ≤ ℵ₁ := by simpa [hCH] using number_upper_bounds.2
  exact ⟨le_antisymm hshi hslo, le_antisymm hrhi hrlo⟩

end Lemmatheca.SetTheory.SplittingReaping
