import Lemmatheca.SetTheory.Countability
import Lemmatheca.SetTheory.FiltersAndUltrafilters
import Mathlib.Order.Filter.AtTopBot.Basic

/-! Finite exceptions and explicit countable diagonal constructions.

Almost containment and equality use mathlib's eventual set relations at `cofinite`.
Function domination uses `atTop`, which agrees with `cofinite` on the naturals.
These results do not encode first-order ZF or certify the human arguments' axiom
strength.
-/

namespace Lemmatheca.SetTheory.FiniteErrors

open Set Filter
universe u

theorem almostSubset_iff_finite_sdiff {α : Type u} (A B : Set α) :
    A ≤ᶠ[cofinite] B ↔ (A \ B).Finite := by
  classical
  change {x | x ∈ A → x ∈ B} ∈ cofinite ↔ _
  rw [mem_cofinite]
  have he : {x | x ∈ A → x ∈ B}ᶜ = A \ B := by ext x; simp
  rw [he]

theorem almostEq_iff_finite_symmDiff {α : Type u} (A B : Set α) :
    A =ᶠ[cofinite] B ↔ ((A \ B) ∪ (B \ A)).Finite := by
  classical
  rw [Filter.eventuallySubset_antisymm_iff,
    almostSubset_iff_finite_sdiff, almostSubset_iff_finite_sdiff, Set.finite_union]

def HasStrongFiniteIntersectionProperty (A : Set (Set ℕ)) : Prop :=
  ∀ E : Set (Set ℕ), E ⊆ A → E.Finite → (⋂₀ E).Infinite

def IsPseudointersection (A : Set (Set ℕ)) (B : Set ℕ) : Prop :=
  B.Infinite ∧ ∀ S ∈ A, B ≤ᶠ[cofinite] S

theorem IsPseudointersection.strongFiniteIntersections {A : Set (Set ℕ)} {B : Set ℕ}
    (hB : IsPseudointersection A B) : HasStrongFiniteIntersectionProperty A := by
  classical
  intro E hEA hE
  have hd : (⋃ S ∈ E, B \ S).Finite := hE.biUnion fun S hS =>
    (almostSubset_iff_finite_sdiff B S).mp (hB.2 S (hEA hS))
  apply (hB.1.sdiff hd).mono
  intro x hx
  simp only [Set.mem_sdiff, mem_iUnion, not_exists, not_and] at hx
  simp only [mem_sInter]
  intro S hS
  by_contra hn
  exact hx.2 S hS hx.1 hn

theorem pseudointersection_empty_iff (B : Set ℕ) :
    IsPseudointersection ∅ B ↔ B.Infinite := by
  simp [IsPseudointersection]

/-- The least admissible point; on inadmissible input the natural infimum is zero.
The specification imposes the strong finite intersection hypothesis. -/
noncomputable def diagonalPoint (A : ℕ → Set ℕ) : ℕ → ℕ
  | 0 => sInf (A 0)
  | n + 1 => sInf {m | diagonalPoint A n < m ∧ ∀ i ≤ n + 1, m ∈ A i}

theorem diagonalPoint_spec (A : ℕ → Set ℕ)
    (hA : HasStrongFiniteIntersectionProperty (Set.range A)) :
    StrictMono (diagonalPoint A) ∧
    (∀ n i, i ≤ n → diagonalPoint A n ∈ A i) ∧
    (∀ n, diagonalPoint A (n + 1) =
      sInf {m | diagonalPoint A n < m ∧ ∀ i ≤ n + 1, m ∈ A i}) ∧
    (∀ i, Set.range (diagonalPoint A) \ A i ⊆
      (diagonalPoint A) '' Set.Iio i) ∧
    IsPseudointersection (Set.range A) (Set.range (diagonalPoint A)) := by
  classical
  have hinf (n : ℕ) : {m | ∀ i ≤ n, m ∈ A i}.Infinite := by
    have he := hA (A '' Iic n) (image_subset_range _ _) ((finite_Iic n).image A)
    convert he using 1
    ext m
    simp
  have hnext (n : ℕ) : {m | diagonalPoint A n < m ∧ ∀ i ≤ n + 1, m ∈ A i}.Nonempty := by
    obtain ⟨m, hm, hgt⟩ := (hinf (n + 1)).exists_gt (diagonalPoint A n)
    exact ⟨m, hgt, hm⟩
  have hstep (n : ℕ) : diagonalPoint A n < diagonalPoint A (n + 1) :=
    (Nat.sInf_mem (hnext n)).1
  have hmem : ∀ n i, i ≤ n → diagonalPoint A n ∈ A i := by
    intro n
    cases n with
    | zero =>
      intro i hi
      have hzero : (A 0).Infinite := by simpa using hinf 0
      have hm := Nat.sInf_mem hzero.nonempty
      simpa [diagonalPoint, Nat.eq_zero_of_le_zero hi] using hm
    | succ n => exact (Nat.sInf_mem (hnext n)).2
  have hmono := strictMono_nat_of_lt_succ hstep
  have hex (i : ℕ) : range (diagonalPoint A) \ A i ⊆ diagonalPoint A '' Iio i := by
    rintro x ⟨⟨n, rfl⟩, hn⟩
    exact ⟨n, show n < i from lt_of_not_ge (fun h => hn (hmem n i h)), rfl⟩
  refine ⟨hmono, hmem, fun _ => rfl, hex, ?_⟩
  refine ⟨infinite_range_of_injective hmono.injective, ?_⟩
  rintro S ⟨i, rfl⟩
  exact (almostSubset_iff_finite_sdiff _ _).mpr
    (((finite_Iio i).image _).subset (hex i))

theorem countable_pseudointersection (A : Set (Set ℕ)) (hc : A.Countable)
    (hA : HasStrongFiniteIntersectionProperty A) :
    ∃ B, IsPseudointersection A B := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨univ, (pseudointersection_empty_iff _).mpr infinite_univ⟩
  · obtain ⟨a, ha⟩ := hc.exists_eq_range hne
    exact ⟨range (diagonalPoint a), ha ▸ (diagonalPoint_spec a (ha ▸ hA)).2.2.2.2⟩

def EventuallyLT (f g : ℕ → ℕ) : Prop :=
  ∀ᶠ n in atTop, f n < g n

def diagonalBound (f : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (fun i => f i n) + 1

theorem diagonalBound_spec (f : ℕ → ℕ → ℕ) :
    (∀ i n, i ≤ n → f i n < diagonalBound f n) ∧
    ∀ i, EventuallyLT (f i) (diagonalBound f) := by
  have h (i n : ℕ) (hi : i ≤ n) : f i n < diagonalBound f n := by
    have := Finset.le_sup (s := Finset.range (n + 1)) (f := fun i => f i n)
      (show i ∈ Finset.range (n + 1) by simpa using hi)
    dsimp [diagonalBound]
    omega
  exact ⟨h, fun i => eventually_atTop.mpr ⟨i, fun n hn => h i n hn⟩⟩

theorem countable_eventual_bound (F : Set (ℕ → ℕ)) (hF : F.Countable) :
    ∃ g : ℕ → ℕ, (F = ∅ → g = fun _ => 0) ∧
      ∀ f ∈ F, EventuallyLT f g := by
  classical
  rcases F.eq_empty_or_nonempty with h | h
  · exact ⟨fun _ => 0, fun _ => rfl, by simp [h]⟩
  · obtain ⟨f, hf⟩ := hF.exists_eq_range h
    refine ⟨diagonalBound f, fun he => (h.ne_empty he).elim, ?_⟩
    rintro g hg
    obtain ⟨i, rfl⟩ := hf ▸ hg
    exact (diagonalBound_spec f).2 i

theorem successor_not_eventuallyLE (g : ℕ → ℕ) :
    ¬ (fun n => g n + 1) ≤ᶠ[atTop] g := by
  intro h
  obtain ⟨n, hn⟩ := h.exists
  exact Nat.not_succ_le_self _ hn

theorem no_countable_ultrafilter_base (U : Ultrafilter ℕ)
    (hU : ¬ FiltersAndUltrafilters.IsPrincipal (U : Filter ℕ))
    (B : Set (Set ℕ)) (hB : B.Countable) :
    ¬ (U : Filter ℕ).HasBasis (fun A => A ∈ B) id := by
  classical
  intro hb
  have hmem (S : Set ℕ) (hS : S ∈ (U : Filter ℕ)) : S.Infinite := by
    intro hfin
    obtain ⟨x, _, hx⟩ := U.eq_pure_of_finite_mem hfin hS
    exact hU ((FiltersAndUltrafilters.principal_ultrafilter_iff U).mpr ⟨x, hx⟩)
  have hstrong : HasStrongFiniteIntersectionProperty B := by
    intro E hEB hE
    apply hmem
    apply (Filter.sInter_mem hE).mpr
    intro S hS
    exact hb.mem_iff.mpr ⟨S, hEB hS, Subset.rfl⟩
  obtain ⟨P, hP⟩ := countable_pseudointersection B hB hstrong
  let e := hP.1.natEmbedding P
  let f : ℕ → ℕ := fun n => (e n).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let C := range (fun n => f (2 * n))
  let D := range (fun n => f (2 * n + 1))
  have hC : C.Infinite := infinite_range_of_injective fun m n h => by
    have := hf h
    omega
  have hD : D.Infinite := infinite_range_of_injective fun m n h => by
    have := hf h
    omega
  have hCP : C ⊆ P := by rintro _ ⟨n, rfl⟩; exact (e (2 * n)).property
  have hDP : D ⊆ P := by rintro _ ⟨n, rfl⟩; exact (e (2 * n + 1)).property
  have hDC : Disjoint D C := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn⟩ ⟨m, hm⟩
    have := hf (hn.trans hm.symm)
    omega
  rcases U.mem_or_compl_mem C with hc | hc
  · obtain ⟨S, hSB, hSC⟩ := hb.mem_iff.mp hc
    have hd := (almostSubset_iff_finite_sdiff P S).mp (hP.2 S hSB)
    exact hD (hd.subset fun x hx => ⟨hDP hx, fun hs => Set.disjoint_left.mp hDC hx (hSC hs)⟩)
  · obtain ⟨S, hSB, hSC⟩ := hb.mem_iff.mp hc
    have hd := (almostSubset_iff_finite_sdiff P S).mp (hP.2 S hSB)
    exact hC (hd.subset fun x hx => ⟨hCP hx, fun hs => hSC hs hx⟩)

/-- The two residue classes modulo two form an infinite partition. -/
theorem parity_partition :
    ({n : ℕ | n % 2 = 0} : Set ℕ).Infinite ∧
    ({n : ℕ | n % 2 = 1} : Set ℕ).Infinite ∧
    ({n : ℕ | n % 2 = 0} ∩ {n : ℕ | n % 2 = 1} : Set ℕ) = ∅ ∧
    ({n : ℕ | n % 2 = 0} ∪ {n : ℕ | n % 2 = 1} : Set ℕ) = univ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    · intro m n h; dsimp at h; omega
    · intro n; simp
  · apply infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
    · intro m n h; dsimp at h; omega
    · intro n; simp
  · ext n; simp
  · ext n; simp; omega

end Lemmatheca.SetTheory.FiniteErrors
