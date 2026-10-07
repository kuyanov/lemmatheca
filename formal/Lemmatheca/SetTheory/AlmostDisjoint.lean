import Lemmatheca.SetTheory.FiniteErrors
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Order.Zorn
import Mathlib.Order.Interval.Set.Nat

/-! Almost disjoint families of infinite subsets of the naturals.

Binary digits are `Bool`, with `false` representing 0 and `true` representing 1.
Families are sets of sets, so repetition is impossible. Cardinalities of families
are cardinalities of their membership subtypes. Finite maximal families are allowed.
-/

namespace Lemmatheca.SetTheory.AlmostDisjoint

open Set Filter Cardinal
universe u

def AreAlmostDisjoint (A B : Set ℕ) : Prop :=
  A.Infinite ∧ B.Infinite ∧ (A ∩ B).Finite

def IsAlmostDisjoint (A : Set (Set ℕ)) : Prop :=
  (∀ S ∈ A, S.Infinite) ∧ A.Pairwise (fun S T => (S ∩ T).Finite)

def binaryPrefix (x : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => x i)

def prefixCodes (x : ℕ → Bool) : Set ℕ :=
  Set.range (fun n => binaryWordCode (binaryPrefix x n))

def binaryPrefixFamily : Set (Set ℕ) := Set.range prefixCodes

private theorem prefix_code_injective (x : ℕ → Bool) :
    Function.Injective (fun n => binaryWordCode (binaryPrefix x n)) := by
  intro n m h
  have := congrArg List.length (binaryWordCode_spec.1 h)
  simpa [binaryPrefix] using this

private theorem prefix_eq_iff (x y : ℕ → Bool) (n : ℕ) :
    binaryPrefix x n = binaryPrefix y n ↔ ∀ i < n, x i = y i := by
  rw [binaryPrefix, binaryPrefix, List.ofFn_inj]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.isLt

theorem prefixCodes_infinite (x : ℕ → Bool) : (prefixCodes x).Infinite := by
  exact infinite_range_of_injective (prefix_code_injective x)

theorem one_mem_prefixCodes (x : ℕ → Bool) : 1 ∈ prefixCodes x := by
  exact ⟨0, by simp [binaryPrefix, binaryWordCode]⟩

theorem prefixCodes_intersection (x y : ℕ → Bool) (k : ℕ)
    (hpre : ∀ i < k, x i = y i) (hne : x k ≠ y k) :
    prefixCodes x ∩ prefixCodes y =
      (fun n => binaryWordCode (binaryPrefix x n)) '' Set.Iic k ∧
    (prefixCodes x ∩ prefixCodes y).ncard = k + 1 := by
  have he : prefixCodes x ∩ prefixCodes y =
      (fun n => binaryWordCode (binaryPrefix x n)) '' Iic k := by
    ext v
    constructor
    · rintro ⟨⟨n, rfl⟩, m, hm⟩
      have hw := binaryWordCode_spec.1 hm
      have hl : m = n := by simpa [binaryPrefix] using congrArg List.length hw
      subst m
      have hp := (prefix_eq_iff y x n).mp hw
      have hn : n ≤ k := by
        by_contra hn
        exact hne (hp k (by omega)).symm
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, n, ?_⟩
      exact congrArg binaryWordCode
        (((prefix_eq_iff x y n).mpr fun i hi => hpre i (lt_of_lt_of_le hi hn)).symm)
  refine ⟨he, ?_⟩
  rw [he, ncard_image_of_injective _ (prefix_code_injective x), ncard_Iic_nat]

theorem prefixCodes_injective : Function.Injective prefixCodes := by
  intro x y h
  funext k
  have hm : binaryWordCode (binaryPrefix x (k + 1)) ∈ prefixCodes y :=
    h ▸ mem_range_self (k + 1)
  obtain ⟨m, hm⟩ := hm
  have hw := binaryWordCode_spec.1 hm
  have hl : m = k + 1 := by simpa [binaryPrefix] using congrArg List.length hw
  subst m
  exact ((prefix_eq_iff y x (k + 1)).mp hw k (by omega)).symm

theorem binaryPrefixFamily_almost_disjoint : IsAlmostDisjoint binaryPrefixFamily := by
  refine ⟨?_, ?_⟩
  · rintro S ⟨x, rfl⟩
    exact prefixCodes_infinite x
  · rintro S ⟨x, rfl⟩ T ⟨y, rfl⟩ hne
    have hn : ∃ k, x k ≠ y k := by
      by_contra h
      push Not at h
      exact hne (congrArg prefixCodes (funext h))
    let k := Nat.find hn
    have hp : ∀ i < k, x i = y i := fun i hi => not_not.mp (Nat.find_min hn hi)
    rw [(prefixCodes_intersection x y k hp (Nat.find_spec hn)).1]
    exact (finite_Iic k).image _

theorem binaryPrefixFamily_cardinality :
    Cardinal.mk binaryPrefixFamily = Cardinal.continuum := by
  rw [binaryPrefixFamily, Cardinal.mk_range_eq _ prefixCodes_injective,
    Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.lift_aleph0, Cardinal.two_power_aleph0]

def IsMaximalAlmostDisjoint (A : Set (Set ℕ)) : Prop :=
  IsAlmostDisjoint A ∧ ∀ M, IsAlmostDisjoint M → A ⊆ M → M = A

private theorem insert_almost_disjoint {A : Set (Set ℕ)} {B : Set ℕ}
    (hA : IsAlmostDisjoint A) (hB : B.Infinite)
    (hi : ∀ S ∈ A, (S ∩ B).Finite) : IsAlmostDisjoint (insert B A) := by
  constructor
  · intro S hS
    rcases hS with rfl | hS
    · exact hB
    · exact hA.1 S hS
  · intro S hS T hT hne
    rcases hS with rfl | hS <;> rcases hT with rfl | hT
    · exact (hne rfl).elim
    · simpa [inter_comm] using hi T hT
    · exact hi S hS
    · exact hA.2 hS hT hne

theorem maximal_iff_infinite_intersection (A : Set (Set ℕ)) (hA : IsAlmostDisjoint A) :
    IsMaximalAlmostDisjoint A ↔
      ∀ B : Set ℕ, B.Infinite → ∃ S ∈ A, (S ∩ B).Infinite := by
  classical
  constructor
  · intro h B hB
    by_contra hn
    have hi : ∀ S ∈ A, (S ∩ B).Finite := by
      intro S hS
      by_contra h
      exact hn ⟨S, hS, h⟩
    have he := h.2 (insert B A) (insert_almost_disjoint hA hB hi) (subset_insert _ _)
    have hBA : B ∈ A := he ▸ mem_insert B A
    exact hB (by simpa using hi B hBA)
  · intro h
    refine ⟨hA, ?_⟩
    intro M hM hAM
    apply Subset.antisymm _ hAM
    intro B hBM
    by_contra hn
    obtain ⟨S, hSA, hSB⟩ := h B (hM.1 B hBM)
    exact hSB (hM.2 (hAM hSA) hBM (by rintro rfl; exact hn hSA))

theorem maximal_finite_partition {ι : Type u} [Finite ι] (A : ι → Set ℕ)
    (hinf : ∀ i, (A i).Infinite) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hc : (⋃ i, A i) = Set.univ) :
    IsMaximalAlmostDisjoint (Set.range A) := by
  classical
  have ha : IsAlmostDisjoint (range A) := by
    constructor
    · rintro S ⟨i, rfl⟩; exact hinf i
    · rintro S ⟨i, rfl⟩ T ⟨j, rfl⟩ hn
      have hij : i ≠ j := fun h => hn (congrArg A h)
      rw [Set.disjoint_iff_inter_eq_empty.mp (hd hij)]
      exact finite_empty
  apply (maximal_iff_infinite_intersection _ ha).mpr
  intro B hB
  by_contra hn
  have hf : ∀ i, (A i ∩ B).Finite := by
    intro i
    by_contra h
    exact hn ⟨A i, mem_range_self i, h⟩
  have he : (⋃ i, A i ∩ B) = B := by
    rw [← iUnion_inter, hc, univ_inter]
  exact hB (he ▸ finite_iUnion hf)

theorem countable_infinite_extension (A : Set (Set ℕ)) (hA : IsAlmostDisjoint A)
    (hc : A.Countable) (hi : A.Infinite) :
    ∃ B : Set ℕ, B.Infinite ∧ B ∉ A ∧
      (∀ S ∈ A, (S ∩ B).Finite) ∧ IsAlmostDisjoint (insert B A) := by
  classical
  let C := Set.compl '' A
  have hs : FiniteErrors.HasStrongFiniteIntersectionProperty C := by
    intro E hEC hE
    let F := Set.compl '' E
    have hF : F.Finite := hE.image _
    have hFA : F ⊆ A := by
      rintro S ⟨T, hTE, rfl⟩
      obtain ⟨S, hSA, rfl⟩ := hEC hTE
      change Sᶜᶜ ∈ A
      simpa only [compl_compl] using hSA
    obtain ⟨T, hTA, hTF⟩ := (hi.sdiff hF).nonempty
    have hf : (⋃ S ∈ F, T ∩ S).Finite := hF.biUnion fun S hS =>
      hA.2 hTA (hFA hS) (fun he => hTF (he ▸ hS))
    apply ((hA.1 T hTA).sdiff hf).mono
    intro n hn
    simp only [mem_sInter]
    intro S hSE
    by_contra hns
    apply hn.2
    exact mem_iUnion.mpr ⟨Sᶜ, mem_iUnion.mpr
      ⟨mem_image_of_mem Set.compl hSE, ⟨hn.1, hns⟩⟩⟩
  obtain ⟨B, hB⟩ := FiniteErrors.countable_pseudointersection C (hc.image _) hs
  have hbS : ∀ S ∈ A, (S ∩ B).Finite := by
    intro S hS
    have := (FiniteErrors.almostSubset_iff_finite_sdiff B Sᶜ).mp
      (hB.2 Sᶜ (mem_image_of_mem Set.compl hS))
    simpa [Set.sdiff_compl, inter_comm] using this
  have hnot : B ∉ A := by
    intro h
    exact hB.1 (by simpa using hbS B h)
  exact ⟨B, hB.1, hnot, hbS, insert_almost_disjoint hA hB.1 hbS⟩

theorem maximal_extension (A : Set (Set ℕ)) (hA : IsAlmostDisjoint A) :
    ∃ M, A ⊆ M ∧ IsMaximalAlmostDisjoint M := by
  classical
  have hchains : ∀ c ⊆ {M : Set (Set ℕ) | IsAlmostDisjoint M},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {M : Set (Set ℕ) | IsAlmostDisjoint M}, ∀ S ∈ c, S ⊆ ub := by
    intro c hc hchain hne
    refine ⟨⋃₀ c, ?_, fun S hS => subset_sUnion_of_mem hS⟩
    constructor
    · rintro S ⟨M, hMc, hSM⟩
      exact (hc hMc).1 S hSM
    · rintro S ⟨M, hMc, hSM⟩ T ⟨N, hNc, hTN⟩ hST
      rcases hchain.total hMc hNc with hMN | hNM
      · exact (hc hNc).2 (hMN hSM) hTN hST
      · exact (hc hMc).2 hSM (hNM hTN) hST
  obtain ⟨M, hAM, hm⟩ := zorn_subset_nonempty
    {M : Set (Set ℕ) | IsAlmostDisjoint M} hchains A hA
  exact ⟨M, hAM, hm.1, fun N hN hMN => Subset.antisymm (hm.2 hN hMN) hMN⟩

theorem continuum_maximal_family :
    ∃ M : Set (Set ℕ), IsMaximalAlmostDisjoint M ∧
      Cardinal.mk M = Cardinal.continuum := by
  obtain ⟨M, hAM, hM⟩ := maximal_extension binaryPrefixFamily binaryPrefixFamily_almost_disjoint
  refine ⟨M, hM, le_antisymm ?_ ?_⟩
  · calc
      Cardinal.mk M ≤ Cardinal.mk (Set ℕ) := Cardinal.mk_subtype_le _
      _ = Cardinal.continuum := by rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  · rw [← binaryPrefixFamily_cardinality]
    exact Cardinal.mk_le_mk_of_subset hAM

theorem no_greatest_family :
    ¬ ∃ G : Set (Set ℕ), IsAlmostDisjoint G ∧
      ∀ A, IsAlmostDisjoint A → A ⊆ G := by
  rintro ⟨G, hG, hg⟩
  have hone (S : Set ℕ) (hS : S.Infinite) : IsAlmostDisjoint {S} := by
    constructor
    · intro T hT; simpa only [mem_singleton_iff.mp hT] using hS
    · intro T hT V hV hn
      exact (hn ((mem_singleton_iff.mp hT).trans (mem_singleton_iff.mp hV).symm)).elim
  have hu : Set.univ ∈ G := hg {Set.univ} (hone Set.univ infinite_univ) (mem_singleton _)
  have hi : (Ici 1 : Set ℕ).Infinite := by
    apply infinite_of_injective_forall_mem (f := fun n : ℕ => n + 1)
    · intro m n h; dsimp at h; omega
    · intro n; simp
  have hv : Ici 1 ∈ G := hg {Ici 1} (hone _ hi) (mem_singleton _)
  have hn : (Set.univ : Set ℕ) ≠ Ici 1 := by
    intro h
    have : 0 ∈ (Ici 1 : Set ℕ) := h ▸ mem_univ 0
    simp at this
  exact hi (by simpa using hG.2 hu hv hn)

end Lemmatheca.SetTheory.AlmostDisjoint
