import Lemmatheca.EffectiveOperators.Characterization

/-! Increasing unions of the same unary partial functions used by effective operators. -/
namespace Lemmatheca.ComputabilityTheory.LeastFixedPointRecursion
open UniversalComputation RiceShapiroTheorem EffectiveOperators
open RicesTheorem (PartialFunction)
noncomputable section
open Classical

def Increasing (F : ℕ → PartialFunction) : Prop :=
  ∀ n, GraphInclusion (F n) (F (n + 1))

def chainUnion (F : ℕ → PartialFunction) (x : ℕ) : Part ℕ :=
  ⟨∃ y, ∃ n, y ∈ F n x, fun h => Classical.choose h⟩

theorem increasing_le (F : ℕ → PartialFunction) (hF : Increasing F)
    (m n : ℕ) (hmn : m ≤ n) : GraphInclusion (F m) (F n) := by
  induction hmn with
  | refl => exact fun _ _ h => h
  | @step n _ ih => exact fun x y hy => hF n x y (ih x y hy)

theorem chain_union_mem (F : ℕ → PartialFunction) (hF : Increasing F) (x y : ℕ) :
    y ∈ chainUnion F x ↔ ∃ n, y ∈ F n x := by
  constructor
  · rintro ⟨hd, he⟩
    obtain ⟨n, hn⟩ := Classical.choose_spec hd
    exact ⟨n, he ▸ hn⟩
  · rintro ⟨n, hn⟩
    have hd : ∃ y, ∃ n, y ∈ F n x := ⟨y, n, hn⟩
    refine ⟨hd, ?_⟩
    change Classical.choose hd = y
    obtain ⟨m, hm⟩ := Classical.choose_spec hd
    exact Part.mem_unique
      (increasing_le F hF m (max m n) (le_max_left _ _) x _ hm)
      (increasing_le F hF n (max m n) (le_max_right _ _) x y hn)

theorem chain_union_unique (F : ℕ → PartialFunction) (hF : Increasing F)
    (h : PartialFunction) (hh : ∀ x y, y ∈ h x ↔ ∃ n, y ∈ F n x) :
    h = chainUnion F := by
  funext x
  apply Part.ext
  intro y
  exact (hh x y).trans (chain_union_mem F hF x y).symm

theorem stage_below_union (F : ℕ → PartialFunction) (hF : Increasing F) (n : ℕ) :
    GraphInclusion (F n) (chainUnion F) := by
  intro x y hy
  exact (chain_union_mem F hF x y).mpr ⟨n, hy⟩

theorem union_below (F : ℕ → PartialFunction) (hF : Increasing F)
    (g : PartialFunction) (hg : ∀ n, GraphInclusion (F n) g) :
    GraphInclusion (chainUnion F) g := by
  intro x y hy
  obtain ⟨n, hn⟩ := (chain_union_mem F hF x y).mp hy
  exact hg n x y hn

private theorem finite_capture_bound (F : ℕ → PartialFunction) (hF : Increasing F)
    (D : PairList) (hD : ∀ p ∈ D, ∃ n, p.2 ∈ F n p.1) :
    ∃ N, ∀ p ∈ D, p.2 ∈ F N p.1 := by
  induction D with
  | nil => exact ⟨0, by simp⟩
  | cons p D ih =>
    obtain ⟨n, hn⟩ := hD p (by simp)
    obtain ⟨m, hm⟩ := ih (fun q hq => hD q (List.mem_cons_of_mem p hq))
    refine ⟨max n m, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact increasing_le F hF n (max n m) (le_max_left _ _) q.1 q.2 hn
    · exact increasing_le F hF m (max n m) (le_max_right _ _) q.1 q.2 (hm q hq)

theorem finite_fragment_capture (F : ℕ → PartialFunction) (hF : Increasing F)
    (d : ℕ) (hd : Valid d) :
    GraphInclusion (fragment d) (chainUnion F) ↔ ∃ n, GraphInclusion (fragment d) (F n) := by
  constructor
  · intro h
    have hD : ∀ p ∈ pairList d, ∃ n, p.2 ∈ F n p.1 := by
      intro p hp
      exact (chain_union_mem F hF p.1 p.2).mp
        (h p.1 p.2 ((tableFunction_mem _ hd p.1 p.2).mpr (by simpa using hp)))
    obtain ⟨N, hN⟩ := finite_capture_bound F hF (pairList d) hD
    exact ⟨N, fun x y hy => hN (x, y) ((tableFunction_mem _ hd x y).mp hy)⟩
  · rintro ⟨n, hn⟩ x y hy
    exact stage_below_union F hF n x y (hn x y hy)

theorem effective_image_increasing (Φ : PartialFunction → PartialFunction)
    (hΦ : IsEffective Φ) (F : ℕ → PartialFunction) (hF : Increasing F) :
    Increasing (fun n => Φ (F n)) := by
  intro n
  exact effective_monotone Φ hΦ (F n) (F (n + 1)) (hF n)

theorem chain_continuity (Φ : PartialFunction → PartialFunction)
    (hΦ : IsEffective Φ) (F : ℕ → PartialFunction) (hF : Increasing F) :
    Φ (chainUnion F) = chainUnion (fun n => Φ (F n)) := by
  obtain ⟨R, hp, hc, hce, rfl⟩ := hΦ
  have hI : Increasing (fun n => operator R (F n)) :=
    fun n => operator_monotone R hp hc (F n) (F (n + 1)) (hF n)
  funext x
  apply Part.ext
  intro y
  rw [operator_mem R hp hc, chain_union_mem _ hI]
  constructor
  · rintro ⟨d, hd, hr⟩
    obtain ⟨n, hn⟩ := (finite_fragment_capture F hF d (hp d x y hr)).mp hd
    exact ⟨n, (operator_mem R hp hc (F n) x y).mpr ⟨d, hn, hr⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨d, hd, hr⟩ := (operator_mem R hp hc (F n) x y).mp hn
    exact ⟨d, fun z v hv => stage_below_union F hF n z v (hd z v hv), hr⟩

end
end Lemmatheca.ComputabilityTheory.LeastFixedPointRecursion
