import Lemmatheca.ExactPairsAndFailureOfMeets.Construction

/-! Exactness and absence of meets in the native degree order. -/
namespace Lemmatheca.ComputabilityTheory.ExactPairs
noncomputable section

def ExactPair (a : ℕ → TuringDegrees.Degree) (b c : TuringDegrees.Degree) : Prop :=
  ∀ d, d ≤ b ∧ d ≤ c ↔ ∃ n, d ≤ a n

theorem constructed_degree_exact_pair (A : ℕ → Set ℕ)
    (h : ∀ n, TuringDegrees.Reducible (A n) (A (n + 1))) :
    ExactPair (fun n => TuringDegrees.degree (A n))
      (TuringDegrees.degree (leftSet A)) (TuringDegrees.degree (rightSet A)) := by
  intro d
  obtain ⟨D, rfl⟩ := TuringDegrees.degree_surjective d
  exact constructed_exact_pair A h D

theorem exact_pair_exists (a : ℕ → TuringDegrees.Degree) (h : ∀ n, a n ≤ a (n + 1)) :
    ∃ b c, ExactPair a b c := by
  classical
  let A : ℕ → Set ℕ := fun n => Classical.choose (TuringDegrees.degree_surjective (a n))
  have hA (n) : TuringDegrees.degree (A n) = a n :=
    Classical.choose_spec (TuringDegrees.degree_surjective (a n))
  have hred (n) : TuringDegrees.Reducible (A n) (A (n + 1)) := by
    change TuringDegrees.degree (A n) ≤ TuringDegrees.degree (A (n + 1))
    simpa only [hA] using h n
  refine ⟨TuringDegrees.degree (leftSet A), TuringDegrees.degree (rightSet A), ?_⟩
  have hx := constructed_degree_exact_pair A hred
  have heq : (fun n => TuringDegrees.degree (A n)) = a := funext hA
  rwa [heq] at hx

theorem exact_pair_no_glb (a : ℕ → TuringDegrees.Degree)
    (h : ∀ n, a n < a (n + 1)) (b c : TuringDegrees.Degree) (hexact : ExactPair a b c) :
    ¬ ∃ d, IsGLB ({b, c} : Set TuringDegrees.Degree) d := by
  rintro ⟨d, hd⟩
  obtain ⟨n, hn⟩ := (hexact d).mp ⟨hd.1 (by simp), hd.1 (by simp)⟩
  have hs := (hexact (a (n + 1))).mpr ⟨n + 1, le_rfl⟩
  have hsd : a (n + 1) ≤ d := hd.2 (by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hs.1
    · exact (Set.mem_singleton_iff.mp hx) ▸ hs.2)
  exact (not_le_of_gt (h n)) (hsd.trans hn)

theorem no_glb_incomparable (b c : TuringDegrees.Degree)
    (h : ¬ ∃ d, IsGLB ({b, c} : Set TuringDegrees.Degree) d) :
    ¬ b ≤ c ∧ ¬ c ≤ b := by
  constructor
  · intro hbc
    apply h
    refine ⟨b, ?_, ?_⟩
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact le_rfl
      · exact (Set.mem_singleton_iff.mp hx) ▸ hbc
    · intro d hd
      exact hd (by simp)
  · intro hcb
    apply h
    refine ⟨c, ?_, ?_⟩
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hcb
      · exact (Set.mem_singleton_iff.mp hx) ▸ le_rfl
    · intro d hd
      exact hd (by simp)

theorem constant_chain_glb (a b c : TuringDegrees.Degree)
    (h : ExactPair (fun _ => a) b c) : IsGLB ({b, c} : Set TuringDegrees.Degree) a := by
  have ha := (h a).mpr ⟨0, le_rfl⟩
  constructor
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ha.1
    · exact (Set.mem_singleton_iff.mp hx) ▸ ha.2
  · intro d hd
    obtain ⟨n, hn⟩ := (h d).mp ⟨hd (by simp), hd (by simp)⟩
    exact hn

theorem minimal_pair_zero_exact (b c : TuringDegrees.Degree) :
    OrdinaryMinimalPairs.MinimalPair b c ↔
      b ≠ TuringDegrees.zeroDegree ∧ c ≠ TuringDegrees.zeroDegree ∧
        ExactPair (fun _ => TuringDegrees.zeroDegree) b c := by
  constructor
  · rintro ⟨hb, hc, h⟩
    refine ⟨hb, hc, fun d => ⟨?_, ?_⟩⟩
    · rintro ⟨hdb, hdc⟩
      exact ⟨0, le_of_eq (h d hdb hdc)⟩
    · rintro ⟨n, hn⟩
      exact ⟨hn.trans (TuringDegrees.zeroDegree_le b),
        hn.trans (TuringDegrees.zeroDegree_le c)⟩
  · rintro ⟨hb, hc, h⟩
    refine ⟨hb, hc, fun d hdb hdc => ?_⟩
    obtain ⟨n, hn⟩ := (h d).mp ⟨hdb, hdc⟩
    exact le_antisymm hn (TuringDegrees.zeroDegree_le d)
end
end Lemmatheca.ComputabilityTheory.ExactPairs
