import Lemmatheca.SetTheory.PartitionRelations

/-! Parity colourings and the five/six-point Ramsey illustration. -/

noncomputable section

namespace Lemmatheca.Entry.PartitionRelations

open Set
open Lemmatheca.SetTheory.PartitionRelations

def parityColoring : Coloring ℕ 2 (Fin 2) := by
  classical
  exact fun s => if ∀ a ∈ s.val, ∀ b ∈ s.val, a % 2 = b % 2 then 0 else 1

theorem parityColoring_spec :
    ({a : ℕ | a % 2 = 0}.Infinite ∧
      IsHomogeneousIn parityColoring {a | a % 2 = 0} 0) ∧
    ({a : ℕ | a % 2 = 1}.Infinite ∧
      IsHomogeneousIn parityColoring {a | a % 2 = 1} 0) ∧
    ∀ H : Finset ℕ, H.card = 3 →
      ¬ IsHomogeneousIn parityColoring (↑H : Set ℕ) 1 := by
  classical
  have he : ({a : ℕ | a % 2 = 0} : Set ℕ).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n)
    · intro n m h; dsimp at h; omega
    · intro n; simp
  have ho : ({a : ℕ | a % 2 = 1} : Set ℕ).Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + 1)
    · intro n m h; dsimp at h; omega
    · intro n; change (2 * n + 1) % 2 = 1; omega
  refine ⟨⟨he, ?_⟩, ⟨ho, ?_⟩, ?_⟩
  · intro s hs
    have hh : ∀ a ∈ s.val, ∀ b ∈ s.val, a % 2 = b % 2 := by
      intro a ha b hb; exact (hs ha).trans (hs hb).symm
    simp [parityColoring]
    exact hh
  · intro s hs
    have hh : ∀ a ∈ s.val, ∀ b ∈ s.val, a % 2 = b % 2 := by
      intro a ha b hb; exact (hs ha).trans (hs hb).symm
    simp [parityColoring]
    exact hh
  · intro H hH hhom
    let f : H → Fin 2 := fun x => ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩
    obtain ⟨a, b, hab, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp [hH])
    have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    have hpar : a.val % 2 = b.val % 2 := congrArg Fin.val hf
    let s : Subsets ℕ 2 := ⟨{a.val, b.val}, by simp [hne]⟩
    have hs : (↑s.val : Set ℕ) ⊆ ↑H := by
      intro x hx
      have hh : x = a.val ∨ x = b.val := by simpa [s] using hx
      rcases hh with rfl | rfl
      · exact a.property
      · exact b.property
    have hh : ∀ x ∈ s.val, ∀ y ∈ s.val, x % 2 = y % 2 := by
      simp only [s, Finset.mem_insert, Finset.mem_singleton]
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hpar]
    have hc := hhom s hs
    simp [parityColoring] at hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hc
    exact hxy (hh x hx y hy)

def fivePointColoring : Coloring (Fin 5) 2 (Fin 2) := by
  classical
  exact fun s =>
    if s.val = {0, 1} ∨ s.val = {1, 2} ∨ s.val = {2, 3} ∨
      s.val = {3, 4} ∨ s.val = {0, 4} then 0 else 1

theorem fivePointColoring_no_triple (H : Finset (Fin 5)) (hH : H.card = 3) :
    ¬ IsHomogeneous fivePointColoring (↑H : Set (Fin 5)) := by
  unfold IsHomogeneous IsHomogeneousIn
  simp only [Set.subset_def, Finset.mem_coe]
  decide +revert

private def sixEdge (c : Coloring (Fin 6) 2 (Fin 2)) (a b : Fin 6) : Fin 2 :=
  if h : a = b then 0 else c ⟨{a,b}, by simp [h]⟩

private theorem sixEdge_symm (c : Coloring (Fin 6) 2 (Fin 2)) (a b : Fin 6) :
    sixEdge c a b = sixEdge c b a := by
  classical
  by_cases h : a = b
  · simp [sixEdge, h]
  · simp only [sixEdge, dite_eq_right h, dite_eq_right (Ne.symm h)]
    apply congrArg c
    exact Subtype.ext (Finset.pair_comm a b)

private theorem sixTriangle (c : Coloring (Fin 6) 2 (Fin 2))
    (a b d : Fin 6) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (i : Fin 2) (h₁ : sixEdge c a b = i) (h₂ : sixEdge c a d = i) (h₃ : sixEdge c b d = i) :
    ∃ H : Finset (Fin 6), H.card = 3 ∧ IsHomogeneous c (↑H : Set (Fin 6)) := by
  classical
  refine ⟨{a,b,d}, by simp [hab,had,hbd], i, ?_⟩
  intro s hs
  obtain ⟨x,y,hxy,hset⟩ := Finset.card_eq_two.mp s.property
  have hx : x ∈ ({a,b,d} : Finset (Fin 6)) := hs (by simp [hset])
  have hy : y ∈ ({a,b,d} : Finset (Fin 6)) := hs (by simp [hset])
  have hc : c s = sixEdge c x y := by
    simp only [sixEdge, dite_eq_right hxy]
    apply congrArg c
    exact Subtype.ext hset
  rw [hc]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact False.elim (hxy rfl)
  · exact h₁
  · exact h₂
  · exact (sixEdge_symm c _ _).trans h₁
  · exact False.elim (hxy rfl)
  · exact h₃
  · exact (sixEdge_symm c _ _).trans h₂
  · exact (sixEdge_symm c _ _).trans h₃
  · exact False.elim (hxy rfl)


theorem sixPoint_homogeneous_triple (c : Coloring (Fin 6) 2 (Fin 2)) :
    ∃ H : Finset (Fin 6), H.card = 3 ∧ IsHomogeneous c (↑H : Set (Fin 6)) := by
  classical
  let S : Finset (Fin 6) := {1,2,3,4,5}
  have hS : S.card = 5 := by decide
  have hzero : (0 : Fin 6) ∉ S := by decide
  let F₀ := S.filter (fun b => sixEdge c 0 b = 0)
  let F₁ := S.filter (fun b => sixEdge c 0 b ≠ 0)
  have hsum : F₀.card + F₁.card = 5 := by
    simpa only [F₀,F₁,hS] using Finset.card_filter_add_card_filter_not
      (s := S) (p := fun b => sixEdge c 0 b = 0)
  have hother (j : Fin 2) : j ≠ 0 ↔ j = 1 := by
    fin_cases j <;> decide
  have hfiber : ∃ (i : Fin 2) (F : Finset (Fin 6)),
      2 < F.card ∧ ∀ b ∈ F, b ≠ 0 ∧ sixEdge c 0 b = i := by
    by_cases h : 2 < F₀.card
    · refine ⟨0,F₀,h,?_⟩
      intro b hb
      have hh := Finset.mem_filter.mp hb
      exact ⟨fun hb0 => hzero (hb0 ▸ hh.1), hh.2⟩
    · refine ⟨1,F₁,by omega,?_⟩
      intro b hb
      have hh := Finset.mem_filter.mp hb
      exact ⟨fun hb0 => hzero (hb0 ▸ hh.1), (hother _).mp hh.2⟩
  obtain ⟨i,F,hF,hmem⟩ := hfiber
  obtain ⟨b,d,e,hb,hd,he,hbd,hbe,hde⟩ := Finset.two_lt_card_iff.mp hF
  have h0b := (hmem b hb).1.symm
  have h0d := (hmem d hd).1.symm
  have h0e := (hmem e he).1.symm
  by_cases hbdc : sixEdge c b d = i
  · exact sixTriangle c 0 b d h0b h0d hbd i (hmem b hb).2 (hmem d hd).2 hbdc
  by_cases hbec : sixEdge c b e = i
  · exact sixTriangle c 0 b e h0b h0e hbe i (hmem b hb).2 (hmem e he).2 hbec
  by_cases hdec : sixEdge c d e = i
  · exact sixTriangle c 0 d e h0d h0e hde i (hmem d hd).2 (hmem e he).2 hdec
  let j : Fin 2 := if i = 0 then 1 else 0
  have hremaining (k : Fin 2) (hk : k ≠ i) : k = j := by
    fin_cases i <;> fin_cases k <;> simp_all [j]
  exact sixTriangle c b d e hbd hbe hde j
    (hremaining _ hbdc) (hremaining _ hbec) (hremaining _ hdec)


theorem ramseyNumber_pairs_two_colors_triple :
    ramseyNumber 2 2 3 (by decide) (by decide) (by decide) = 6 := by
  classical
  unfold ramseyNumber
  apply (Nat.find_eq_iff _).mpr
  constructor
  · exact ⟨by decide, sixPoint_homogeneous_triple⟩
  · intro N hN hprop
    have hN5 : N ≤ 5 := by omega
    let e := Fin.castLEEmb hN5
    obtain ⟨H, hH, i, hi⟩ := hprop.2 (pullback e fivePointColoring)
    have hc : (H.map e).card = 3 := (Finset.card_map e).trans hH
    apply fivePointColoring_no_triple (H.map e) hc
    refine ⟨i, ?_⟩
    have hh := (pullback_homogeneousIn e fivePointColoring (↑H : Set (Fin N)) i).mp hi
    simpa only [Finset.coe_map] using hh

theorem constant_colors_disagree (H : Set ℕ) (hH : H.Infinite) :
    IsHomogeneousIn (fun _ : Subsets ℕ 1 => (0 : Fin 2)) H 0 ∧
    IsHomogeneousIn (fun _ : Subsets ℕ 1 => (1 : Fin 2)) H 1 ∧
    ¬ ∃ i : Fin 2,
      IsHomogeneousIn (fun _ : Subsets ℕ 1 => (0 : Fin 2)) H i ∧
      IsHomogeneousIn (fun _ : Subsets ℕ 1 => (1 : Fin 2)) H i := by
  refine ⟨(fun _ _ => rfl), (fun _ _ => rfl), ?_⟩
  rintro ⟨i, h₀, h₁⟩
  obtain ⟨a, ha⟩ := hH.nonempty
  let s : Subsets ℕ 1 := ⟨{a}, by simp⟩
  have hs : (↑s.val : Set ℕ) ⊆ H := by simpa [s] using ha
  have he : (0 : Fin 2) = 1 := (h₀ s hs).trans (h₁ s hs).symm
  exact (by decide : (0 : Fin 2) ≠ 1) he

def cardinalParityColoring (s : Finset ℕ) : Fin 2 :=
  if s.card % 2 = 0 then 0 else 1

theorem cardinalParityColoring_fixed_arity (n : ℕ) (s : Subsets ℕ n) :
    cardinalParityColoring s.val = if n % 2 = 0 then 0 else 1 := by
  simp only [cardinalParityColoring, s.property]

theorem cardinalParityColoring_no_infinite_constant (H : Set ℕ) (hH : H.Infinite) :
    ¬ ∃ i : Fin 2, ∀ s : Finset ℕ,
      (↑s : Set ℕ) ⊆ H → s.Nonempty → cardinalParityColoring s = i := by
  classical
  rintro ⟨i, hi⟩
  obtain ⟨a, ha⟩ := hH.nonempty
  obtain ⟨b, hb, hab⟩ := hH.exists_gt a
  have hne : a ≠ b := ne_of_lt hab
  have h₁ := hi {a} (by simpa using ha) (by simp)
  have h₂ := hi {a, b} (by simp only [Finset.coe_insert, Finset.coe_singleton,
    Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨ha, hb⟩) (by simp)
  simp [cardinalParityColoring, hne] at h₁ h₂
  omega

end Lemmatheca.Entry.PartitionRelations
