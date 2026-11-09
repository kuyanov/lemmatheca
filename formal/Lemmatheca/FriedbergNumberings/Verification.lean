import Lemmatheca.FriedbergNumberings.Construction

namespace Lemmatheca.ComputabilityTheory.FriedbergNumberings

open UniversalComputation EffectiveEnumerations

noncomputable section

private def addState (z : State) (e : ℕ) : State :=
  ((rows z) ++ [(e, (none, []))], z.2)

private def copyState (z : State) (e x s : ℕ) : State :=
  ((rows z).set x (e, (none, observedRow e s)), z.2)

private def retireState (z : State) (e x : ℕ) : State :=
  let k := freshEndpoint z x
  ((rows z).set x (e, (some k, List.range (k + 1))), (k, events z ++ [(x, k)]))

private theorem rowAt_get (z : State) (x : ℕ) (hx : x < (rows z).length) :
    rowAt z x = (rows z)[x] := by
  exact (List.getElem_eq_getD (l := rows z) (i := x) (h := hx) (0, (none, []))).symm

private theorem rowAt_add_old (z : State) (e x : ℕ) (hx : x < (rows z).length) :
    rowAt (addState z e) x = rowAt z x := by
  simp only [rowAt, addState, rows, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (show x < z.1.length from hx)]

private theorem rowAt_add_new (z : State) (e : ℕ) :
    rowAt (addState z e) (rows z).length = (e, (none, [])) := by
  simp only [rowAt, addState, rows, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem rowAt_set_self (z : State) (x : ℕ) (r : Row)
    (tail : ℕ × List (ℕ × ℕ)) (hx : x < (rows z).length) :
    rowAt ((rows z).set x r, tail) x = r := by
  simp only [rowAt, rows, List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_self (show x < z.1.length from hx)]
  rfl

private theorem rowAt_set_ne (z : State) (i x : ℕ) (r : Row)
    (tail : ℕ × List (ℕ × ℕ)) (hxi : x ≠ i) :
    rowAt ((rows z).set i r, tail) x = rowAt z x := by
  simp only [rowAt, rows, List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_ne hxi.symm]

private theorem follower_bound (z : State) (e : ℕ) :
    follower e z ≤ (rows z).length := List.findIdx_le_length

private theorem follower_active (z : State) (e : ℕ)
    (h : follower e z < (rows z).length) : Active z e (follower e z) := by
  refine ⟨h, ?_⟩
  have hp := List.findIdx_getElem
    (xs := rows z) (p := fun r => decide (source r = e ∧ endpoint r = none)) (w := h)
  change decide (source (rows z)[follower e z] = e ∧
    endpoint (rows z)[follower e z] = none) = true at hp
  rw [← rowAt_get z (follower e z) h] at hp
  exact of_decide_eq_true hp

private theorem active_implies_follower_bound (z : State) (e x : ℕ)
    (h : Active z e x) : follower e z < (rows z).length := by
  apply List.findIdx_lt_length_of_exists
  refine ⟨rowAt z x, ?_, ?_⟩
  · rw [rowAt_get z x h.1]
    exact List.getElem_mem h.1
  · simp only [h.2.1, h.2.2, and_self, decide_true]

private theorem next_cases (s : ℕ) (z : State) :
    ((∀ x, ¬ Active z (visit s) x) ∧ next s z = addState z (visit s)) ∨
      ∃ x, Active z (visit s) x ∧
        ((passTest (visit s) s x = true ∧ next s z = copyState z (visit s) x s) ∨
          (passTest (visit s) s x = false ∧ next s z = retireState z (visit s) x)) := by
  by_cases ha : follower (visit s) z = (rows z).length
  · left
    refine ⟨?_, ?_⟩
    · intro x hx
      have := active_implies_follower_bound z (visit s) x hx
      omega
    · simp [next, ha, addState, latest, events]
  · right
    have hx : follower (visit s) z < (rows z).length :=
      lt_of_le_of_ne (follower_bound z (visit s)) ha
    refine ⟨follower (visit s) z, follower_active z (visit s) hx, ?_⟩
    cases hp : passTest (visit s) s (follower (visit s) z) with
    | false => exact Or.inr ⟨rfl, by simp [next, ha, hp, retireState]⟩
    | true => exact Or.inl ⟨rfl, by simp [next, ha, hp, copyState, latest, events]⟩

@[simp] private theorem add_length (z : State) (e : ℕ) :
    (rows (addState z e)).length = (rows z).length + 1 := by
  simp [rows, addState]

@[simp] private theorem copy_length (z : State) (e x s : ℕ) :
    (rows (copyState z e x s)).length = (rows z).length := by
  simp [rows, copyState]

@[simp] private theorem retire_length (z : State) (e x : ℕ) :
    (rows (retireState z e x)).length = (rows z).length := by
  simp [rows, retireState]

private theorem active_add (z : State) (e d y : ℕ) :
    Active (addState z e) d y ↔ Active z d y ∨ (y = (rows z).length ∧ d = e) := by
  by_cases hy : y < (rows z).length
  · have hne : y ≠ (rows z).length := by omega
    simp only [Active, add_length, rowAt_add_old z e y hy, hy, hne,
      false_and, or_false, true_and, Nat.lt_succ_of_lt hy]
  · by_cases he : y = (rows z).length
    · subst y
      simp only [Active, add_length, rowAt_add_new, source, endpoint,
        Nat.lt_succ_self, true_and, Nat.lt_irrefl, false_and, false_or, and_true]
      exact eq_comm
    · have hlt : ¬ y < (rows z).length + 1 := by omega
      simp only [Active, add_length, hlt, hy, he, false_and, or_false]

private theorem active_copy (z : State) (e x s d y : ℕ) (hx : Active z e x) :
    Active (copyState z e x s) d y ↔ Active z d y := by
  dsimp only [Active, source, endpoint] at hx
  by_cases hy : y = x
  · subst y
    have he : rowAt (copyState z e x s) x = (e, (none, observedRow e s)) :=
      rowAt_set_self z x _ z.2 hx.1
    simp only [Active, copy_length, he, hx.1, hx.2.1, hx.2.2, source, endpoint,
      true_and, and_true]
  · have he := rowAt_set_ne z x y (e, (none, observedRow e s)) z.2 hy
    change rowAt (copyState z e x s) y = rowAt z y at he
    simp only [Active, copy_length, he]

private theorem active_retire (z : State) (e x d y : ℕ) (hx : Active z e x) :
    Active (retireState z e x) d y ↔ Active z d y ∧ y ≠ x := by
  by_cases hy : y = x
  · subst y
    have he : rowAt (retireState z e x) x =
        (e, (some (freshEndpoint z x), List.range (freshEndpoint z x + 1))) :=
      rowAt_set_self z x _ _ hx.1
    simp only [Active, he, endpoint, reduceCtorEq, and_false, ne_eq,
      not_true_eq_false]
  · have he := rowAt_set_ne z x y
      (e, (some (freshEndpoint z x), List.range (freshEndpoint z x + 1)))
      (freshEndpoint z x, events z ++ [(x, freshEndpoint z x)]) hy
    change rowAt (retireState z e x) y = rowAt z y at he
    simp only [Active, retire_length, he, ne_eq, hy, not_false_eq_true, and_true]

private theorem retired_add (z : State) (e y k : ℕ) :
    Retired (addState z e) y k ↔ Retired z y k := by
  by_cases hy : y < (rows z).length
  · simp only [Retired, add_length, rowAt_add_old z e y hy, hy, true_and,
      Nat.lt_succ_of_lt hy]
  · by_cases he : y = (rows z).length
    · subst y
      simp only [Retired, add_length, rowAt_add_new, endpoint, Nat.lt_succ_self,
        Nat.lt_irrefl, true_and, false_and, reduceCtorEq]
    · have hlt : ¬ y < (rows z).length + 1 := by omega
      simp only [Retired, add_length, hy, hlt, false_and]

private theorem retired_copy (z : State) (e x s y k : ℕ) (hx : Active z e x) :
    Retired (copyState z e x s) y k ↔ Retired z y k := by
  dsimp only [Active, source, endpoint] at hx
  by_cases hy : y = x
  · subst y
    have he : rowAt (copyState z e x s) x = (e, (none, observedRow e s)) :=
      rowAt_set_self z x _ _ hx.1
    simp only [Retired, he, endpoint, hx.2.2, reduceCtorEq, and_false]
  · have he := rowAt_set_ne z x y (e, (none, observedRow e s)) z.2 hy
    change rowAt (copyState z e x s) y = rowAt z y at he
    simp only [Retired, copy_length, he]

private theorem retired_retire (z : State) (e x y k : ℕ) (hx : Active z e x) :
    Retired (retireState z e x) y k ↔
      Retired z y k ∨ (y = x ∧ k = freshEndpoint z x) := by
  dsimp only [Active, source, endpoint] at hx
  by_cases hy : y = x
  · subst y
    have he : rowAt (retireState z e x) x =
        (e, (some (freshEndpoint z x), List.range (freshEndpoint z x + 1))) :=
      rowAt_set_self z x _ _ hx.1
    simp only [Retired, he, retire_length, hx.1, endpoint, hx.2.2, reduceCtorEq,
      true_and, and_false, false_or, Option.some.injEq]
    exact eq_comm
  · have he := rowAt_set_ne z x y
      (e, (some (freshEndpoint z x), List.range (freshEndpoint z x + 1)))
      (freshEndpoint z x, events z ++ [(x, freshEndpoint z x)]) hy
    change rowAt (retireState z e x) y = rowAt z y at he
    simp only [Retired, retire_length, he, hy, false_and, or_false]

theorem allocated_partition (s x : ℕ) (hx : x < allocated s) :
    (∃ e, Active (state s) e x) ∨ ∃ k, Retired (state s) x k := by
  cases he : endpoint (rowAt (state s) x) with
  | none => exact Or.inl ⟨source (rowAt (state s) x), hx, rfl, he⟩
  | some k => exact Or.inr ⟨k, hx, he⟩

theorem active_follower_unique (s e x y : ℕ)
    (hx : Active (state s) e x) (hy : Active (state s) e y) : x = y := by
  induction s generalizing e x y with
  | zero => simpa [Active, state, initialState, rows] using hx.1
  | succ s ih =>
    change Active (next s (state s)) e x at hx
    change Active (next s (state s)) e y at hy
    rcases next_cases s (state s) with ⟨hn, he⟩ | ⟨z, hz, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he, active_add] at hx hy
      rcases hx with hx | ⟨hx, hxe⟩ <;> rcases hy with hy | ⟨hy, hye⟩
      · exact ih e x y hx hy
      · exact False.elim (hn x (hye ▸ hx))
      · exact False.elim (hn y (hxe ▸ hy))
      · exact hx.trans hy.symm
    · rw [he, active_copy _ _ _ _ _ _ hz] at hx hy
      exact ih e x y hx hy
    · rw [he, active_retire _ _ _ _ _ hz] at hx hy
      exact ih e x y hx.1 hy.1

theorem allocated_monotone : Monotone allocated := by
  apply monotone_nat_of_le_succ
  intro s
  change (rows (state s)).length ≤ (rows (next s (state s))).length
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
  all_goals rw [he]; simp [addState, copyState, retireState, rows]

private theorem retired_step (s x k : ℕ) (h : Retired (state s) x k) :
    Retired (state (s + 1)) x k ∧ rowAt (state (s + 1)) x = rowAt (state s) x := by
  change Retired (next s (state s)) x k ∧ rowAt (next s (state s)) x = _
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
  · rw [he]
    exact ⟨(retired_add _ _ _ _).mpr h, rowAt_add_old _ _ _ h.1⟩
  · have hxy : x ≠ y := by
      intro heq; subst x
      have := h.2.symm.trans hy.2.2
      cases this
    rw [he]
    exact ⟨(retired_copy _ _ _ _ _ _ hy).mpr h, rowAt_set_ne _ _ _ _ _ hxy⟩
  · have hxy : x ≠ y := by
      intro heq; subst x
      have := h.2.symm.trans hy.2.2
      cases this
    rw [he]
    exact ⟨(retired_retire _ _ _ _ _ hy).mpr (Or.inl h), rowAt_set_ne _ _ _ _ _ hxy⟩

private theorem retired_contents (s x k : ℕ) (h : Retired (state s) x k) :
    contents (rowAt (state s) x) = List.range (k + 1) := by
  induction s generalizing x k with
  | zero => simpa [state, initialState, Retired, rows] using h.1
  | succ s ih =>
    change Retired (next s (state s)) x k at h
    change contents (rowAt (next s (state s)) x) = _
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he, retired_add] at h
      rw [he, rowAt_add_old _ _ _ h.1]
      exact ih x k h
    · rw [he, retired_copy _ _ _ _ _ _ hy] at h
      have hxy : x ≠ y := by
        intro heq; subst x; have := h.2.symm.trans hy.2.2; cases this
      rw [he, show rowAt (copyState (state s) (visit s) y s) x = rowAt (state s) x from
        rowAt_set_ne _ _ _ _ _ hxy]
      exact ih x k h
    · rw [he, retired_retire _ _ _ _ _ hy] at h
      rcases h with h | ⟨rfl, rfl⟩
      · have hxy : x ≠ y := by
          intro heq; subst x; have := h.2.symm.trans hy.2.2; cases this
        rw [he, show rowAt (retireState (state s) (visit s) y) x = rowAt (state s) x from
          rowAt_set_ne _ _ _ _ _ hxy]
        exact ih x k h
      · rw [he, show rowAt (retireState (state s) (visit s) x) x =
          (visit s, (some (freshEndpoint (state s) x), List.range (freshEndpoint (state s) x + 1))) from
          rowAt_set_self _ _ _ _ hy.1]
        rfl

theorem active_row_subset (s e x : ℕ) (h : Active (state s) e x) :
    rowStage x s ⊆ stage e s := by
  induction s generalizing e x with
  | zero => simpa [state, initialState, Active, rows] using h.1
  | succ s ih =>
    change Active (next s (state s)) e x at h
    intro v hv
    change v ∈ contents (rowAt (next s (state s)) x) at hv
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he, active_add] at h
      rcases h with h | ⟨rfl, rfl⟩
      · rw [he, rowAt_add_old _ _ _ h.1] at hv
        exact stage_monotone e (Nat.le_succ s) (ih e x h hv)
      · rw [he, rowAt_add_new] at hv
        simp [contents] at hv
    · rw [he, active_copy _ _ _ _ _ _ hy] at h
      by_cases hxy : x = y
      · subst x
        have heq : e = visit s := h.2.1.symm.trans hy.2.1
        subst e
        rw [he, show rowAt (copyState (state s) (visit s) y s) y =
          (visit s, (none, observedRow (visit s) s)) from rowAt_set_self _ _ _ _ hy.1] at hv
        have hm := (observed_row_spec (visit s) s v).mp hv
        exact stage_monotone (visit s) (Nat.le_succ s) hm
      · rw [he, show rowAt (copyState (state s) (visit s) y s) x = rowAt (state s) x from
          rowAt_set_ne _ _ _ _ _ hxy] at hv
        exact stage_monotone e (Nat.le_succ s) (ih e x h hv)
    · rw [he, active_retire _ _ _ _ _ hy] at h
      rw [he, show rowAt (retireState (state s) (visit s) y) x = rowAt (state s) x from
        rowAt_set_ne _ _ _ _ _ h.2] at hv
      exact stage_monotone e (Nat.le_succ s) (ih e x h.1 hv)

theorem retired_frozen (s x k : ℕ) (h : Retired (state s) x k) :
    ∀ t, s ≤ t → Retired (state t) x k ∧ rowStage x t = Set.Iic k := by
  intro t ht
  have hr : Retired (state t) x k := by
    induction t, ht using Nat.le_induction with
    | base => exact h
    | succ t ht ih => exact (retired_step t x k ih).1
  refine ⟨hr, ?_⟩
  ext v
  change v ∈ contents (rowAt (state t) x) ↔ v ≤ k
  rw [retired_contents t x k hr, List.mem_range]
  omega

theorem retirement_record_spec (s x k : ℕ) :
    (x, k) ∈ events (state s) ↔ Retired (state s) x k := by
  induction s generalizing x k with
  | zero => simp [state, initialState, events, Retired, rows]
  | succ s ih =>
    change (x, k) ∈ events (next s (state s)) ↔ Retired (next s (state s)) x k
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he, retired_add]
      exact ih x k
    · rw [he, retired_copy _ _ _ _ _ _ hy]
      exact ih x k
    · rw [he, retired_retire _ _ _ _ _ hy]
      change (x, k) ∈ events (state s) ++ [(y, freshEndpoint (state s) y)] ↔ _
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq, ih]

private theorem fold_max_bounds (L : List ℕ) (a : ℕ) :
    a ≤ L.foldl max a ∧ ∀ y ∈ L, y ≤ L.foldl max a := by
  induction L generalizing a with
  | nil => simp
  | cons b L ih =>
    have h := ih (max a b)
    refine ⟨(le_max_left a b).trans h.1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (le_max_right a y).trans h.1
    · exact h.2 y hy

private theorem fresh_gt_latest (z : State) (x : ℕ) : latest z < freshEndpoint z x := by
  unfold freshEndpoint
  have := le_max_left (latest z) ((contents (rowAt z x)).foldl max 0)
  omega

private theorem fresh_gt_contents (z : State) (x y : ℕ)
    (hy : y ∈ contents (rowAt z x)) : y < freshEndpoint z x := by
  have h := (fold_max_bounds (contents (rowAt z x)) 0).2 y hy
  have := le_max_right (latest z) ((contents (rowAt z x)).foldl max 0)
  unfold freshEndpoint
  omega

private theorem rowAt_unallocated (z : State) (x : ℕ) (hx : (rows z).length ≤ x) :
    rowAt z x = (0, (none, [])) := by
  simp only [rowAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem row_stage_monotone (x : ℕ) : Monotone (rowStage x) := by
  apply monotone_nat_of_le_succ
  intro s v hv
  change v ∈ contents (rowAt (state s) x) at hv
  change v ∈ contents (rowAt (next s (state s)) x)
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
  · by_cases hx : x < (rows (state s)).length
    · rw [he, rowAt_add_old _ _ _ hx]; exact hv
    · rw [rowAt_unallocated _ _ (by omega)] at hv
      simp [contents] at hv
  · by_cases hx : x = y
    · subst x
      rw [he, show rowAt (copyState (state s) (visit s) y s) y =
        (visit s, (none, observedRow (visit s) s)) from rowAt_set_self _ _ _ _ hy.1]
      exact (observed_row_spec _ _ _).mpr (active_row_subset s _ y hy hv)
    · rw [he, show rowAt (copyState (state s) (visit s) y s) x = rowAt (state s) x from
        rowAt_set_ne _ _ _ _ _ hx]; exact hv
  · by_cases hx : x = y
    · subst x
      rw [he, show rowAt (retireState (state s) (visit s) y) y =
        (visit s, (some (freshEndpoint (state s) y), List.range (freshEndpoint (state s) y + 1))) from
        rowAt_set_self _ _ _ _ hy.1]
      change v ∈ List.range (freshEndpoint (state s) y + 1)
      exact List.mem_range.mpr (Nat.lt_succ_of_lt (fresh_gt_contents _ _ _ hv))
    · rw [he, show rowAt (retireState (state s) (visit s) y) x = rowAt (state s) x from
        rowAt_set_ne _ _ _ _ _ hx]; exact hv

theorem latest_monotone : Monotone (fun s => latest (state s)) := by
  apply monotone_nat_of_le_succ
  intro s
  change latest (state s) ≤ latest (next s (state s))
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
  · rw [he]; rfl
  · rw [he]; rfl
  · rw [he]
    exact (fresh_gt_latest (state s) x).le

theorem events_monotone : Monotone (fun s => {p : ℕ × ℕ | p ∈ events (state s)}) := by
  apply monotone_nat_of_le_succ
  intro s p hp
  change p ∈ events (next s (state s))
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
  · exact he ▸ hp
  · exact he ▸ hp
  · rw [he]
    exact List.mem_append_left _ hp

theorem events_bound (s : ℕ) (p : ℕ × ℕ) (hp : p ∈ events (state s)) :
    p.2 ≤ latest (state s) := by
  induction s with
  | zero => simp [state, initialState, events] at hp
  | succ s ih =>
    change p ∈ events (next s (state s)) at hp
    change p.2 ≤ latest (next s (state s))
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he] at hp ⊢; exact ih hp
    · rw [he] at hp ⊢; exact ih hp
    · rw [he] at hp ⊢
      change p ∈ events (state s) ++ [(x, freshEndpoint (state s) x)] at hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (ih hp).trans (fresh_gt_latest (state s) x).le
      · have hp := List.mem_singleton.mp hp
        subst p
        rfl

theorem events_stable_below (s t : ℕ) (hst : s ≤ t) (p : ℕ × ℕ)
    (hp : p.2 ≤ latest (state s)) :
    p ∈ events (state t) ↔ p ∈ events (state s) := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    change p ∈ events (next t (state t)) ↔ _
    rcases next_cases t (state t) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he]; exact ih
    · rw [he]; exact ih
    · rw [he]
      change p ∈ events (state t) ++ [(x, freshEndpoint (state t) x)] ↔ _
      have hn : p ≠ (x, freshEndpoint (state t) x) := by
        intro heq
        have hlt := fresh_gt_latest (state t) x
        have hle := latest_monotone hst
        change latest (state s) ≤ latest (state t) at hle
        have hpeq := congrArg Prod.snd heq
        dsimp only at hpeq
        omega
      simpa only [List.mem_append, List.mem_singleton, hn, or_false] using ih

theorem retirement_events_increasing (s : ℕ) :
    (events (state s)).Pairwise (fun a b => a.2 < b.2) := by
  induction s with
  | zero => simp [state, initialState, events]
  | succ s ih =>
    change (events (next s (state s))).Pairwise _
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
    · exact he ▸ ih
    · exact he ▸ ih
    · rw [he]
      change (events (state s) ++ [(x, freshEndpoint (state s) x)]).Pairwise _
      apply List.pairwise_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have hb := List.mem_singleton.mp hb
      subst b
      exact lt_of_le_of_lt (events_bound s a ha) (fresh_gt_latest (state s) x)

theorem latest_record (s : ℕ) :
    latest (state s) = (((events (state s)).getLast?).map Prod.snd).getD 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change latest (next s (state s)) =
      (((events (next s (state s))).getLast?).map Prod.snd).getD 0
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨x, _, ⟨_, he⟩ | ⟨_, he⟩⟩
    · simpa [he, addState, latest, events] using ih
    · simpa [he, copyState, latest, events] using ih
    · simp [he, retireState, latest, events]

theorem retired_positive_even (s x k : ℕ) (h : Retired (state s) x k) :
    0 < k ∧ Even k := by
  induction s generalizing x k with
  | zero => simpa [state, initialState, Retired, rows] using h.1
  | succ s ih =>
    change Retired (next s (state s)) x k at h
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
    · rw [he, retired_add] at h; exact ih x k h
    · rw [he, retired_copy _ _ _ _ _ _ hy] at h; exact ih x k h
    · rw [he, retired_retire _ _ _ _ _ hy] at h
      rcases h with h | ⟨_, rfl⟩
      · exact ih x k h
      · refine ⟨?_, ⟨max (latest (state s)) ((contents (rowAt (state s) y)).foldl max 0) + 1, ?_⟩⟩
        · unfold freshEndpoint; omega
        · unfold freshEndpoint; omega

private theorem copied_at_visit (s e x : ℕ) (he : visit s = e)
    (ha : Active (state s) e x) (hb : Active (state (s + 1)) e x) :
    passTest e s x = true ∧ next s (state s) = copyState (state s) e x s := by
  change Active (next s (state s)) e x at hb
  rcases next_cases s (state s) with ⟨hn, hnxt⟩ | ⟨y, hy, ⟨hp, hnxt⟩ | ⟨_, hnxt⟩⟩
  · exact False.elim (hn x (he.symm ▸ ha))
  · have hxy := active_follower_unique s e x y ha (he ▸ hy)
    subst y
    simpa only [he] using And.intro hp hnxt
  · have hxy := active_follower_unique s e x y ha (he ▸ hy)
    subst y
    rw [hnxt, active_retire _ _ _ _ _ hy] at hb
    exact False.elim (hb.2 rfl)

theorem permanent_row (e x : ℕ) (h : Permanent e x) : preliminaryRow x = indexSet e := by
  obtain ⟨S, hS⟩ := h
  ext v
  constructor
  · rintro ⟨s, hs⟩
    have ht := row_stage_monotone x (le_max_left s S) hs
    exact (stage_union e v).mpr ⟨max s S, active_row_subset _ e x (hS _ (le_max_right s S)) ht⟩
  · intro hv
    obtain ⟨s, hs⟩ := (stage_union e v).mp hv
    obtain ⟨t, ht, he⟩ := fair_visits e (max S s)
    have hSt : S ≤ t := (le_max_left S s).trans ht
    have hc := (copied_at_visit t e x he (hS t hSt) (hS (t + 1) (by omega))).2
    refine ⟨t + 1, ?_⟩
    change v ∈ contents (rowAt (next t (state t)) x)
    rw [hc, show rowAt (copyState (state t) e x t) x = (e, (none, observedRow e t)) from
      rowAt_set_self _ _ _ _ (hS t hSt).1]
    exact (observed_row_spec e t v).mpr
      (stage_monotone e ((le_max_right S s).trans ht) hs)

private theorem permanent_pass_late (e x : ℕ) (h : Permanent e x) (T : ℕ) :
    ∃ t, T ≤ t ∧ Passes e t x := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨t, ht, he⟩ := fair_visits e (max S T)
  have hSt : S ≤ t := (le_max_left S T).trans ht
  exact ⟨t, (le_max_right S T).trans ht,
    (pass_test_spec e t x).mp
      (copied_at_visit t e x he (hS t hSt) (hS (t + 1) (by omega))).1⟩

theorem permanent_least_noninitial (e x : ℕ) (h : Permanent e x) :
    ¬ IsLowerSet (indexSet e) ∧ ∀ j < e, indexSet e ≠ indexSet j := by
  constructor
  · obtain ⟨S, hS⟩ := finite_prefix_stabilization e x
    obtain ⟨t, ht, hp⟩ := permanent_pass_late e x h S
    rw [Passes, hS t ht] at hp
    intro hl
    apply hp.1
    intro a b hab hb
    exact ⟨hl hab hb.1, hab.trans hb.2⟩
  · intro j hj heq
    obtain ⟨S, hS⟩ := finite_prefix_stabilization e x
    obtain ⟨T, hT⟩ := finite_prefix_stabilization j x
    obtain ⟨t, ht, hp⟩ := permanent_pass_late e x h (max S T)
    apply hp.2 j hj
    rw [hS t ((le_max_left S T).trans ht), hT t ((le_max_right S T).trans ht), heq]

private theorem active_predecessor (s e x : ℕ) (ha : Active (state (s + 1)) e x) :
    Active (state s) e x ∨ (x = allocated s ∧ allocated (s + 1) = allocated s + 1) := by
  change Active (next s (state s)) e x at ha
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
  · rw [he, active_add] at ha
    rcases ha with ha | ⟨hxa, _⟩
    · exact Or.inl ha
    · exact Or.inr ⟨hxa, by change (rows (next s (state s))).length = _; rw [he, add_length]; rfl⟩
  · rw [he, active_copy _ _ _ _ _ _ hy] at ha; exact Or.inl ha
  · rw [he, active_retire _ _ _ _ _ hy] at ha; exact Or.inl ha.1

private theorem active_existing_back (s t e x : ℕ) (hst : s ≤ t)
    (hx : x < allocated s) (ha : Active (state t) e x) : Active (state s) e x := by
  induction t, hst using Nat.le_induction with
  | base => exact ha
  | succ t hst ih =>
    rcases active_predecessor t e x ha with hb | ⟨he, _⟩
    · exact ih hb
    · have hle := allocated_monotone hst
      omega

private theorem active_or_retired_step (s e x : ℕ) (ha : Active (state s) e x) :
    Active (state (s + 1)) e x ∨ ∃ k, Retired (state (s + 1)) x k := by
  change Active (next s (state s)) e x ∨ ∃ k, Retired (next s (state s)) x k
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
  · exact Or.inl (he ▸ (active_add _ _ _ _).mpr (Or.inl ha))
  · exact Or.inl (he ▸ (active_copy _ _ _ _ _ _ hy).mpr ha)
  · rw [he]
    by_cases hxy : x = y
    · subst x
      exact Or.inr ⟨freshEndpoint (state s) y,
        (retired_retire _ _ _ _ _ hy).mpr (Or.inr ⟨rfl, rfl⟩)⟩
    · exact Or.inl ((active_retire _ _ _ _ _ hy).mpr ⟨ha, hxy⟩)

private theorem active_eventually_retires (s e x : ℕ) (ha : Active (state s) e x)
    (hn : ¬ Permanent e x) : ∃ t k, s ≤ t ∧ Retired (state t) x k := by
  classical
  by_contra h
  apply hn
  refine ⟨s, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ha
  | succ t ht ih =>
    rcases active_or_retired_step t e x ih with hh | ⟨k, hk⟩
    · exact hh
    · exact False.elim (h ⟨t + 1, k, by omega, hk⟩)

private theorem active_after_visit (e S : ℕ) :
    ∃ s x, S ≤ s ∧ Active (state s) e x := by
  obtain ⟨t, ht, he⟩ := fair_visits e S
  rcases next_cases t (state t) with ⟨_, hn⟩ | ⟨x, hx, _⟩
  · refine ⟨t + 1, allocated t, by omega, ?_⟩
    change Active (next t (state t)) e (rows (state t)).length
    rw [hn, active_add]
    exact Or.inr ⟨rfl, he.symm⟩
  · exact ⟨t, x, ht, he ▸ hx⟩

private theorem empty_index_exists : ∃ e, indexSet e = ∅ := by
  obtain ⟨e, he⟩ := phi_complete (f := fun _ => Part.none) Nat.Partrec.none
  refine ⟨e, ?_⟩
  ext x
  simp [indexSet, he]

private theorem allocation_late (S : ℕ) : ∃ s, S ≤ s ∧ allocated s < allocated (s + 1) := by
  classical
  by_contra hn
  have hno (s : ℕ) (hs : S ≤ s) : allocated (s + 1) = allocated s := by
    have hle := allocated_monotone (Nat.le_succ s)
    change allocated s ≤ allocated (s + 1) at hle
    have hnot : ¬ allocated s < allocated (s + 1) := fun h => hn ⟨s, hs, h⟩
    omega
  have hback (s t e x : ℕ) (hSs : S ≤ s) (hst : s ≤ t)
      (ha : Active (state t) e x) : Active (state s) e x := by
    induction t, hst using Nat.le_induction with
    | base => exact ha
    | succ t hst ih =>
      rcases active_predecessor t e x ha with hb | ⟨_, hh⟩
      · exact ih hb
      · have := hno t (hSs.trans hst); omega
  obtain ⟨e, he⟩ := empty_index_exists
  obtain ⟨t, x, ht, hx⟩ := active_after_visit e S
  have hxS := hback S t e x (le_refl S) ht hx
  have hp : Permanent e x := by
    refine ⟨S, ?_⟩
    intro r hr
    obtain ⟨u, y, hu, hy⟩ := active_after_visit e r
    have hyS := hback S u e y (le_refl S) (hr.trans hu) hy
    have hxy := active_follower_unique S e x y hxS hyS
    subst y
    exact hback r u e x hr hu hy
  have hni := (permanent_least_noninitial e x hp).1
  rw [he] at hni
  exact hni (fun _ _ _ h => False.elim h)

private theorem retirement_late (S : ℕ) :
    ∃ s, S ≤ s ∧ latest (state s) < latest (state (s + 1)) := by
  classical
  by_contra hn
  have hno (s : ℕ) (hs : S ≤ s) : latest (state (s + 1)) = latest (state s) := by
    have hle := latest_monotone (Nat.le_succ s)
    change latest (state s) ≤ latest (state (s + 1)) at hle
    have hnot : ¬ latest (state s) < latest (state (s + 1)) := fun h => hn ⟨s, hs, h⟩
    omega
  have hstep (s e x : ℕ) (hs : S ≤ s) (ha : Active (state s) e x) :
      Active (state (s + 1)) e x := by
    change Active (next s (state s)) e x
    rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨_, he⟩⟩
    · exact he ▸ (active_add _ _ _ _).mpr (Or.inl ha)
    · exact he ▸ (active_copy _ _ _ _ _ _ hy).mpr ha
    · have hh := hno s hs
      change latest (next s (state s)) = _ at hh
      rw [he] at hh
      have hg := fresh_gt_latest (state s) y
      change freshEndpoint (state s) y = _ at hh
      omega
  obtain ⟨e, he⟩ := empty_index_exists
  obtain ⟨s, x, hs, hx⟩ := active_after_visit e S
  have hp : Permanent e x := by
    refine ⟨s, ?_⟩
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact hx
    | succ t ht ih => exact hstep t e x (hs.trans ht) ih
  have hni := (permanent_least_noninitial e x hp).1
  rw [he] at hni
  exact hni (fun _ _ _ h => False.elim h)

theorem infinitely_many_allocations_and_retirements :
    {s | allocated s < allocated (s + 1)}.Infinite ∧
      {s | latest (state s) < latest (state (s + 1))}.Infinite := by
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro S
    obtain ⟨s, hs, hh⟩ := allocation_late (S + 1)
    exact ⟨s, hh, by omega⟩
  · apply Set.infinite_of_forall_exists_gt
    intro S
    obtain ⟨s, hs, hh⟩ := retirement_late (S + 1)
    exact ⟨s, hh, by omega⟩

theorem all_rows_allocated (x : ℕ) : ∃ s, x < allocated s := by
  have hu (n : ℕ) : ∃ s, n ≤ allocated s := by
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨t, ht, hh⟩ := allocation_late s
      have hle := allocated_monotone ht
      exact ⟨t + 1, by omega⟩
  obtain ⟨s, hs⟩ := hu (x + 1)
  exact ⟨s, by omega⟩

theorem latest_unbounded (n : ℕ) : ∃ s, n ≤ latest (state s) := by
  induction n with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht, hh⟩ := retirement_late s
    have hle := latest_monotone ht
    change latest (state s) ≤ latest (state t) at hle
    exact ⟨t + 1, by omega⟩

theorem row_eventually_classified (x : ℕ) :
    (∃ e, Permanent e x) ∨ ∃ s k, Retired (state s) x k := by
  classical
  by_cases hr : ∃ s k, Retired (state s) x k
  · exact Or.inr hr
  · left
    obtain ⟨s, hs⟩ := all_rows_allocated x
    rcases allocated_partition s x hs with ⟨e, he⟩ | ⟨k, hk⟩
    · refine ⟨e, ?_⟩
      by_contra hn
      obtain ⟨t, k, _, hk⟩ := active_eventually_retires s e x he hn
      exact hr ⟨t, k, hk⟩
    · exact False.elim (hr ⟨s, k, hk⟩)

private theorem active_large (e B S : ℕ) (hn : ¬ ∃ x, Permanent e x) :
    ∃ s x, S ≤ s ∧ B ≤ x ∧ Active (state s) e x := by
  induction B with
  | zero =>
    obtain ⟨s, x, hs, hx⟩ := active_after_visit e S
    exact ⟨s, x, hs, Nat.zero_le _, hx⟩
  | succ B ih =>
    obtain ⟨s, x, hs, hBx, ha⟩ := ih
    by_cases hb : B + 1 ≤ x
    · exact ⟨s, x, hs, hb, ha⟩
    have hxB : x = B := by omega
    obtain ⟨t, k, hst, hr⟩ := active_eventually_retires s e x ha (fun hp => hn ⟨x, hp⟩)
    obtain ⟨u, y, htu, hu⟩ := active_after_visit e t
    have hlarge : allocated s ≤ y := by
      by_contra hh
      have hback := active_existing_back s u e y (hst.trans htu) (by omega) hu
      have hyx := active_follower_unique s e y x hback ha
      subst y
      have hret := (retired_frozen t x k hr u htu).1
      have hbad := hret.2.symm.trans hu.2.2
      cases hbad
    have hxalloc : x < allocated s := ha.1
    exact ⟨u, y, hs.trans (hst.trans htu), by omega, hu⟩

private theorem active_step_if_pass (s e x : ℕ) (ha : Active (state s) e x)
    (hp : visit s = e → passTest e s x = true) : Active (state (s + 1)) e x := by
  change Active (next s (state s)) e x
  rcases next_cases s (state s) with ⟨_, he⟩ | ⟨y, hy, ⟨_, he⟩ | ⟨hf, he⟩⟩
  · exact he ▸ (active_add _ _ _ _).mpr (Or.inl ha)
  · exact he ▸ (active_copy _ _ _ _ _ _ hy).mpr ha
  · rw [he]
    apply (active_retire _ _ _ _ _ hy).mpr
    refine ⟨ha, ?_⟩
    intro hxy
    subst y
    have hve : visit s = e := hy.2.1.symm.trans ha.2.1
    have ht := hp hve
    rw [← hve, hf] at ht
    cases ht

theorem eventual_pass (e : ℕ) (hi : ¬ IsLowerSet (indexSet e))
    (he : ∀ j < e, indexSet e ≠ indexSet j) :
    ∃ B S, ∀ s, S ≤ s → ∀ x, B ≤ x → Passes e s x := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := (noninitial_witness (indexSet e)).mp hi
  have hd : ∀ j : Fin e, ∃ n, ¬ (n ∈ indexSet e ↔ n ∈ indexSet j.val) := by
    intro j
    by_contra hn
    apply he j.val j.isLt
    ext n
    by_contra hne
    exact hn ⟨n, hne⟩
  choose w hw using hd
  let B := max b (Finset.univ.sup w)
  have hbB : b ≤ B := le_max_left _ _
  have haB : a ≤ B := hab.le.trans hbB
  have hwB (j : Fin e) : w j ≤ B :=
    (Finset.le_sup (f := w) (Finset.mem_univ j)).trans (le_max_right _ _)
  have htimes : ∀ i : Fin (e + 1), ∃ T, ∀ s, T ≤ s →
      stage i.val s ∩ Set.Iic B = indexSet i.val ∩ Set.Iic B := by
    intro i
    exact finite_prefix_stabilization i.val B
  choose time htime using htimes
  let S := Finset.univ.sup time
  refine ⟨B, S, ?_⟩
  intro s hSs x hBx
  have hsettle (i : ℕ) (hie : i ≤ e) (y : ℕ) (hy : y ≤ B) :
      y ∈ stage i s ↔ y ∈ indexSet i := by
    let j : Fin (e + 1) := ⟨i, by omega⟩
    have ht : time j ≤ s := (Finset.le_sup (f := time) (Finset.mem_univ j)).trans hSs
    have hs := htime j s ht
    have hm : y ∈ stage i s ∩ Set.Iic B ↔ y ∈ indexSet i ∩ Set.Iic B := by
      rw [hs]
    simpa only [Set.mem_inter_iff, Set.mem_Iic, hy, and_true] using hm
  refine ⟨?_, ?_⟩
  · apply (noninitial_witness (stage e s ∩ Set.Iic x)).mpr
    refine ⟨a, b, hab, ?_, ?_⟩
    · intro hmem
      exact ha ((hsettle e le_rfl a haB).mp hmem.1)
    · exact ⟨(hsettle e le_rfl b hbB).mpr hb, hbB.trans hBx⟩
  · intro j hj heq
    let i : Fin e := ⟨j, hj⟩
    have hwx : w i ≤ x := (hwB i).trans hBx
    have hm : w i ∈ stage e s ∩ Set.Iic x ↔ w i ∈ stage j s ∩ Set.Iic x := by
      rw [heq]
    have hstages : w i ∈ stage e s ↔ w i ∈ stage j s := by
      simpa only [Set.mem_inter_iff, Set.mem_Iic, hwx, and_true] using hm
    exact hw i ((hsettle e le_rfl (w i) (hwB i)).symm.trans
      (hstages.trans (hsettle j hj.le (w i) (hwB i))))


theorem least_noninitial_permanent (e : ℕ) (hi : ¬ IsLowerSet (indexSet e))
    (he : ∀ j < e, indexSet e ≠ indexSet j) : ∃ x, Permanent e x := by
  classical
  by_contra hn
  obtain ⟨B, S, hpass⟩ := eventual_pass e hi he
  obtain ⟨s, x, hs, hx, ha⟩ := active_large e B S hn
  apply hn
  refine ⟨x, s, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ha
  | succ t ht ih =>
    apply active_step_if_pass t e x ih
    intro _
    exact (pass_test_spec e t x).mpr (hpass t (hs.trans ht) x hx)

private theorem retired_row (s x k : ℕ) (h : Retired (state s) x k) :
    preliminaryRow x = Set.Iic k := by
  ext v
  constructor
  · rintro ⟨t, ht⟩
    have hm := row_stage_monotone x (le_max_right s t) ht
    rw [(retired_frozen s x k h (max s t) (le_max_left s t)).2] at hm
    exact hm
  · intro hv
    refine ⟨s, ?_⟩
    rw [(retired_frozen s x k h s (le_refl s)).2]
    exact hv

theorem preliminary_injective : Function.Injective preliminaryRow := by
  intro x y hxy
  rcases row_eventually_classified x with ⟨e, he⟩ | ⟨s, k, hk⟩ <;>
    rcases row_eventually_classified y with ⟨f, hf⟩ | ⟨t, l, hl⟩
  · have hef : indexSet e = indexSet f :=
      (permanent_row e x he).symm.trans (hxy.trans (permanent_row f y hf))
    have heq : e = f := by
      rcases lt_trichotomy e f with hlt | heq | hgt
      · exact False.elim ((permanent_least_noninitial f y hf).2 e hlt hef.symm)
      · exact heq
      · exact False.elim ((permanent_least_noninitial e x he).2 f hgt hef)
    subst f
    obtain ⟨S, hS⟩ := he
    obtain ⟨T, hT⟩ := hf
    exact active_follower_unique (max S T) e x y
      (hS _ (le_max_left S T)) (hT _ (le_max_right S T))
  · have hi := (permanent_least_noninitial e x he).1
    have heq : indexSet e = Set.Iic l :=
      (permanent_row e x he).symm.trans (hxy.trans (retired_row t y l hl))
    rw [heq] at hi
    exact False.elim (hi (fun _ _ hab hb => hab.trans hb))
  · have hi := (permanent_least_noninitial f y hf).1
    have heq : indexSet f = Set.Iic k :=
      (permanent_row f y hf).symm.trans (hxy.symm.trans (retired_row s x k hk))
    rw [heq] at hi
    exact False.elim (hi (fun _ _ hab hb => hab.trans hb))
  · have heq : Set.Iic k = Set.Iic l :=
      (retired_row s x k hk).symm.trans (hxy.trans (retired_row t y l hl))
    have hkl : k = l := by
      have h1 : k ∈ Set.Iic l := heq ▸ (show k ∈ Set.Iic k from le_refl k)
      have h2 : l ∈ Set.Iic k := heq.symm ▸ (show l ∈ Set.Iic l from le_refl l)
      exact Nat.le_antisymm h1 h2
    subst l
    have hx : (x, k) ∈ events (state (max s t)) :=
      events_monotone (le_max_left s t) ((retirement_record_spec s x k).mpr hk)
    have hy : (y, k) ∈ events (state (max s t)) :=
      events_monotone (le_max_right s t) ((retirement_record_spec t y k).mpr hl)
    have hn : ((events (state (max s t))).map Prod.snd).Nodup := by
      apply List.pairwise_map.mpr
      exact (retirement_events_increasing (max s t)).imp (fun h => ne_of_lt h)
    exact congrArg Prod.fst (List.inj_on_of_nodup_map hn hx hy rfl)

theorem preliminary_range (A : Set ℕ) :
    (∃ x, preliminaryRow x = A) ↔
      (REPred A ∧ ¬ IsLowerSet A) ∨
        ∃ k, k ∈ retirementEndpoints ∧ A = Set.Iic k := by
  classical
  constructor
  · rintro ⟨x, rfl⟩
    rcases row_eventually_classified x with ⟨e, he⟩ | ⟨s, k, hk⟩
    · left
      rw [permanent_row e x he]
      exact ⟨(enumerable_iff_index _).mpr ⟨e, fun _ => Iff.rfl⟩,
        (permanent_least_noninitial e x he).1⟩
    · right
      exact ⟨k, ⟨s, x, (retirement_record_spec s x k).mpr hk⟩, retired_row s x k hk⟩
  · rintro (⟨hA, hi⟩ | ⟨k, ⟨s, x, hk⟩, rfl⟩)
    · obtain ⟨d, hd⟩ := (enumerable_iff_index A).mp hA
      have hex : ∃ e, indexSet e = A := ⟨d, Set.ext (fun x => (hd x).symm)⟩
      let e := Nat.find hex
      have heA : indexSet e = A := Nat.find_spec hex
      have hleast (j : ℕ) (hj : j < e) : indexSet e ≠ indexSet j := by
        intro heq
        exact Nat.find_min hex hj (heq.symm.trans heA)
      obtain ⟨x, hx⟩ := least_noninitial_permanent e (heA.symm ▸ hi) hleast
      exact ⟨x, (permanent_row e x hx).trans heA⟩
    · exact ⟨x, retired_row s x k ((retirement_record_spec s x k).mp hk)⟩

theorem preliminary_nonempty_proper (x : ℕ) :
    preliminaryRow x ≠ ∅ ∧ preliminaryRow x ≠ Set.univ := by
  rcases row_eventually_classified x with ⟨e, he⟩ | ⟨s, k, hk⟩
  · rw [permanent_row e x he]
    have hi := (permanent_least_noninitial e x he).1
    constructor
    · intro hh
      apply hi
      rw [hh]
      exact fun _ _ _ hm => False.elim hm
    · intro hh
      apply hi
      rw [hh]
      exact fun _ _ _ _ => trivial
  · rw [retired_row s x k hk]
    constructor
    · intro hh
      have hm : 0 ∈ Set.Iic k := Nat.zero_le _
      rw [hh] at hm
      exact hm
    · intro hh
      have hm : k + 1 ∈ Set.Iic k := hh.symm ▸ (Set.mem_univ (k + 1))
      change k + 1 ≤ k at hm
      omega

end
end Lemmatheca.ComputabilityTheory.FriedbergNumberings
