import Lemmatheca.FiniteStructureInexpressibility.GraphTranslation
import Mathlib.Data.Nat.ModEq

/-! Arithmetic of the distance-two graph on a finite cyclically ordered carrier. -/
namespace Lemmatheca.ModelTheory.FiniteStructureInexpressibility
open FirstOrder FirstOrder.Language

theorem cyclicSuccessor_fin {n : ℕ} (hn : 0 < n) (a b : Fin n) :
    CyclicSuccessor (fun x y : Fin n => x < y) a b ↔ b.val = (a.val + 1) % n := by
  constructor
  · rintro (⟨hab, hgap⟩ | ⟨hmax, hmin⟩)
    · have heq : b.val = a.val + 1 := by
        by_contra hne
        have habv : a.val < b.val := hab
        let c : Fin n := ⟨a.val + 1, by omega⟩
        exact hgap ⟨c, by change a.val < a.val + 1; omega,
          by change a.val + 1 < b.val; omega⟩
      rw [heq, Nat.mod_eq_of_lt (show a.val + 1 < n by rw [← heq]; exact b.isLt)]
    · have ha : a.val + 1 = n := by
        by_contra hne
        let c : Fin n := ⟨a.val + 1, by omega⟩
        exact hmax ⟨c, by change a.val < a.val + 1; omega⟩
      have hb : b.val = 0 := by
        by_contra hne
        exact hmin ⟨⟨0, hn⟩, by change 0 < b.val; omega⟩
      simp only [ha, hb, Nat.mod_self]
  · intro h
    by_cases hlt : a.val + 1 < n
    · have hb : b.val = a.val + 1 := by simpa only [Nat.mod_eq_of_lt hlt] using h
      left
      refine ⟨by change a.val < b.val; omega, ?_⟩
      rintro ⟨c, hac, hcb⟩
      have hv₁ : a.val < c.val := hac
      have hv₂ : c.val < b.val := hcb
      omega
    · have ha : a.val + 1 = n := by omega
      have hb : b.val = 0 := by simpa only [ha, Nat.mod_self] using h
      right
      constructor
      · rintro ⟨c, hac⟩
        have hv : a.val < c.val := hac
        have hc := c.isLt
        omega
      · rintro ⟨c, hcb⟩
        have hv : c.val < b.val := hcb
        omega

theorem graphEdge_fin {n : ℕ} (hn : 0 < n) (a b : Fin n) :
    GraphEdge (fun x y : Fin n => x < y) a b ↔
      b.val = (a.val + 2) % n ∨ a.val = (b.val + 2) % n := by
  have two (a b : Fin n) :
      (∃ c, CyclicSuccessor (fun x y : Fin n => x < y) a c ∧
        CyclicSuccessor (fun x y : Fin n => x < y) c b) ↔
        b.val = (a.val + 2) % n := by
    constructor
    · rintro ⟨c, hac, hcb⟩
      rw [cyclicSuccessor_fin hn] at hac hcb
      rw [hcb, hac]
      simp only [Nat.mod_add_mod]
    · intro h
      let c : Fin n := ⟨(a.val + 1) % n, Nat.mod_lt _ hn⟩
      refine ⟨c, (cyclicSuccessor_fin hn _ _).mpr rfl, (cyclicSuccessor_fin hn _ _).mpr ?_⟩
      change b.val = ((a.val + 1) % n + 1) % n
      rw [h]
      simp only [Nat.mod_add_mod]
  exact or_congr (two a b) (two b a)

theorem graphEdge_is_graph (n : ℕ) (hn : 3 ≤ n) :
    Std.Symm (GraphEdge (fun x y : Fin n => x < y)) ∧
      Std.Irrefl (GraphEdge (fun x y : Fin n => x < y)) := by
  refine ⟨⟨fun a b h => h.elim Or.inr Or.inl⟩, ⟨fun a h => ?_⟩⟩
  have heq := (graphEdge_fin (by omega) a a).mp h
  rcases heq with heq | heq <;>
    by_cases hlt : a.val + 2 < n
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have hle : n ≤ a.val + 2 := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at heq
    omega
  · rw [Nat.mod_eq_of_lt hlt] at heq
    omega
  · have hle : n ≤ a.val + 2 := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)] at heq
    omega

private theorem step_walk {n : ℕ} (hn : 0 < n) (a : Fin n) (k : ℕ) :
    ExpressiveLimits.Walk (GraphEdge (fun x y : Fin n => x < y)) k a
      ⟨(a.val + 2 * k) % n, Nat.mod_lt _ hn⟩ := by
  induction k generalizing a with
  | zero =>
    apply Fin.ext
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]
  | succ k ih =>
    let c : Fin n := ⟨(a.val + 2) % n, Nat.mod_lt _ hn⟩
    refine ⟨c, (graphEdge_fin hn a c).mpr (Or.inl rfl), ?_⟩
    have h := ih c
    convert h using 1
    apply Fin.ext
    change (a.val + 2 * (k + 1)) % n = ((a.val + 2) % n + 2 * k) % n
    rw [Nat.mod_add_mod]
    congr 1
    omega

private theorem even_edge_parity {n : ℕ} (hn : 0 < n) (he : Even n)
    {a b : Fin n} (h : GraphEdge (fun x y : Fin n => x < y) a b) :
    a.val % 2 = b.val % 2 := by
  obtain ⟨r, hr⟩ := he
  have hd : 2 ∣ n := ⟨r, by omega⟩
  have hmod (x : ℕ) : (x + 2) % n % 2 = x % 2 := by
    rw [Nat.mod_mod_of_dvd _ hd]
    omega
  rcases (graphEdge_fin hn a b).mp h with h | h
  · rw [h, hmod]
  · rw [h, hmod]

private theorem even_walk_parity {n : ℕ} (hn : 0 < n) (he : Even n)
    {a b : Fin n} {k : ℕ}
    (h : ExpressiveLimits.Walk (GraphEdge (fun x y : Fin n => x < y)) k a b) :
    a.val % 2 = b.val % 2 := by
  induction k generalizing a with
  | zero => exact congrArg (fun x : Fin n => x.val % 2) h
  | succ k ih =>
    obtain ⟨c, hac, hcb⟩ := h
    exact (even_edge_parity hn he hac).trans (ih hcb)

theorem cyclic_graph_connected_iff (n : ℕ) (hn : 3 ≤ n) :
    (∀ a b : Fin n, ExpressiveLimits.Reachable (GraphEdge (fun x y : Fin n => x < y)) a b) ↔ Odd n := by
  constructor
  · intro h
    by_contra hodd
    have heven : Even n := Nat.not_odd_iff_even.mp hodd
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    obtain ⟨k, hk⟩ := h a b
    have hp := even_walk_parity (by omega) heven hk
    change 0 % 2 = 1 % 2 at hp
    norm_num at hp
  · rintro ⟨r, hr⟩ a b
    have hn' : n = 2 * r + 1 := by omega
    have hpos : 0 < n := by omega
    let d := b.val + n - a.val
    let k := d * (r + 1)
    have had : a.val + d = b.val + n := by
      dsimp [d]
      have ha := a.isLt
      omega
    have hnum : a.val + 2 * k = (b.val + n) + d * n := by
      dsimp [k]
      calc
        a.val + 2 * (d * (r + 1)) = (a.val + d) + d * (2 * r + 1) := by ring
        _ = (b.val + n) + d * n := by rw [← hn', had]
    have heq : (⟨(a.val + 2 * k) % n, Nat.mod_lt _ hpos⟩ : Fin n) = b := by
      apply Fin.ext
      change (a.val + 2 * k) % n = b.val
      rw [hnum, Nat.add_mul_mod_self_right]
      simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt b.isLt]
    exact ⟨k, heq ▸ step_walk hpos a k⟩


end Lemmatheca.ModelTheory.FiniteStructureInexpressibility
