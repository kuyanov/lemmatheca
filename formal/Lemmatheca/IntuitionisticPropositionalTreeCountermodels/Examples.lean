import Lemmatheca.IntuitionisticPropositionalTreeCountermodels.Models
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Order.Preorder.Finite

namespace Lemmatheca.Entry.IntuitionisticPropositionalTreeCountermodels

open Lemmatheca.ProofTheory.Intuitionistic.Kripke
open Lemmatheca.ProofTheory.Intuitionistic.Kripke.StrictPaths
open Lemmatheca.MathematicalLogic.Propositional

universe u v

abbrev Diamond := Bool × Bool
local instance diamondDecidableLT : DecidableLT Diamond := fun x y =>
  decidable_of_iff' (x ≤ y ∧ ¬ y ≤ x) lt_iff_le_not_ge

def diamondRoot : Diamond := (false, false)
def diamondLeft : Diamond := (true, false)
def diamondRight : Diamond := (false, true)
def diamondTop : Diamond := (true, true)

theorem diamond_order_spec (x y : Diamond) :
    x ≤ y ↔ x = diamondRoot ∨ x = y ∨ y = diamondTop := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;> decide

theorem diamond_not_tree : ¬ IsFiniteRootedTree diamondRoot := by
  intro h
  have hc := h.2.2 diamondLeft diamondRight diamondTop (by decide) (by decide)
  rcases hc with hc | hc
  · exact (by decide : ¬ diamondLeft ≤ diamondRight) hc
  · exact (by decide : ¬ diamondRight ≤ diamondLeft) hc

/-- All six lists in the displayed all-strict-path diamond example. -/
def diamondLists : Fin 6 → List Diamond
  | 0 => [diamondRoot]
  | 1 => [diamondRoot, diamondLeft]
  | 2 => [diamondRoot, diamondRight]
  | 3 => [diamondRoot, diamondTop]
  | 4 => [diamondRoot, diamondLeft, diamondTop]
  | 5 => [diamondRoot, diamondRight, diamondTop]

def diamondPath (i : Fin 6) : Path diamondRoot :=
  ⟨diamondLists i, by unfold IsPath; fin_cases i <;> decide⟩

private theorem diamond_root_successor (x : Diamond) :
    diamondRoot < x → x = diamondLeft ∨ x = diamondRight ∨ x = diamondTop := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> decide

private theorem diamond_left_successor (x : Diamond) :
    diamondLeft < x → x = diamondTop := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> decide

private theorem diamond_right_successor (x : Diamond) :
    diamondRight < x → x = diamondTop := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> decide

private theorem diamond_top_no_successor (x : Diamond) : ¬ diamondTop < x := by
  exact not_lt_of_ge (show x ≤ diamondTop from le_top)

theorem diamond_paths_exact (p : Path diamondRoot) :
    ∃ i : Fin 6, diamondPath i = p := by
  rcases p with ⟨l, hp⟩
  cases l with
  | nil => simp [IsPath] at hp
  | cons a tail =>
      have ha : a = diamondRoot := by
        simpa only [List.head?_cons, Option.some.injEq] using hp.1
      subst a
      cases tail with
      | nil => exact ⟨0, Path.ext_val rfl⟩
      | cons x tail =>
          have hx : diamondRoot < x := (List.pairwise_cons.mp hp.2).1 x (by simp)
          have ht := (List.pairwise_cons.mp hp.2).2
          rcases diamond_root_successor x hx with rfl | rfl | rfl
          · cases tail with
            | nil => exact ⟨1, Path.ext_val rfl⟩
            | cons y tail =>
                have hy : y = diamondTop :=
                  diamond_left_successor y ((List.pairwise_cons.mp ht).1 y (by simp))
                subst y
                cases tail with
                | nil => exact ⟨4, Path.ext_val rfl⟩
                | cons z zs =>
                    have hz := (List.pairwise_cons.mp (List.pairwise_cons.mp ht).2).1 z (by simp)
                    exact (diamond_top_no_successor z hz).elim
          · cases tail with
            | nil => exact ⟨2, Path.ext_val rfl⟩
            | cons y tail =>
                have hy : y = diamondTop :=
                  diamond_right_successor y ((List.pairwise_cons.mp ht).1 y (by simp))
                subst y
                cases tail with
                | nil => exact ⟨5, Path.ext_val rfl⟩
                | cons z zs =>
                    have hz := (List.pairwise_cons.mp (List.pairwise_cons.mp ht).2).1 z (by simp)
                    exact (diamond_top_no_successor z hz).elim
          · cases tail with
            | nil => exact ⟨3, Path.ext_val rfl⟩
            | cons y ys =>
                exact (diamond_top_no_successor y ((List.pairwise_cons.mp ht).1 y (by simp))).elim

theorem diamond_path_card : Fintype.card (Path diamondRoot) = 6 := by
  have hd : Function.Injective diamondLists := by unfold Function.Injective; decide
  have hi : Function.Injective diamondPath := by
    intro i j h
    exact hd (congrArg Path.val h)
  have hc := Fintype.card_congr (Equiv.ofBijective diamondPath ⟨hi, diamond_paths_exact⟩)
  simpa only [Fintype.card_fin] using hc.symm

theorem diamond_top_paths (i : Fin 6) :
    last (diamondPath i) = diamondTop ↔ i = 3 ∨ i = 4 ∨ i = 5 := by
  fin_cases i <;> decide

theorem diamond_incomparable :
    ¬ diamondPath 4 ≤ diamondPath 5 ∧ ¬ diamondPath 5 ≤ diamondPath 4 := by
  change ¬ (diamondLists 4).IsPrefix (diamondLists 5) ∧
    ¬ (diamondLists 5).IsPrefix (diamondLists 4)
  decide

def diamondModel {α : Type u} (a : α) : Model α Diamond where
  world_nonempty := ⟨diamondRoot⟩
  valuation w q := w = ⊤ ∧ q = a
  persistent h _ hq := by
    rcases hq with ⟨rfl, hqa⟩
    exact ⟨top_le_iff.mp h, hqa⟩

theorem diamond_path_atom {α : Type u} (a : α) (i : Fin 6) :
    Forces (model (diamondModel a) diamondRoot) (diamondPath i) (.atom a) ↔
      i = 3 ∨ i = 4 ∨ i = 5 := by
  change (last (diamondPath i) = diamondTop ∧ a = a) ↔ i = 3 ∨ i = 4 ∨ i = 5
  exact ⟨fun h => (diamond_top_paths i).mp h.1,
    fun h => ⟨(diamond_top_paths i).mpr h, rfl⟩⟩

/-- Nonempty nondecreasing paths in the actual one-world preorder. -/
def WeakSingletonPath :=
  {l : List PUnit // l ≠ [] ∧ l.Pairwise (· ≤ ·)}

def repetitions (n : ℕ) : WeakSingletonPath :=
  ⟨List.replicate (n + 1) PUnit.unit, by simp⟩

theorem repetitions_injective : Function.Injective repetitions := by
  intro m n h
  have hl := congrArg (fun p : WeakSingletonPath => p.val.length) h
  simp only [repetitions, List.length_replicate] at hl
  exact Nat.add_right_cancel hl

theorem weak_singleton_infinite : Infinite WeakSingletonPath := by
  exact Infinite.of_injective repetitions repetitions_injective

/-- This explicitly supplied preorder is universal, unlike the standard Boolean order. -/
@[instance_reducible] def clusterPreorder : Preorder Bool where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
  lt_iff_le_not_ge _ _ := by simp

theorem no_finite_poset_cluster_map {X : Type v} [PartialOrder X] [Finite X] [Nonempty X]
    (f : X → Bool) :
    ¬ @IsBoundedFrameMap X Bool inferInstance clusterPreorder f := by
  classical
  obtain ⟨m, hm⟩ := (Set.finite_univ : (Set.univ : Set X).Finite).exists_maximal Set.univ_nonempty
  intro hf
  obtain ⟨v, hmv, hfv⟩ :=
    @IsBoundedFrameMap.back X Bool inferInstance clusterPreorder f hf m (!(f m)) trivial
  have hvm : v ≤ m := hm.2 (Set.mem_univ v) hmv
  have hvm' : v = m := le_antisymm hvm hmv
  have hn : f m ≠ !(f m) := by cases f m <;> decide
  exact hn (by simpa only [hvm'] using hfv)

end Lemmatheca.Entry.IntuitionisticPropositionalTreeCountermodels
