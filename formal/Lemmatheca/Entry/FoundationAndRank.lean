import Lemmatheca.Entry.NaturalNumbersAsSets
import Mathlib.SetTheory.ZFC.Cardinal

set_option autoImplicit false

/-! Transitive closure uses the entry's superset convention, so it does not
automatically contain its input as a member. Local rank functions use small
membership subtypes; their values live in `Ordinal.{u}`. -/
namespace Lemmatheca.Entry.FoundationAndRank
open scoped ZFSet Ordinal
universe u v

def closureStage (x : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => x
  | n + 1 => closureStage x n ∪ ZFSet.sUnion (closureStage x n)

noncomputable def transitiveClosure (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (closureStage x)

def IsTransitiveClosure (x T : ZFSet.{u}) : Prop :=
  T.IsTransitive ∧ x ⊆ T ∧ ∀ U, U.IsTransitive → x ⊆ U → T ⊆ U

theorem transitiveClosure_spec (x : ZFSet.{u}) :
    IsTransitiveClosure x (transitiveClosure x) := by
  sorry

theorem transitiveClosure_unique (x : ZFSet.{u}) : ∃! T, IsTransitiveClosure x T := by
  sorry

theorem transitiveClosure_fixed (T : ZFSet.{u}) (hT : T.IsTransitive) :
    transitiveClosure T = T := by
  sorry

theorem closure_examples :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    let x : ZFSet.{u} := {a, b}
    transitiveClosure x = {z, a, b} ∧ transitiveClosure ({x} : ZFSet.{u}) = {z, a, b, x} ∧
      transitiveClosure (∅ : ZFSet.{u}) = ∅ ∧ x ∉ transitiveClosure x := by
  sorry

theorem membership_not_transitive :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    z ∈ a ∧ a ∈ b ∧ z ∉ b ∧ ZFSet.IsTransitive ({z, a, b} : ZFSet.{u}) := by
  sorry

theorem no_finite_membership_cycle (n : ℕ) (f : Fin (n + 1) → ZFSet.{u}) :
    ¬ ∀ i, f (i + 1) ∈ f i := by
  sorry

def MembershipInduction {α : Type v} (M : α → α → Prop) : Prop :=
  ∀ P : α → Prop, (∀ x, (∀ y, M y x → P y) → P x) → ∀ x, P x

theorem foundation_of_induction {α : Type v} (M : α → α → Prop)
    (h : MembershipInduction M) (A : Set α) (hne : A.Nonempty) :
    ∃ a ∈ A, ∀ b ∈ A, ¬ M b a := by
  sorry

def LocalRankEquation (T : ZFSet.{u}) (r : T → Ordinal.{u}) : Prop :=
  ∀ x : T, r x = ⨆ y : {y : T // y.val ∈ x.val}, Order.succ (r y.val)

theorem local_rank_unique (T : ZFSet.{u}) (hT : T.IsTransitive) :
    ∃! r : T → Ordinal.{u}, LocalRankEquation T r := by
  sorry

theorem local_rank_agrees (T : ZFSet.{u}) (hT : T.IsTransitive)
    (r : T → Ordinal.{u}) (hr : LocalRankEquation T r) : ∀ x : T, r x = x.val.rank := by
  sorry

theorem rank_equation (x : ZFSet.{u}) :
    x.rank = ⨆ y : x, Order.succ y.val.rank := by
  sorry

theorem rank_zero_iff (x : ZFSet.{u}) : x.rank = 0 ↔ x = ∅ := by
  sorry

theorem rank_sUnion (x : ZFSet.{u}) : (ZFSet.sUnion x).rank = ⨆ y : x, y.val.rank := by
  sorry

theorem closure_rank (x : ZFSet.{u}) : (transitiveClosure x).rank = x.rank := by
  sorry

theorem rank_inclusion_not_strict :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    ({b} : ZFSet.{u}) ⊂ ({z, b} : ZFSet.{u}) ∧
      ({b} : ZFSet.{u}).rank = 3 ∧ ({z, b} : ZFSet.{u}).rank = 3 ∧
      ({a, b} : ZFSet.{u}).rank = 3 ∧ b.rank = 2 ∧ a.rank = 1 := by
  sorry

theorem ordinal_height_wellFounded {α : Type v} (R : α → α → Prop)
    (h : α → Ordinal.{u}) (hR : ∀ a b, R a b → h a < h b) : WellFounded R := by
  sorry

theorem singleton_ordinal_rank_size (a : Ordinal.{u}) :
    ({a.toZFSet} : ZFSet.{u}).card = 1 ∧
      ({a.toZFSet} : ZFSet.{u}).rank = a + 1 := by
  sorry

theorem omega_rank_size :
    ZFSet.omega.{u}.rank = Ordinal.omega0 ∧ ZFSet.omega.{u}.card = Cardinal.aleph0 ∧
    ({ZFSet.omega} : ZFSet.{u}).rank = Ordinal.omega0 + 1 ∧
    ({{ZFSet.omega}} : ZFSet.{u}).rank = Ordinal.omega0 + 2 ∧
    ({ZFSet.omega} : ZFSet.{u}).card = 1 ∧ ({{ZFSet.omega}} : ZFSet.{u}).card = 1 := by
  sorry

end Lemmatheca.Entry.FoundationAndRank
