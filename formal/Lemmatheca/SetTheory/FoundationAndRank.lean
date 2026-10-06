import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic

/-! Reusable FoundationAndRank definitions and results. -/

set_option autoImplicit false

/-! Transitive closure uses the entry's superset convention, so it does not
automatically contain its input as a member. Local rank functions use small
membership subtypes; their values live in `Ordinal.{u}`. -/
namespace Lemmatheca.SetTheory.FoundationAndRank
open scoped ZFSet Ordinal
universe u v

def closureStage (x : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => x
  | n + 1 => closureStage x n ∪ ZFSet.sUnion (closureStage x n)

-- Lift the entire explicit pre-set construction through the quotient once.
-- No representatives are selected independently for the countable family.

private def preClosureStage (x : PSet.{u}) : ℕ → PSet.{u}
  | 0 => x
  | n + 1 => PSet.sUnion ({preClosureStage x n, PSet.sUnion (preClosureStage x n)} : PSet)

private theorem preClosureStage_mk (x : PSet.{u}) (n : ℕ) :
    ZFSet.mk (preClosureStage x n) = closureStage (ZFSet.mk x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ZFSet.mk (preClosureStage x n) ∪ ZFSet.sUnion (ZFSet.mk (preClosureStage x n)) = _
    rw [ih]
    rfl

private def preClosure (x : PSet.{u}) : PSet.{u} :=
  ⟨Σ n : ULift ℕ, (preClosureStage x n.down).Type,
    fun p => (preClosureStage x p.1.down).Func p.2⟩

private theorem mem_preClosure (x : PSet.{u}) (z : ZFSet.{u}) :
    z ∈ ZFSet.mk (preClosure x) ↔ ∃ n, z ∈ closureStage (ZFSet.mk x) n := by
  induction z using Quotient.inductionOn with
  | _ z =>
    simp only [← preClosureStage_mk]
    change (∃ i : (Σ n : ULift ℕ, (preClosureStage x n.down).Type),
      PSet.Equiv z ((preClosureStage x i.1.down).Func i.2)) ↔
      ∃ n : ℕ, ∃ i, PSet.Equiv z ((preClosureStage x n).Func i)
    exact ⟨fun ⟨⟨n,i⟩,h⟩ => ⟨n.down,i,h⟩,
      fun ⟨n,i,h⟩ => ⟨⟨⟨n⟩,i⟩,h⟩⟩

def transitiveClosure (x : ZFSet.{u}) : ZFSet.{u} :=
  Quotient.lift (fun a => ZFSet.mk (preClosure a)) (fun a b h => by
    apply ZFSet.ext
    intro z
    rw [mem_preClosure,mem_preClosure,ZFSet.sound h]) x

theorem mem_transitiveClosure {x z : ZFSet.{u}} :
    z ∈ transitiveClosure x ↔ ∃ n, z ∈ closureStage x n := by
  induction x using Quotient.inductionOn with
  | _ x => exact mem_preClosure x z

def IsTransitiveClosure (x T : ZFSet.{u}) : Prop :=
  T.IsTransitive ∧ x ⊆ T ∧ ∀ U, U.IsTransitive → x ⊆ U → T ⊆ U

theorem transitiveClosure_spec (x : ZFSet.{u}) :
    IsTransitiveClosure x (transitiveClosure x) := by
  have hb : x ⊆ transitiveClosure x := fun z hz => mem_transitiveClosure.mpr ⟨0, hz⟩
  refine ⟨?_,hb,?_⟩
  · intro y hy z hz
    obtain ⟨n,hn⟩ := mem_transitiveClosure.mp hy
    exact mem_transitiveClosure.mpr ⟨n+1,ZFSet.mem_union.mpr
      (Or.inr (ZFSet.mem_sUnion_of_mem hz hn))⟩
  · intro U hU hx z hz
    obtain ⟨n,hn⟩ := mem_transitiveClosure.mp hz
    have hc : ∀ k, closureStage x k ⊆ U := by
      intro k
      induction k with
      | zero => exact hx
      | succ k ih =>
        intro w hw
        rcases ZFSet.mem_union.mp hw with hw | hw
        · exact ih hw
        · obtain ⟨v,hv,hw⟩ := ZFSet.mem_sUnion.mp hw
          exact hU v (ih hv) hw
    exact hc n hn

theorem transitiveClosure_unique (x : ZFSet.{u}) : ∃! T, IsTransitiveClosure x T := by
  refine ⟨transitiveClosure x, transitiveClosure_spec x, ?_⟩
  intro T hT
  exact le_antisymm (hT.2.2 _ (transitiveClosure_spec x).1 (transitiveClosure_spec x).2.1)
    ((transitiveClosure_spec x).2.2 T hT.1 hT.2.1)

theorem transitiveClosure_fixed (T : ZFSet.{u}) (hT : T.IsTransitive) :
    transitiveClosure T = T := by
  exact le_antisymm ((transitiveClosure_spec T).2.2 T hT (le_refl _))
    (transitiveClosure_spec T).2.1

theorem no_finite_membership_cycle (n : ℕ) (f : Fin (n + 1) → ZFSet.{u}) :
    ¬ ∀ i, f (i + 1) ∈ f i := by
  intro hf
  have h : ∀ a : ZFSet.{u}, ∀ i, f i = a → False := by
    intro a
    induction a using ZFSet.inductionOn with
    | _ a ih =>
      intro i hi
      exact ih (f (i + 1)) (hi ▸ hf i) (i + 1) rfl
  exact h (f 0) 0 rfl

def MembershipInduction {α : Type v} (M : α → α → Prop) : Prop :=
  ∀ P : α → Prop, (∀ x, (∀ y, M y x → P y) → P x) → ∀ x, P x

theorem foundation_of_induction {α : Type v} (M : α → α → Prop)
    (h : MembershipInduction M) (A : Set α) (hne : A.Nonempty) :
    ∃ a ∈ A, ∀ b ∈ A, ¬ M b a := by
  classical
  by_contra! hn
  have hout : ∀ x, x ∉ A := h (fun x => x ∉ A) (by
    intro x hx hxin
    obtain ⟨y,hy,hM⟩ := hn x hxin
    exact hx y hM hy)
  obtain ⟨a,ha⟩ := hne
  exact hout a ha

def LocalRankEquation (T : ZFSet.{u}) (r : T → Ordinal.{u}) : Prop :=
  ∀ x : T, r x = ⨆ y : {y : T // y.val ∈ x.val}, Order.succ (r y.val)

theorem rank_equation (x : ZFSet.{u}) :
    x.rank = ⨆ y : x, Order.succ y.val.rank := by
  apply le_antisymm
  · apply ZFSet.rank_le_iff.mpr
    intro y hy
    exact (Order.lt_succ y.rank).trans_le
      (Ordinal.le_iSup (fun z : x => Order.succ z.val.rank) ⟨y,hy⟩)
  · exact Ordinal.iSup_le fun y => Order.succ_le_of_lt (ZFSet.rank_lt_of_mem y.property)

theorem local_rank_agrees (T : ZFSet.{u}) (hT : T.IsTransitive)
    (r : T → Ordinal.{u}) (hr : LocalRankEquation T r) : ∀ x : T, r x = x.val.rank := by
  have aux : ∀ a : ZFSet.{u}, ∀ ha : a ∈ T, r ⟨a,ha⟩ = a.rank := by
    intro a
    induction a using ZFSet.inductionOn with
    | _ a ih =>
      intro ha
      rw [hr ⟨a,ha⟩,rank_equation a]
      apply le_antisymm
      · apply Ordinal.iSup_le
        intro y
        rw [ih y.val.val y.property y.val.property]
        exact Ordinal.le_iSup (fun z : a => Order.succ z.val.rank) ⟨y.val.val,y.property⟩
      · apply Ordinal.iSup_le
        intro y
        rw [← ih y.val y.property (hT a ha y.property)]
        exact Ordinal.le_iSup (fun z : {z : T // z.val ∈ a} => Order.succ (r z.val))
          ⟨⟨y.val,hT a ha y.property⟩,y.property⟩
  intro x
  exact aux x.val x.property

theorem local_rank_unique (T : ZFSet.{u}) (hT : T.IsTransitive) :
    ∃! r : T → Ordinal.{u}, LocalRankEquation T r := by
  have hh : LocalRankEquation T (fun x => x.val.rank) := by
    intro x
    change x.val.rank = ⨆ y : {y : T // y.val ∈ x.val}, Order.succ y.val.val.rank
    rw [rank_equation x.val]
    apply le_antisymm
    · apply Ordinal.iSup_le
      intro y
      exact Ordinal.le_iSup (fun z : {z : T // z.val ∈ x.val} => Order.succ z.val.val.rank)
        ⟨⟨y.val,hT x.val x.property y.property⟩,y.property⟩
    · apply Ordinal.iSup_le
      intro y
      exact Ordinal.le_iSup (fun z : x.val => Order.succ z.val.rank) ⟨y.val.val,y.property⟩
  exact ⟨_,hh,fun r hr => funext (local_rank_agrees T hT r hr)⟩

theorem rank_zero_iff (x : ZFSet.{u}) : x.rank = 0 ↔ x = ∅ := by
  constructor
  · intro h
    apply (ZFSet.eq_empty x).mpr
    intro y hy
    have hh := ZFSet.rank_lt_of_mem hy
    rw [h] at hh
    exact not_lt_of_ge zero_le hh
  · rintro rfl
    exact ZFSet.rank_empty

theorem rank_sUnion (x : ZFSet.{u}) : (ZFSet.sUnion x).rank = ⨆ y : x, y.val.rank := by
  apply le_antisymm
  · apply ZFSet.rank_le_iff.mpr
    intro y hy
    obtain ⟨z,hz,hy⟩ := ZFSet.mem_sUnion.mp hy
    exact (ZFSet.rank_lt_of_mem hy).trans_le (Ordinal.le_iSup (fun z : x => z.val.rank) ⟨z,hz⟩)
  · apply Ordinal.iSup_le
    intro y
    exact ZFSet.rank_mono (fun z hz => ZFSet.mem_sUnion_of_mem hz y.property)

theorem closure_rank (x : ZFSet.{u}) : (transitiveClosure x).rank = x.rank := by
  have hs : ∀ n, (closureStage x n).rank = x.rank := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (closureStage x n ∪ ZFSet.sUnion (closureStage x n)).rank = x.rank
      rw [ZFSet.rank_union,max_eq_left (ZFSet.rank_sUnion_le _),ih]
  have he : transitiveClosure x = ZFSet.iUnion (closureStage x) := by
    apply ZFSet.ext
    intro z
    rw [mem_transitiveClosure, ZFSet.mem_iUnion]
  rw [he]
  simp [ZFSet.rank_iUnion, hs]

theorem ordinal_height_wellFounded {α : Type v} (R : α → α → Prop)
    (h : α → Ordinal.{u}) (hR : ∀ a b, R a b → h a < h b) : WellFounded R := by
  exact (Ordinal.lt_wf.onFun (f := h)).mono hR

theorem singleton_ordinal_rank_size (a : Ordinal.{u}) :
    ({a.toZFSet} : ZFSet.{u}).card = 1 ∧
      ({a.toZFSet} : ZFSet.{u}).rank = a + 1 := by
  constructor
  · exact ZFSet.card_singleton
  · simp [Order.succ_eq_add_one]

end Lemmatheca.SetTheory.FoundationAndRank
