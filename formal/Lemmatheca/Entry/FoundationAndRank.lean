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

theorem membership_not_transitive :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    z ∈ a ∧ a ∈ b ∧ z ∉ b ∧ ZFSet.IsTransitive ({z, a, b} : ZFSet.{u}) := by
  dsimp
  refine ⟨by simp,by simp,?_,?_⟩
  · simp only [ZFSet.mem_singleton]
    intro h
    have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
    rw [← h] at hm
    exact ZFSet.notMem_empty _ hm
  · intro y hy z hz
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · exact (ZFSet.notMem_empty z hz).elim
    · exact Or.inl (ZFSet.mem_singleton.mp hz)
    · exact Or.inr (Or.inl (ZFSet.mem_singleton.mp hz))

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
    exact ((show y.rank < Order.succ y.rank from by simpa [Order.succ_eq_add_one] using (lt_add_one y.rank))).trans_le
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

theorem rank_inclusion_not_strict :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    ({b} : ZFSet.{u}) ⊂ ({z, b} : ZFSet.{u}) ∧
      ({b} : ZFSet.{u}).rank = 3 ∧ ({z, b} : ZFSet.{u}).rank = 3 ∧
      ({a, b} : ZFSet.{u}).rank = 3 ∧ b.rank = 2 ∧ a.rank = 1 := by
  dsimp
  have hs : (∅ : ZFSet.{u}) ≠ ({{∅}} : ZFSet.{u}) := by
    intro h
    have hm : ({∅} : ZFSet.{u}) ∈ ({{∅}} : ZFSet.{u}) := by simp
    rw [← h] at hm
    exact ZFSet.notMem_empty _ hm
  have ht : ({{{∅}}} : ZFSet.{u}) ⊂ ({∅,{{∅}}} : ZFSet.{u}) := by
    change ({{{∅}}} : ZFSet.{u}) ≤ ({∅,{{∅}}} : ZFSet.{u}) ∧
      ¬ ({∅,{{∅}}} : ZFSet.{u}) ≤ ({{{∅}}} : ZFSet.{u})
    constructor
    · intro y hy
      exact ZFSet.mem_pair.mpr (Or.inr (ZFSet.mem_singleton.mp hy))
    · intro h
      exact hs (ZFSet.mem_singleton.mp (h (ZFSet.mem_pair.mpr (Or.inl rfl))))
  refine ⟨ht,?_,?_,?_,?_,?_⟩ <;>
    norm_num [ZFSet.rank_pair,Order.succ_eq_add_one]

theorem ordinal_height_wellFounded {α : Type v} (R : α → α → Prop)
    (h : α → Ordinal.{u}) (hR : ∀ a b, R a b → h a < h b) : WellFounded R := by
  exact (Ordinal.lt_wf.onFun (f := h)).mono hR

theorem singleton_ordinal_rank_size (a : Ordinal.{u}) :
    ({a.toZFSet} : ZFSet.{u}).card = 1 ∧
      ({a.toZFSet} : ZFSet.{u}).rank = a + 1 := by
  constructor
  · exact ZFSet.card_singleton
  · simp [Order.succ_eq_add_one]

theorem omega_rank_size :
    ZFSet.omega.{u}.rank = Ordinal.omega0 ∧ ZFSet.omega.{u}.card = Cardinal.aleph0 ∧
    ({ZFSet.omega} : ZFSet.{u}).rank = Ordinal.omega0 + 1 ∧
    ({{ZFSet.omega}} : ZFSet.{u}).rank = Ordinal.omega0 + 2 ∧
    ({ZFSet.omega} : ZFSet.{u}).card = 1 ∧ ({{ZFSet.omega}} : ZFSet.{u}).card = 1 := by
  rw [Lemmatheca.Entry.NaturalNumbersAsSets.omega_eq_ordinal]
  norm_num [Order.succ_eq_add_one,Ordinal.card_toZFSet,Ordinal.card_omega0,add_assoc]

theorem closure_examples :
    let z : ZFSet.{u} := ∅
    let a : ZFSet.{u} := {z}
    let b : ZFSet.{u} := {a}
    let x : ZFSet.{u} := {a, b}
    transitiveClosure x = {z, a, b} ∧ transitiveClosure ({x} : ZFSet.{u}) = {z, a, b, x} ∧
      transitiveClosure (∅ : ZFSet.{u}) = ∅ ∧ x ∉ transitiveClosure x := by
  dsimp
  let z : ZFSet.{u} := ∅
  let a : ZFSet.{u} := {z}
  let b : ZFSet.{u} := {a}
  let x : ZFSet.{u} := {a,b}
  let T : ZFSet.{u} := {z,a,b}
  let U : ZFSet.{u} := {z,a,b,x}
  have hT : T.IsTransitive := membership_not_transitive.2.2.2
  have hU : U.IsTransitive := by
    intro y hy w hw
    change y ∈ ({z,a,b,x} : ZFSet.{u}) at hy
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (ZFSet.notMem_empty w hw).elim
    · have he := ZFSet.mem_singleton.mp hw
      rw [he]
      simp [U]
    · have he := ZFSet.mem_singleton.mp hw
      rw [he]
      simp [U]
    · rcases ZFSet.mem_pair.mp hw with rfl | rfl <;> simp [U]
  have hc := transitiveClosure_spec x
  have hc' := transitiveClosure_spec ({x} : ZFSet.{u})
  have ha : a ∈ transitiveClosure x := hc.2.1 (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hb : b ∈ transitiveClosure x := hc.2.1 (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hz : z ∈ transitiveClosure x := hc.1 a ha (ZFSet.mem_singleton.mpr rfl)
  have hX : transitiveClosure x = T := by
    apply le_antisymm
    · apply hc.2.2 T hT
      intro y hy
      rcases ZFSet.mem_pair.mp hy with rfl | rfl <;> simp [T]
    · intro y hy
      change y ∈ ({z,a,b} : ZFSet.{u}) at hy
      simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact hz
      · exact ha
      · exact hb
  have hx' : x ∈ transitiveClosure ({x} : ZFSet.{u}) := hc'.2.1 (ZFSet.mem_singleton.mpr rfl)
  have hinc : transitiveClosure x ⊆ transitiveClosure ({x} : ZFSet.{u}) :=
    hc.2.2 _ hc'.1 (hc'.1 x hx')
  have hX' : transitiveClosure ({x} : ZFSet.{u}) = U := by
    apply le_antisymm
    · apply hc'.2.2 U hU
      intro y hy
      rw [ZFSet.mem_singleton.mp hy]
      simp [U]
    · intro y hy
      change y ∈ ({z,a,b,x} : ZFSet.{u}) at hy
      simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hinc hz
      · exact hinc ha
      · exact hinc hb
      · exact hx'
  refine ⟨hX,hX',transitiveClosure_fixed ∅ ZFSet.isTransitive_empty,?_⟩
  intro hx
  rw [hX] at hx
  change x ∈ ({z,a,b} : ZFSet.{u}) at hx
  simp only [ZFSet.mem_insert_iff,ZFSet.mem_singleton] at hx
  have hax : a ∈ x := ZFSet.mem_pair.mpr (Or.inl rfl)
  have hbx : b ∈ x := ZFSet.mem_pair.mpr (Or.inr rfl)
  rcases hx with he | he | he
  · rw [he] at hax
    exact ZFSet.notMem_empty a hax
  · rw [he] at hbx
    have hbz : b = z := ZFSet.mem_singleton.mp hbx
    have hab : a ∈ b := ZFSet.mem_singleton.mpr rfl
    rw [hbz] at hab
    exact ZFSet.notMem_empty a hab
  · rw [he] at hbx
    exact ZFSet.mem_irrefl b hbx

end Lemmatheca.Entry.FoundationAndRank
