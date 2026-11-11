import Lemmatheca.CountablyClosedForcing.Closure
import Lemmatheca.InfiniteTrees.InfiniteTrees
import Mathlib.SetTheory.Cardinal.Regular

namespace Lemmatheca.SetTheory.CountablyClosedForcing
open Set Order Ordinal Cardinal
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.InfiniteTrees
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Index := (ω₁ : Ordinal.{0}).ToType
abbrev Prefix := OrderDual (FunctionNode (ω₁ : Ordinal.{0}) Bool)
abbrev prefixOrder : PartialOrder Prefix := inferInstance
attribute [local instance] prefixOrder

def position (i : Index) : Ordinal := i.toOrd.val
def index (α : Ordinal) (hα : α < ω₁) : Index := Ordinal.ToType.mk ⟨α,hα⟩

theorem position_index (α : Ordinal) (hα : α < ω₁) : position (index α hα) = α := by
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply ⟨α,hα⟩)


theorem position_lt (i j : Index) : i < j ↔ position i < position j := by
  exact Ordinal.ToType.mk.symm.lt_iff_lt.symm


private theorem position_injective : Function.Injective position := by
  intro i j h
  exact Ordinal.ToType.mk.symm.injective (Subtype.ext h)

private theorem one_ne_empty : ({∅} : ZFSet) ≠ ∅ := by
  intro h
  have hm : (∅ : ZFSet) ∈ ({∅} : ZFSet) := by simp
  rw [h] at hm
  exact ZFSet.notMem_empty _ hm

private theorem bit_injective : Function.Injective (bitSet.{0}) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bitSet,one_ne_empty,Ne.symm one_ne_empty]

private theorem bit_mem (b : Bool) : bitSet b ∈ ({∅,{∅}} : ZFSet) := by
  cases b <;> simp [bitSet]

def prefixGraph (p : Prefix) : Set (Index × Bool) :=
  {z | ∃ h : z.1 < p.1, p.2 ⟨z.1,h⟩ = z.2}

def prefixSet (p : Prefix) : ZFSet :=
  ZFSet.range (fun i : Set.Iio p.1 =>
    ZFSet.pair (position i.val).toZFSet (bitSet (p.2 i)))

theorem prefix_order (p q : Prefix) : q ≤ p ↔ Extends p q := by
  rfl


theorem prefix_graph_order (p q : Prefix) : q ≤ p ↔ prefixGraph p ⊆ prefixGraph q := by
  constructor
  · rintro ⟨hle,he⟩ z ⟨hz,hbit⟩
    refine ⟨hz.trans_le hle,?_⟩
    exact (congrFun he ⟨z.1,hz⟩).symm.trans hbit
  · intro h
    have hle : p.1 ≤ q.1 := by
      by_contra hn
      have hlt := lt_of_not_ge hn
      obtain ⟨hh,_⟩ := h (show (q.1,p.2 ⟨q.1,hlt⟩) ∈ prefixGraph p from ⟨hlt,rfl⟩)
      exact (lt_irrefl q.1) hh
    refine ⟨hle,?_⟩
    funext i
    obtain ⟨hi,he⟩ := h (show (i.val,p.2 i) ∈ prefixGraph p from ⟨i.property,rfl⟩)
    exact he.symm


theorem prefix_graph_injective : Function.Injective prefixGraph := by
  intro p q h
  exact le_antisymm ((prefix_graph_order q p).mpr h.symm.subset)
    ((prefix_graph_order p q).mpr h.subset)


theorem prefix_set_members (p : Prefix) (z : ZFSet) : z ∈ prefixSet p ↔
    ∃ i : Index, ∃ h : i < p.1,
      z = ZFSet.pair (position i).toZFSet (bitSet (p.2 ⟨i,h⟩)) := by
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hz
    exact ⟨i.val,i.property,hi.symm⟩
  · rintro ⟨i,hi,rfl⟩
    exact ZFSet.mem_range_self (f := fun j : Set.Iio p.1 =>
      ZFSet.pair (position j.val).toZFSet (bitSet (p.2 j))) ⟨i,hi⟩


theorem prefix_set_function (p : Prefix) :
    ZFSet.IsFunc (position p.1).toZFSet {∅,{∅}} (prefixSet p) := by
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (prefix_set_members p z).mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr
      ((position_lt i p.1).mp hi),bit_mem _⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    let i := index a (ha.trans p.1.toOrd.property)
    have hi : i < p.1 := (position_lt i p.1).mpr (by simpa [i,position_index] using ha)
    have he : (position i).toZFSet = a.toZFSet := by simp only [i,position_index]
    refine ⟨bitSet (p.2 ⟨i,hi⟩),?_,?_⟩
    · rw [← he]
      exact (prefix_set_members p _).mpr ⟨i,hi,rfl⟩
    · intro w hw
      obtain ⟨j,hj,hpair⟩ := (prefix_set_members p _).mp hw
      obtain ⟨hpos,hval⟩ := ZFSet.pair_inj.mp hpair
      have hij : i = j := position_injective (by
        apply Ordinal.toZFSet_injective
        exact he.trans hpos)
      subst j
      exact hval


theorem prefix_set_injective : Function.Injective prefixSet := by
  intro p q h
  apply prefix_graph_injective
  ext ⟨i,b⟩
  have hp : (i,b) ∈ prefixGraph p ↔
      ZFSet.pair (position i).toZFSet (bitSet b) ∈ prefixSet p := by
    constructor
    · rintro ⟨hi,hb⟩
      exact (prefix_set_members p _).mpr ⟨i,hi,by rw [hb]⟩
    · intro hm
      obtain ⟨j,hj,he⟩ := (prefix_set_members p _).mp hm
      obtain ⟨hij,hb⟩ := ZFSet.pair_inj.mp he
      have heq := position_injective (Ordinal.toZFSet_injective hij)
      subst j
      exact ⟨hj,(bit_injective hb).symm⟩
  have hq : (i,b) ∈ prefixGraph q ↔
      ZFSet.pair (position i).toZFSet (bitSet b) ∈ prefixSet q := by
    constructor
    · rintro ⟨hi,hb⟩
      exact (prefix_set_members q _).mpr ⟨i,hi,by rw [hb]⟩
    · intro hm
      obtain ⟨j,hj,he⟩ := (prefix_set_members q _).mp hm
      obtain ⟨hij,hb⟩ := ZFSet.pair_inj.mp he
      have heq := position_injective (Ordinal.toZFSet_injective hij)
      subst j
      exact ⟨hj,(bit_injective hb).symm⟩
  rw [hp,hq,h]


def emptyPrefix : Prefix := ⟨index 0 (Ordinal.omega_pos 1), fun _ => false⟩

@[instance_reducible] def prefixOrderTop : OrderTop Prefix where
  top := emptyPrefix
  le_top := by
    intro p
    refine ⟨?_,?_⟩
    · apply le_of_not_gt
      intro h
      have hh := (position_lt p.1 emptyPrefix.1).mp h
      have hz : position emptyPrefix.1 = 0 := position_index _ _
      rw [hz] at hh
      exact not_lt_zero hh
    · funext i
      have hi := (position_lt i.val emptyPrefix.1).mp i.property
      have hz : position emptyPrefix.1 = 0 := position_index _ _
      rw [hz] at hi
      exact (not_lt_zero hi).elim
attribute [local instance] prefixOrderTop

theorem prefix_compatible (p q : Prefix) : Compatible p q ↔
    ∀ i : Index, ∀ hp : i < p.1, ∀ hq : i < q.1,
      p.2 ⟨i,hp⟩ = q.2 ⟨i,hq⟩ := by
  constructor
  · rintro ⟨r,hrp,hrq⟩ i hi hj
    exact (congrFun hrp.2 ⟨i,hi⟩).trans (congrFun hrq.2 ⟨i,hj⟩).symm
  · intro h
    rcases le_total p.1 q.1 with hpq | hqp
    · have hqp' : q ≤ p := ⟨hpq,by funext i; exact h i.val i.property (i.property.trans_le hpq)⟩
      exact ⟨q,hqp',le_rfl⟩
    · have hpq' : p ≤ q := ⟨hqp,by funext i; exact (h i.val (i.property.trans_le hqp) i.property).symm⟩
      exact ⟨p,le_rfl,hpq'⟩


theorem prefix_compatible_comparable (p q : Prefix) :
    Compatible p q ↔ p ≤ q ∨ q ≤ p := by
  constructor
  · intro h
    have he := (prefix_compatible p q).mp h
    rcases le_total p.1 q.1 with hpq | hqp
    · exact Or.inr ⟨hpq,by funext i; exact he i.val i.property (i.property.trans_le hpq)⟩
    · exact Or.inl ⟨hqp,by funext i; exact (he i.val (i.property.trans_le hqp) i.property).symm⟩
  · rintro (h | h)
    · exact ⟨p,le_rfl,h⟩
    · exact ⟨q,h,le_rfl⟩


def extendPrefix (p : Prefix) (δ : Index) (fill : Index → Bool) : Prefix :=
  ⟨δ, fun i => if hi : i.val < p.1 then p.2 ⟨i.val,hi⟩ else fill i.val⟩

theorem extend_prefix_spec (p : Prefix) (δ : Index) (fill : Index → Bool)
    (hp : p.1 ≤ δ) :
    (extendPrefix p δ fill).1 = δ ∧ extendPrefix p δ fill ≤ p := by
  rcases p with ⟨a,f⟩
  refine ⟨rfl,hp,?_⟩
  funext i
  change f i = if hi : i.val < a then f ⟨i.val,hi⟩ else fill i.val
  split
  · rfl
  · rename_i hn
    exact (hn i.property).elim



def longDomain (β : Index) : Set Prefix := {p | β < p.1}

theorem long_domain_dense (β : Index) : Dense (longDomain β) := by
  intro p
  let δ := index (max (position p.1) (position β + 1))
    (max_lt p.1.toOrd.property ((Cardinal.isSuccLimit_omega 1).add_one_lt β.toOrd.property))
  have hp : p.1 ≤ δ := le_of_not_gt (fun h => (not_lt_of_ge
    (show position p.1 ≤ position δ by simpa only [δ,position_index] using le_max_left (position p.1) (position β + 1)))
      ((position_lt δ p.1).mp h))
  refine ⟨extendPrefix p δ (fun _ => false),?_,(extend_prefix_spec p δ (fun _ => false) hp).2⟩
  change β < δ
  apply (position_lt β δ).mpr
  simp only [δ,position_index]
  exact (lt_add_one (position β)).trans_le (le_max_right _ _)


theorem union_length_bound (s : ℕ → Prefix) :
    (⨆ n, position (s n).1) < ω₁ := by
  exact Ordinal.iSup_lt_omega_one (fun n => (s n).1.toOrd.property)


def unionIndex (s : ℕ → Prefix) : Index :=
  index (⨆ n, position (s n).1) (union_length_bound s)

theorem union_index_cover (s : ℕ → Prefix) (i : Set.Iio (unionIndex s)) :
    ∃ n, i.val < (s n).1 := by
  have hi := (position_lt i.val (unionIndex s)).mp i.property
  change position i.val < position (index (⨆ n, position (s n).1) (union_length_bound s)) at hi
  rw [position_index] at hi
  obtain ⟨n,hn⟩ := Ordinal.lt_iSup_iff.mp hi
  exact ⟨n,(position_lt _ _).mpr hn⟩


def unionPrefix (s : ℕ → Prefix) : Prefix :=
  ⟨unionIndex s, fun i =>
    (s (Classical.choose (union_index_cover s i))).2
      ⟨i.val,Classical.choose_spec (union_index_cover s i)⟩⟩

private theorem descending_bits_eq (s : ℕ → Prefix) (hs : Antitone s)
    (i : Index) (n m : ℕ) (hn : i < (s n).1) (hm : i < (s m).1) :
    (s n).2 ⟨i,hn⟩ = (s m).2 ⟨i,hm⟩ := by
  have hnr := hs (le_max_left n m)
  have hmr := hs (le_max_right n m)
  exact (congrFun hnr.2 ⟨i,hn⟩).trans (congrFun hmr.2 ⟨i,hm⟩).symm

theorem union_prefix_graph (s : ℕ → Prefix) (hs : Antitone s) :
    prefixGraph (unionPrefix s) = ⋃ n, prefixGraph (s n) := by
  ext ⟨i,b⟩
  constructor
  · rintro ⟨hi,hb⟩
    let j : Set.Iio (unionIndex s) := ⟨i,hi⟩
    exact Set.mem_iUnion.mpr ⟨Classical.choose (union_index_cover s j),
      Classical.choose_spec (union_index_cover s j),hb⟩
  · intro hb
    obtain ⟨n,hn,hbit⟩ := Set.mem_iUnion.mp hb
    have hi : i < unionIndex s := (position_lt _ _).mpr (by
      simp only [unionIndex,position_index]
      exact ((position_lt _ _).mp hn).trans_le (Ordinal.le_iSup (fun n => position (s n).1) n))
    refine ⟨hi,?_⟩
    let j : Set.Iio (unionIndex s) := ⟨i,hi⟩
    exact (descending_bits_eq s hs i (Classical.choose (union_index_cover s j)) n
      (Classical.choose_spec (union_index_cover s j)) hn).trans hbit


theorem union_prefix_set (s : ℕ → Prefix) (hs : Antitone s) :
    prefixSet (unionPrefix s) = ZFSet.sUnion (ZFSet.range (fun n => prefixSet (s n))) := by
  ext z
  rw [ZFSet.mem_sUnion]
  constructor
  · intro hz
    obtain ⟨i,hi,rfl⟩ := (prefix_set_members (unionPrefix s) z).mp hz
    have hm : (i,(unionPrefix s).2 ⟨i,hi⟩) ∈ prefixGraph (unionPrefix s) := ⟨hi,rfl⟩
    rw [union_prefix_graph s hs] at hm
    obtain ⟨n,hn,hb⟩ := Set.mem_iUnion.mp hm
    refine ⟨prefixSet (s n),ZFSet.mem_range_self n,?_⟩
    exact (prefix_set_members (s n) _).mpr ⟨i,hn,by rw [hb]⟩
  · rintro ⟨x,hx,hz⟩
    obtain ⟨n,rfl⟩ := ZFSet.mem_range.mp hx
    obtain ⟨i,hi,rfl⟩ := (prefix_set_members (s n) z).mp hz
    have hm : (i,(s n).2 ⟨i,hi⟩) ∈ prefixGraph (unionPrefix s) := by
      rw [union_prefix_graph s hs]
      exact Set.mem_iUnion.mpr ⟨n,hi,rfl⟩
    obtain ⟨hu,hb⟩ := hm
    exact (prefix_set_members (unionPrefix s) _).mpr ⟨i,hu,by rw [hb]⟩


theorem union_prefix_lower_bound (s : ℕ → Prefix) (hs : Antitone s) :
    ∀ n, unionPrefix s ≤ s n := by
  intro n
  apply (prefix_graph_order _ _).mpr
  rw [union_prefix_graph s hs]
  intro z hz
  exact Set.mem_iUnion.mpr ⟨n,hz⟩


theorem prefix_countably_closed : CountablyClosed Prefix := by
  exact fun s hs => ⟨unionPrefix s,union_prefix_lower_bound s hs⟩


def genericGraph (G : PFilter Prefix) : Set (Index × Bool) :=
  {z | ∃ p ∈ G, z ∈ prefixGraph p}

def genericBits (G : PFilter Prefix) (i : Index) : Bool :=
  if hi : ∃ p : Prefix, p ∈ G ∧ i < p.1 then
    (Classical.choose hi).2 ⟨i,(Classical.choose_spec hi).2⟩ else false

theorem generic_graph_functional (G : PFilter Prefix) (i : Index) (b c : Bool)
    (hb : (i,b) ∈ genericGraph G) (hc : (i,c) ∈ genericGraph G) : b = c := by
  obtain ⟨p,hp,hi,hb'⟩ := hb
  obtain ⟨q,hq,hj,hc'⟩ := hc
  have he := (prefix_compatible p q).mp (filter_compatible G hp hq) i hi hj
  exact hb'.symm.trans (he.trans hc')


theorem generic_bits_spec (G : PFilter Prefix) (hd : ∀ i, Meets G (longDomain i)) :
    genericGraph G = Set.range (fun i => (i,genericBits G i)) ∧
    ∀ p ∈ G, ∀ i : Set.Iio p.1, genericBits G i.val = p.2 i := by
  have hbit (i : Index) : (i,genericBits G i) ∈ genericGraph G := by
    have hi : ∃ p : Prefix, p ∈ G ∧ i < p.1 := hd i
    rw [genericBits,dite_eq_left hi]
    exact ⟨Classical.choose hi,(Classical.choose_spec hi).1,
      (Classical.choose_spec hi).2,rfl⟩
  refine ⟨?_,?_⟩
  · ext ⟨i,b⟩
    constructor
    · intro hb
      exact ⟨i,Prod.ext rfl (generic_graph_functional G i _ _ (hbit i) hb)⟩
    · rintro ⟨j,hj⟩
      exact hj ▸ hbit j
  · intro p hp i
    exact generic_graph_functional G i.val _ _ (hbit i.val) ⟨p,hp,i.property,rfl⟩


end
end Lemmatheca.SetTheory.CountablyClosedForcing
