import Lemmatheca.CountablyClosedForcing.Blocks
import Lemmatheca.ManyCohenReals.Names

namespace Lemmatheca.SetTheory.CountablyClosedForcing
open Set Order Ordinal Cardinal
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.NaturalNumbersAsSets
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] prefixOrder prefixOrderTop

def prefixConditions : ZFSet := ZFSet.range prefixSet

def prefixCode : Prefix ≃ prefixConditions where
  toFun p := ⟨prefixSet p,ZFSet.mem_range_self p⟩
  invFun z := Classical.choose (ZFSet.mem_range.mp z.property)
  left_inv := by
    intro p
    apply prefix_set_injective
    exact Classical.choose_spec (ZFSet.mem_range.mp
      (ZFSet.mem_range_self (f := prefixSet) p))
  right_inv := by
    intro z
    apply Subtype.ext
    exact Classical.choose_spec (ZFSet.mem_range.mp z.property)


private theorem position_injective : Function.Injective position := by
  intro i j h
  exact Ordinal.ToType.mk.symm.injective (Subtype.ext h)

private theorem bit_mem (b : Bool) : bitSet b ∈ ({∅,{∅}} : ZFSet) := by
  cases b <;> simp [bitSet]

private theorem prefix_in_filter (G : PFilter Prefix) (p : Prefix) :
    (prefixCode p).val ∈ filterSet prefixConditions prefixCode G ↔ p ∈ G := by
  rw [filterSet_mem]
  constructor
  · rintro ⟨q, hq, he⟩
    have h : p = q := prefix_set_injective he
    exact h.symm ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

private theorem top_in_filter (G : PFilter Prefix) :
    (prefixCode ⊤).val ∈ filterSet prefixConditions prefixCode G :=
  (prefix_in_filter G ⊤).mpr (show (⊤ : Prefix) ∈ G from PFilter.top_mem)

private theorem op_check_value (G : PFilter Prefix) (a b : ZFSet) :
    evaluation (filterSet prefixConditions prefixCode G)
      (orderedPairName (prefixCode ⊤).val
        (checkName (prefixCode ⊤).val a) (checkName (prefixCode ⊤).val b)) =
      ZFSet.pair a b := by
  rw [orderedPairName_value _ _ _ _ (top_in_filter G),
    checkName_value _ _ _ (top_in_filter G), checkName_value _ _ _ (top_in_filter G)]

def prefixRelation : ZFSet :=
  ZFSet.range (fun qp : {qp : Prefix × Prefix // qp.1 ≤ qp.2} =>
    ZFSet.pair (prefixSet qp.val.1) (prefixSet qp.val.2))

theorem prefix_code_order (p q : Prefix) :
    ZFSet.pair (prefixCode q).val (prefixCode p).val ∈ prefixRelation ↔ q ≤ p := by
  rw [prefixRelation, ZFSet.mem_range]
  constructor
  · rintro ⟨qp, hqp⟩
    obtain ⟨hq, hp⟩ := ZFSet.pair_inj.mp hqp
    have hq' := prefix_set_injective hq
    have hp' := prefix_set_injective hp
    exact hq' ▸ hp' ▸ qp.property
  · intro hqp
    exact ⟨⟨(q, p), hqp⟩, rfl⟩

def unionName : ZFSet :=
  ZFSet.range (fun pi : {pi : Prefix × Index // pi.2 < pi.1.1} =>
    ZFSet.pair (orderedPairName (prefixCode ⊤).val
      (checkName (prefixCode ⊤).val (position pi.val.2).toZFSet)
      (checkName (prefixCode ⊤).val (bitSet (pi.val.1.2 ⟨pi.val.2,pi.property⟩))))
      (prefixCode pi.val.1).val)

def unionSet (G : PFilter Prefix) : ZFSet :=
  ZFSet.sUnion (ZFSet.range (fun p : G => prefixSet p.val))

def genericSet (G : PFilter Prefix) : ZFSet :=
  ZFSet.range (fun i : Index =>
    ZFSet.pair (position i).toZFSet (bitSet (genericBits G i)))

theorem union_name_valid : IsName prefixConditions unionName := by
  apply (isName_iff prefixConditions _).mpr
  intro z hz
  obtain ⟨pi, rfl⟩ := ZFSet.mem_range.mp hz
  have ht : (prefixCode ⊤).val ∈ prefixConditions := (prefixCode ⊤).property
  exact ⟨_, (prefixCode pi.val.1).val, rfl, (prefixCode pi.val.1).property,
    orderedPairName_isName prefixConditions _ _ _ ht
      (checkName_isName prefixConditions _ _ ht) (checkName_isName prefixConditions _ _ ht)⟩

theorem union_name_value (G : PFilter Prefix) :
    evaluation (filterSet prefixConditions prefixCode G) unionName = unionSet G := by
  ext x
  rw [evaluation_mem, unionSet, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨σ, q, hσq, hq, he⟩
    obtain ⟨pi, hpi⟩ := ZFSet.mem_range.mp hσq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp hpi
    have hp := (prefix_in_filter G pi.val.1).mp hq
    refine ⟨prefixSet pi.val.1,
      ZFSet.mem_range_self (f := fun p : G => prefixSet p.val) ⟨pi.val.1, hp⟩, ?_⟩
    rw [he, op_check_value]
    exact (prefix_set_members pi.val.1 _).mpr ⟨pi.val.2, pi.property, rfl⟩
  · rintro ⟨z, hz, hx⟩
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.mp hz
    obtain ⟨i, hi, rfl⟩ := (prefix_set_members p.val x).mp hx
    refine ⟨_, (prefixCode p.val).val,
      ZFSet.mem_range_self (f := fun pi : {pi : Prefix × Index // pi.2 < pi.1.1} =>
        ZFSet.pair (orderedPairName (prefixCode ⊤).val
          (checkName (prefixCode ⊤).val (position pi.val.2).toZFSet)
          (checkName (prefixCode ⊤).val (bitSet (pi.val.1.2 ⟨pi.val.2, pi.property⟩))))
          (prefixCode pi.val.1).val) ⟨(p.val, i), hi⟩,
      (prefix_in_filter G p.val).mpr p.property, ?_⟩
    exact (op_check_value G _ _).symm

theorem union_set_generic_set (G : PFilter Prefix)
    (hd : ∀ i, Meets G (longDomain i)) : unionSet G = genericSet G := by
  ext x
  rw [unionSet, ZFSet.mem_sUnion, genericSet, ZFSet.mem_range]
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.mp hz
    obtain ⟨i, hi, he⟩ := (prefix_set_members p.val x).mp hx
    refine ⟨i, ?_⟩
    rw [(generic_bits_spec G hd).2 p.val p.property ⟨i, hi⟩]
    exact he.symm
  · rintro ⟨i, hi⟩
    obtain ⟨p, hp, hpi⟩ := hd i
    refine ⟨prefixSet p,
      ZFSet.mem_range_self (f := fun p : G => prefixSet p.val) ⟨p, hp⟩, ?_⟩
    apply (prefix_set_members p _).mpr
    refine ⟨i, hpi, ?_⟩
    rw [(generic_bits_spec G hd).2 p hp ⟨i, hpi⟩] at hi
    exact hi.symm

theorem generic_set_function (G : PFilter Prefix) :
    ZFSet.IsFunc (ω₁ : Ordinal.{0}).toZFSet {∅,{∅}} (genericSet G) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr i.toOrd.property, bit_mem _⟩
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    let i := index a ha
    have he : (position i).toZFSet = a.toZFSet := by simp only [i, position_index]
    refine ⟨bitSet (genericBits G i), ?_, ?_⟩
    · rw [← he]
      exact ZFSet.mem_range_self i
    · intro w hw
      obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hw
      obtain ⟨hpos, hval⟩ := ZFSet.pair_inj.mp hj
      have hij : i = j := position_injective (Ordinal.toZFSet_injective (he.trans hpos.symm))
      subst j
      exact hval.symm

def blockName (α : Index) : ZFSet :=
  ZFSet.range (fun pn : {pn : Prefix × ℕ // blockIndex α pn.2 < pn.1.1} =>
    ZFSet.pair (orderedPairName (prefixCode ⊤).val
      (checkName (prefixCode ⊤).val (naturalSet pn.val.2))
      (checkName (prefixCode ⊤).val
        (bitSet (pn.val.1.2 ⟨blockIndex α pn.val.2,pn.property⟩))))
      (prefixCode pn.val.1).val)

theorem block_name_valid (α : Index) : IsName prefixConditions (blockName α) := by
  apply (isName_iff prefixConditions _).mpr
  intro z hz
  obtain ⟨pn, rfl⟩ := ZFSet.mem_range.mp hz
  have ht : (prefixCode ⊤).val ∈ prefixConditions := (prefixCode ⊤).property
  exact ⟨_, (prefixCode pn.val.1).val, rfl, (prefixCode pn.val.1).property,
    orderedPairName_isName prefixConditions _ _ _ ht
      (checkName_isName prefixConditions _ _ ht) (checkName_isName prefixConditions _ _ ht)⟩

theorem block_name_value (G : PFilter Prefix) (hd : ∀ i, Meets G (longDomain i))
    (α : Index) : evaluation (filterSet prefixConditions prefixCode G) (blockName α) =
      binarySequenceSet (blockReal G α) := by
  ext x
  rw [evaluation_mem, binarySequenceSet, ZFSet.mem_range]
  constructor
  · rintro ⟨σ, q, hσq, hq, he⟩
    obtain ⟨pn, hpn⟩ := ZFSet.mem_range.mp hσq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp hpn
    have hp := (prefix_in_filter G pn.val.1).mp hq
    refine ⟨pn.val.2, ?_⟩
    rw [blockReal, (generic_bits_spec G hd).2 pn.val.1 hp ⟨blockIndex α pn.val.2, pn.property⟩]
    exact (he.trans (op_check_value G _ _)).symm
  · rintro ⟨n, hn⟩
    obtain ⟨p, hp, hi⟩ := hd (blockIndex α n)
    refine ⟨_, (prefixCode p).val,
      ZFSet.mem_range_self (f := fun pn : {pn : Prefix × ℕ // blockIndex α pn.2 < pn.1.1} =>
        ZFSet.pair (orderedPairName (prefixCode ⊤).val
          (checkName (prefixCode ⊤).val (naturalSet pn.val.2))
          (checkName (prefixCode ⊤).val (bitSet (pn.val.1.2 ⟨blockIndex α pn.val.2, pn.property⟩))))
          (prefixCode pn.val.1).val) ⟨(p, n), hi⟩,
      (prefix_in_filter G p).mpr hp, ?_⟩
    rw [op_check_value]
    simpa only [blockReal, (generic_bits_spec G hd).2 p hp ⟨blockIndex α n, hi⟩] using hn.symm

def ordinalIndex (α : (ω₁ : Ordinal.{0}).toZFSet) : Index :=
  index α.val.rank (by
    obtain ⟨a, ha, he⟩ := Ordinal.mem_toZFSet_iff.mp α.property
    rw [← he, Ordinal.rank_toZFSet]
    exact ha)

theorem ordinal_index_value (α : (ω₁ : Ordinal.{0}).toZFSet) :
    (position (ordinalIndex α)).toZFSet = α.val := by
  rw [ordinalIndex, position_index]
  obtain ⟨a, ha, he⟩ := Ordinal.mem_toZFSet_iff.mp α.property
  rw [← he, Ordinal.rank_toZFSet]

def listingName : ZFSet :=
  Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName
    (ω₁ : Ordinal.{0}).toZFSet (prefixCode ⊤).val
    (fun α => blockName (ordinalIndex α))

theorem listing_name_valid : IsName prefixConditions listingName := by
  exact Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName_isName
    prefixConditions (ω₁ : Ordinal.{0}).toZFSet (prefixCode ⊤).val
    (fun α => blockName (ordinalIndex α)) (prefixCode ⊤).property
    (fun α => block_name_valid (ordinalIndex α))

theorem listing_name_value (G : PFilter Prefix) (hd : ∀ i, Meets G (longDomain i)) :
    evaluation (filterSet prefixConditions prefixCode G) listingName = listingGraph G := by
  rw [listingName, Lemmatheca.SetTheory.ManyCohenReals.indexedFamilyName_value
    _ _ _ _ (top_in_filter G)]
  ext x
  rw [ZFSet.mem_range, listingGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨ordinalIndex α, ?_⟩
    rw [ordinal_index_value]
    rw [block_name_value G hd] at hα
    exact hα
  · rintro ⟨i, hi⟩
    let α : (ω₁ : Ordinal.{0}).toZFSet :=
      ⟨(position i).toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr i.toOrd.property⟩
    have he : ordinalIndex α = i :=
      position_injective (Ordinal.toZFSet_injective (ordinal_index_value α))
    refine ⟨α, ?_⟩
    rw [block_name_value G hd, he]
    exact hi

theorem listing_graph_in_extension (M : ZFSet) (G : PFilter Prefix)
    (hm : listingName ∈ M) (hd : ∀ i, Meets G (longDomain i)) :
    listingGraph G ∈ extension prefixConditions M (filterSet prefixConditions prefixCode G) := by
  exact (extension_mem _ _ _ _).mpr
    ⟨listingName, hm, listing_name_valid, listing_name_value G hd⟩

theorem union_graph_in_extension (M : ZFSet) (G : PFilter Prefix)
    (hm : unionName ∈ M) (hd : ∀ i, Meets G (longDomain i)) :
    genericSet G ∈ extension prefixConditions M (filterSet prefixConditions prefixCode G) := by
  exact (extension_mem _ _ _ _).mpr
    ⟨unionName, hm, union_name_valid, (union_name_value G).trans (union_set_generic_set G hd)⟩

end
end Lemmatheca.SetTheory.CountablyClosedForcing
