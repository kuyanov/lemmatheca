import Lemmatheca.CountablyClosedForcing.Prefixes

namespace Lemmatheca.SetTheory.CountablyClosedForcing
open Set Order Ordinal Cardinal
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingNames
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] prefixOrder prefixOrderTop

def blockPosition (α : Index) (n : ℕ) : Ordinal := ω * position α + n

theorem block_position_bound (α : Index) (n : ℕ) : blockPosition α n < ω₁ := by
  have ha : (position α).card ≤ (ℵ₀ : Cardinal) :=
    Cardinal.card_le_iff.mpr (by simpa only [Cardinal.succ_aleph0,Cardinal.ord_aleph,position,Set.mem_Iio] using α.toOrd.property)
  have hc : (ω * position α + n).card ≤ (ℵ₀ : Cardinal) := by
    rw [Ordinal.card_add,Ordinal.card_mul,Ordinal.card_omega0,Ordinal.card_nat]
    calc
      ℵ₀ * (position α).card + n ≤ ℵ₀ * ℵ₀ + ℵ₀ :=
        by gcongr; exact Cardinal.natCast_le_aleph0
      _ = ℵ₀ := by simp
  simpa [blockPosition] using (Cardinal.card_le_iff.mp hc)


def blockIndex (α : Index) (n : ℕ) : Index :=
  index (blockPosition α n) (block_position_bound α n)

theorem block_index_injective (α : Index) : Function.Injective (blockIndex α) := by
  intro n m h
  have he := congrArg position h
  simp only [blockIndex,position_index,blockPosition] at he
  exact_mod_cast (add_left_cancel he)


theorem block_end_bound (α : Index) : ω * (position α + 1) < ω₁ := by
  have ha : (position α).card ≤ (ℵ₀ : Cardinal) :=
    Cardinal.card_le_iff.mpr (by simpa only [Cardinal.succ_aleph0,Cardinal.ord_aleph,position,Set.mem_Iio] using α.toOrd.property)
  have hc : (ω * (position α + 1)).card ≤ (ℵ₀ : Cardinal) := by
    rw [mul_add_one,Ordinal.card_add,Ordinal.card_mul,Ordinal.card_omega0]
    calc
      ℵ₀ * (position α).card + ℵ₀ ≤ ℵ₀ * ℵ₀ + ℵ₀ := by gcongr
      _ = ℵ₀ := by simp
  simpa using Cardinal.card_le_iff.mp hc


theorem block_before_end (α : Index) (n : ℕ) :
    blockPosition α n < ω * (position α + 1) := by
  rw [blockPosition,mul_add_one]
  exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 n)


theorem successor_position_bound (p : Prefix) : position p.1 + 1 < ω₁ := by
  exact (Cardinal.isSuccLimit_omega 1).add_one_lt p.1.toOrd.property


def freshBlock (p : Prefix) : Index :=
  index (position p.1 + 1) (successor_position_bound p)

theorem fresh_block_gap (p : Prefix) :
    position p.1 < ω * position (freshBlock p) := by
  rw [freshBlock,position_index]
  exact (lt_add_one (position p.1)).trans_le (Ordinal.le_mul_right _ Ordinal.omega0_pos)


def Codes (p : Prefix) (α : Index) (r : ℕ → Bool) : Prop :=
  ∀ n, ∃ h : blockIndex α n < p.1, p.2 ⟨blockIndex α n,h⟩ = r n

def codingPrefix (p : Prefix) (r : ℕ → Bool) : Prefix :=
  ⟨index (ω * (position (freshBlock p) + 1)) (block_end_bound (freshBlock p)),
    fun i => if hi : i.val < p.1 then p.2 ⟨i.val,hi⟩
      else if hn : ∃ n, blockIndex (freshBlock p) n = i.val then r (Classical.choose hn)
      else false⟩

theorem coding_prefix_spec (p : Prefix) (r : ℕ → Bool) :
    codingPrefix p r ≤ p ∧ Codes (codingPrefix p r) (freshBlock p) r := by
  have hlen : position p.1 < ω * (position (freshBlock p) + 1) :=
    (fresh_block_gap p).trans (by
      have hb := block_before_end (freshBlock p) 0
      simpa only [blockPosition,Nat.cast_zero,add_zero] using hb)
  have hle : p.1 ≤ (codingPrefix p r).1 := le_of_lt ((position_lt _ _).mpr (by
    simpa only [codingPrefix,position_index] using hlen))
  refine ⟨⟨hle,?_⟩,?_⟩
  · funext i
    change p.2 i = if hi : i.val < p.1 then p.2 ⟨i.val,hi⟩ else _
    split
    · rfl
    · rename_i hn
      exact (hn i.property).elim
  · intro n
    have hb : blockIndex (freshBlock p) n < (codingPrefix p r).1 :=
      (position_lt _ _).mpr (by
        simpa only [blockIndex,codingPrefix,position_index] using block_before_end (freshBlock p) n)
    refine ⟨hb,?_⟩
    have hn : ¬blockIndex (freshBlock p) n < p.1 := by
      intro h
      have h' := (position_lt _ _).mp h
      have hl : position p.1 < position (blockIndex (freshBlock p) n) := by
        simp only [blockIndex,position_index,blockPosition]
        exact (fresh_block_gap p).trans_le le_self_add
      exact (not_lt_of_ge hl.le) h'
    change (if hi : blockIndex (freshBlock p) n < p.1 then _ else
      if h : ∃ m, blockIndex (freshBlock p) m = blockIndex (freshBlock p) n then r (Classical.choose h)
      else false) = r n
    rw [dite_eq_right hn,dite_eq_left (show ∃ m, blockIndex (freshBlock p) m = blockIndex (freshBlock p) n from ⟨n,rfl⟩)]
    congr 1
    exact block_index_injective _ (Classical.choose_spec
      (show ∃ m, blockIndex (freshBlock p) m = blockIndex (freshBlock p) n from ⟨n,rfl⟩))


def codingDense (r : ℕ → Bool) : Set Prefix := {p | ∃ α, Codes p α r}

theorem coding_dense (r : ℕ → Bool) : Dense (codingDense r) := by
  intro p
  exact ⟨codingPrefix p r,⟨freshBlock p,(coding_prefix_spec p r).2⟩,(coding_prefix_spec p r).1⟩


def blockReal (G : PFilter Prefix) (α : Index) : ℕ → Bool :=
  fun n => genericBits G (blockIndex α n)

def listingGraph (G : PFilter Prefix) : ZFSet :=
  ZFSet.range (fun α : Index =>
    ZFSet.pair (position α).toZFSet (binarySequenceSet (blockReal G α)))

theorem generic_coded_block (G : PFilter Prefix)
    (hd : ∀ i, Meets G (longDomain i)) (p : Prefix) (hp : p ∈ G)
    (α : Index) (r : ℕ → Bool) (hc : Codes p α r) : blockReal G α = r := by
  funext n
  obtain ⟨hi,hbit⟩ := hc n
  exact ((generic_bits_spec G hd).2 p hp ⟨blockIndex α n,hi⟩).trans hbit


theorem block_listing_covers (G : PFilter Prefix)
    (hd : ∀ i, Meets G (longDomain i)) (S : Set (ℕ → Bool))
    (hc : ∀ r ∈ S, Meets G (codingDense r)) : S ⊆ Set.range (blockReal G) := by
  intro r hr
  obtain ⟨p,hp,α,hc'⟩ := hc r hr
  exact ⟨α,generic_coded_block G hd p hp α r hc'⟩


theorem listing_graph_function (G : PFilter Prefix) :
    ZFSet.IsFunc (ω₁ : Ordinal.{0}).toZFSet
      (ZFSet.funs ZFSet.omega {∅,{∅}}) (listingGraph G) := by
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨α,rfl⟩ := ZFSet.mem_range.mp hz
    exact ZFSet.pair_mem_prod.mpr ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr α.toOrd.property,
      ZFSet.mem_funs.mpr (binarySequenceSet_isFunc _)⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    let α := index a ha
    have he : (position α).toZFSet = a.toZFSet := by simp only [α,position_index]
    refine ⟨binarySequenceSet (blockReal G α),?_,?_⟩
    · rw [← he]
      exact ZFSet.mem_range_self α
    · intro w hw
      obtain ⟨β,hβ⟩ := ZFSet.mem_range.mp hw
      obtain ⟨hpos,hval⟩ := ZFSet.pair_inj.mp hβ
      have hαβ : α = β := Ordinal.ToType.mk.symm.injective
        (Subtype.ext (Ordinal.toZFSet_injective (he.trans hpos.symm)))
      subst β
      exact hval.symm


theorem listing_cardinal_bound (G : PFilter Prefix) (S : Set (ℕ → Bool))
    (hc : S ⊆ Set.range (blockReal G)) : #S ≤ ℵ₁ := by
  calc
    #S ≤ #(Set.range (blockReal G)) := Cardinal.mk_le_mk_of_subset hc
    _ ≤ #Index := Cardinal.mk_range_le
    _ = ℵ₁ := by simp [Index,Cardinal.mk_toType]


theorem ch_of_block_listing (G : PFilter Prefix)
    (hc : Function.Surjective (blockReal G)) : #(ℕ → Bool) = ℵ₁ := by
  apply le_antisymm
  · simpa [Index,Cardinal.mk_toType] using Cardinal.mk_le_of_surjective hc
  · apply Cardinal.aleph_one_le_iff.mpr
    rw [Cardinal.mk_arrow,Cardinal.mk_bool,Cardinal.mk_nat]
    simpa only [Cardinal.lift_id,Cardinal.two_power_aleph0] using (Cardinal.aleph0_lt_continuum : (ℵ₀ : Cardinal) < 𝔠)


end
end Lemmatheca.SetTheory.CountablyClosedForcing
