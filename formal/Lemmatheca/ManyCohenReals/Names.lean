import Lemmatheca.ManyCohenReals.Array
import Lemmatheca.ForcingNames.CohenName
import Mathlib.Logic.Small.List

/-! Actual set codes, coordinate names, and the name of the entire indexed family. -/
namespace Lemmatheca.SetTheory.ManyCohenReals
open Set Order
open scoped ZFSet
open Lemmatheca.SetTheory.FinitePartialMaps
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingChainConditions
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.NaturalNumbersAsSets
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

local instance namesSmallMultiset {α : Type (u + 1)} [Small.{u} α] : Small.{u} (Multiset α) :=
  inferInstanceAs (Small.{u} (Quotient (List.isSetoid α)))

local instance conditionsSmall (K : ZFSet.{u}) : Small.{u} (Conditions K) :=
  small_of_injective (show Function.Injective (fun p : Conditions K => p.entries) from
    fun _ _ h => Finmap.ext h)

local instance namesOrder (K : ZFSet.{u}) : PartialOrder (Conditions K) := binaryOrder (ℕ × K)
local instance namesTop (K : ZFSet.{u}) : OrderTop (Conditions K) := binaryOrderTop (ℕ × K)


private theorem one_ne_empty : ({∅} : ZFSet.{u}) ≠ ∅ := by
  intro h
  have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
  rw [h] at hm
  exact ZFSet.notMem_empty _ hm

private theorem bit_injective : Function.Injective (bitSet.{u}) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bitSet, one_ne_empty, Ne.symm one_ne_empty]

private theorem nat_injective : Function.Injective (naturalSet.{u}) := by
  intro m n h
  exact Nat.le_antisymm ((naturalSet_order m n).2.mp (fun _ hz => h ▸ hz))
    ((naturalSet_order n m).2.mp (fun _ hz => h.symm ▸ hz))

private theorem decode_assignment {K : ZFSet.{u}} {n m : ℕ} {α β : K} {b c : Bool}
    (h : ZFSet.pair (ZFSet.pair (naturalSet n) α.val) (bitSet b) =
      ZFSet.pair (ZFSet.pair (naturalSet m) β.val) (bitSet c)) :
    n = m ∧ α = β ∧ b = c := by
  obtain ⟨hcoord, hbit⟩ := ZFSet.pair_inj.mp h
  obtain ⟨hn, hα⟩ := ZFSet.pair_inj.mp hcoord
  exact ⟨nat_injective hn, Subtype.ext hα, bit_injective hbit⟩

/-- The native map is encoded by the actual pairs ((n,alpha),b). -/
def conditionCode (K : ZFSet.{u}) (p : Conditions K) : ZFSet.{u} :=
  ZFSet.range (fun z : graph p =>
    ZFSet.pair (ZFSet.pair (naturalSet z.val.1.1) z.val.1.2.val) (bitSet z.val.2))

def conditionPoset (K : ZFSet.{u}) : ZFSet.{u} := ZFSet.range (conditionCode K)

def conditionRelation (K : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun qp : {qp : Conditions K × Conditions K // qp.1 ≤ qp.2} =>
    ZFSet.pair (conditionCode K qp.val.1) (conditionCode K qp.val.2))

theorem conditionCode_members (K : ZFSet.{u}) (p : Conditions K) (x : ZFSet.{u}) :
    x ∈ conditionCode K p ↔ ∃ (n : ℕ) (α : K) (b : Bool),
      ((n, α), b) ∈ graph p ∧
        x = ZFSet.pair (ZFSet.pair (naturalSet n) α.val) (bitSet b) := by
  rw [conditionCode, ZFSet.mem_range]
  constructor
  · rintro ⟨z, he⟩
    exact ⟨z.val.1.1, z.val.1.2, z.val.2, z.property, he.symm⟩
  · rintro ⟨n, α, b, hnb, he⟩
    exact ⟨⟨((n, α), b), hnb⟩, he.symm⟩

theorem conditionCode_injective (K : ZFSet.{u}) : Function.Injective (conditionCode K) := by
  intro p q he
  apply binary_graph_injective
  ext ⟨⟨n, α⟩, b⟩
  constructor
  · intro hnb
    have hmem := (conditionCode_members K p _).mpr ⟨n, α, b, hnb, rfl⟩
    rw [he] at hmem
    obtain ⟨m, β, c, hmc, hpair⟩ := (conditionCode_members K q _).mp hmem
    obtain ⟨rfl, rfl, rfl⟩ := decode_assignment hpair
    exact hmc
  · intro hnb
    have hmem := (conditionCode_members K q _).mpr ⟨n, α, b, hnb, rfl⟩
    rw [← he] at hmem
    obtain ⟨m, β, c, hmc, hpair⟩ := (conditionCode_members K p _).mp hmem
    obtain ⟨rfl, rfl, rfl⟩ := decode_assignment hpair
    exact hmc

theorem conditionCode_bijective (K : ZFSet.{u}) :
    Function.Bijective (fun p : Conditions K =>
      (⟨conditionCode K p, ZFSet.mem_range_self (f := conditionCode K) p⟩ : conditionPoset K)) := by
  refine ⟨fun p q h => conditionCode_injective K (congrArg Subtype.val h), ?_⟩
  intro x
  obtain ⟨p, hp⟩ := ZFSet.mem_range.mp x.property
  exact ⟨p, Subtype.ext hp⟩

/-- The specified coding, not an arbitrary bijection with some set of conditions. -/
def conditionCoding (K : ZFSet.{u}) : Conditions K ≃ conditionPoset K :=
  Equiv.ofBijective _ (conditionCode_bijective K)

theorem conditionCoding_value (K : ZFSet.{u}) (p : Conditions K) :
    (conditionCoding K p).val = conditionCode K p := by
  rfl


private theorem condition_in_filter (K : ZFSet.{u}) (G : PFilter (Conditions K))
    (p : Conditions K) :
    conditionCode K p ∈ filterSet (conditionPoset K) (conditionCoding K) G ↔ p ∈ G := by
  rw [filterSet_mem]
  simp only [conditionCoding_value]
  constructor
  · rintro ⟨q, hq, he⟩
    have h := conditionCode_injective K he
    exact h.symm ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

private theorem top_in_filter (K : ZFSet.{u}) (G : PFilter (Conditions K)) :
    conditionCode K (⊤ : Conditions K) ∈
      filterSet (conditionPoset K) (conditionCoding K) G :=
  (condition_in_filter K G ⊤).mpr (show (⊤ : Conditions K) ∈ G from PFilter.top_mem)

private theorem op_check_value (K : ZFSet.{u}) (G : PFilter (Conditions K))
    (n : ℕ) (b : Bool) :
    evaluation (filterSet (conditionPoset K) (conditionCoding K) G)
      (orderedPairName (conditionCode K (⊤ : Conditions K))
        (checkName (conditionCode K (⊤ : Conditions K)) (naturalSet n))
        (checkName (conditionCode K (⊤ : Conditions K)) (bitSet b))) =
      ZFSet.pair (naturalSet.{u} n) (bitSet b) := by
  rw [orderedPairName_value _ _ _ _ (top_in_filter K G),
    checkName_value _ _ _ (top_in_filter K G), checkName_value _ _ _ (top_in_filter K G)]

theorem conditionCode_order (K : ZFSet.{u}) (q p : Conditions K) :
    q ≤ p ↔ conditionCode K p ⊆ conditionCode K q := by
  change graph p ⊆ graph q ↔ _
  constructor
  · intro h x hx
    obtain ⟨n, α, b, hnb, rfl⟩ := (conditionCode_members K p x).mp hx
    exact (conditionCode_members K q _).mpr ⟨n, α, b, h hnb, rfl⟩
  · intro h nb hnb
    rcases nb with ⟨⟨n, α⟩, b⟩
    have hmem := h ((conditionCode_members K p _).mpr ⟨n, α, b, hnb, rfl⟩)
    obtain ⟨m, β, c, hmc, hpair⟩ := (conditionCode_members K q _).mp hmem
    obtain ⟨rfl, rfl, rfl⟩ := decode_assignment hpair
    exact hmc

theorem conditionRelation_correct (K : ZFSet.{u}) (q p : Conditions K) :
    ZFSet.pair (conditionCode K q) (conditionCode K p) ∈ conditionRelation K ↔ q ≤ p := by
  simp only [conditionRelation, ZFSet.mem_range]
  constructor
  · rintro ⟨qp, hqp⟩
    obtain ⟨hq, hp⟩ := ZFSet.pair_inj.mp hqp
    have hq' := conditionCode_injective K hq
    have hp' := conditionCode_injective K hp
    exact hq' ▸ hp' ▸ qp.property
  · intro hqp
    exact ⟨⟨(q, p), hqp⟩, rfl⟩

theorem conditionCode_top (K : ZFSet.{u}) : conditionCode K (⊤ : Conditions K) = ∅ := by
  ext x
  rw [conditionCode_members]
  simp only [ZFSet.notMem_empty]
  refine ⟨?_, False.elim⟩
  rintro ⟨n, α, b, hnb, _⟩
  change Sigma.mk (n, α) b ∈ (∅ : Conditions K).entries at hnb
  have hlookup : (∅ : Conditions K).lookup (n, α) = some b :=
    Finmap.lookup_eq_some_iff.mpr hnb
  simp at hlookup

/-- The exact coordinate name displayed in the human argument. -/
def coordinateName (K : ZFSet.{u}) (α : K) : ZFSet.{u} :=
  ZFSet.range (fun pnb : {t : Conditions K × ℕ × Bool // ((t.2.1, α), t.2.2) ∈ graph t.1} =>
    ZFSet.pair
      (orderedPairName (conditionCode K (⊤ : Conditions K))
        (checkName (conditionCode K (⊤ : Conditions K)) (naturalSet pnb.val.2.1))
        (checkName (conditionCode K (⊤ : Conditions K)) (bitSet pnb.val.2.2)))
      (conditionCode K pnb.val.1))

theorem coordinateName_attachments (K : ZFSet.{u}) (α : K) (x : ZFSet.{u}) :
    x ∈ coordinateName K α ↔ ∃ p n b, ((n, α), b) ∈ graph p ∧ x = ZFSet.pair
      (orderedPairName (conditionCode K (⊤ : Conditions K))
        (checkName (conditionCode K (⊤ : Conditions K)) (naturalSet n))
        (checkName (conditionCode K (⊤ : Conditions K)) (bitSet b)))
      (conditionCode K p) := by
  rw [coordinateName, ZFSet.mem_range]
  constructor
  · rintro ⟨pnb, he⟩
    exact ⟨pnb.val.1, pnb.val.2.1, pnb.val.2.2, pnb.property, he.symm⟩
  · rintro ⟨p, n, b, hnb, he⟩
    exact ⟨⟨(p, n, b), hnb⟩, he.symm⟩

theorem coordinateName_isName (K : ZFSet.{u}) (α : K) :
    IsName (conditionPoset K) (coordinateName K α) := by
  apply (isName_iff (conditionPoset K) _).mpr
  intro z hz
  obtain ⟨p, n, b, hnb, rfl⟩ := (coordinateName_attachments K α z).mp hz
  have ht : conditionCode K (⊤ : Conditions K) ∈ conditionPoset K := ZFSet.mem_range_self _
  exact ⟨_, conditionCode K p, rfl, ZFSet.mem_range_self (f := conditionCode K) p,
    orderedPairName_isName (conditionPoset K) _ _ _ ht
      (checkName_isName (conditionPoset K) _ _ ht)
      (checkName_isName (conditionPoset K) _ _ ht)⟩

theorem coordinateName_members (K : ZFSet.{u}) (α : K)
    (G : PFilter (Conditions K)) (x : ZFSet.{u}) :
    x ∈ evaluation (filterSet (conditionPoset K) (conditionCoding K) G) (coordinateName K α) ↔
      ∃ n b, ((n, α), b) ∈ arrayUnion G ∧
        x = ZFSet.pair (naturalSet n) (bitSet b) := by
  rw [evaluation_mem]
  constructor
  · rintro ⟨σ, q, hσq, hq, he⟩
    obtain ⟨p, n, b, hnb, hpair⟩ := (coordinateName_attachments K α _).mp hσq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp hpair
    have hp := (condition_in_filter K G p).mp hq
    exact ⟨n, b, ⟨p, hp, hnb⟩, he.trans (op_check_value K G n b)⟩
  · rintro ⟨n, b, ⟨p, hp, hnb⟩, he⟩
    refine ⟨_, conditionCode K p, (coordinateName_attachments K α _).mpr
      ⟨p, n, b, hnb, rfl⟩, (condition_in_filter K G p).mpr hp, ?_⟩
    exact he.trans (op_check_value K G n b).symm

theorem coordinateName_column (K : ZFSet.{u}) (α : K)
    (G : PFilter (Conditions K)) (hc : ∀ n α, Meets G (coordinateDense n α)) :
    evaluation (filterSet (conditionPoset K) (conditionCoding K) G) (coordinateName K α) =
      binarySequenceSet (column G hc α) := by
  ext x
  rw [coordinateName_members]
  simp only [binarySequenceSet, ZFSet.mem_range]
  constructor
  · rintro ⟨n, b, hb, he⟩
    have hbit : b = column G hc α n := by
      have h := hb
      rw [(column_spec G hc).1] at h
      exact h
    subst b
    exact ⟨n, he.symm⟩
  · rintro ⟨n, he⟩
    refine ⟨n, column G hc α n, ?_, he.symm⟩
    rw [(column_spec G hc).1]
    rfl

theorem coordinateName_in_extension (K M : ZFSet.{u}) (α : K)
    (G : PFilter (Conditions K)) (hc : ∀ n α, Meets G (coordinateDense n α))
    (hname : coordinateName K α ∈ M) :
    binarySequenceSet (column G hc α) ∈
      extension (conditionPoset K) M (filterSet (conditionPoset K) (conditionCoding K) G) := by
  exact (extension_mem _ _ _ _).mpr
    ⟨coordinateName K α, hname, coordinateName_isName K α,
      coordinateName_column K α G hc⟩

/-- The actual set-coded graph of a specified entire family of binary sequences. -/
def familyGraph (K : ZFSet.{u}) (c : K → ℕ → Bool) : ZFSet.{u} :=
  ZFSet.range (fun α : K => ZFSet.pair α.val (binarySequenceSet (c α)))

theorem familyGraph_members (K : ZFSet.{u}) (c : K → ℕ → Bool) (x : ZFSet.{u}) :
    x ∈ familyGraph K c ↔ ∃ α : K, x = ZFSet.pair α.val (binarySequenceSet (c α)) := by
  rw [familyGraph, ZFSet.mem_range]
  exact ⟨fun ⟨α, h⟩ => ⟨α, h.symm⟩, fun ⟨α, h⟩ => ⟨α, h.symm⟩⟩

theorem familyGraph_function (K : ZFSet.{u}) (c : K → ℕ → Bool) :
    ZFSet.IsFunc K (ZFSet.range (binarySequenceSet.{u})) (familyGraph K c) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨α, rfl⟩ := (familyGraph_members K c x).mp hx
    exact ZFSet.pair_mem_prod.mpr ⟨α.property, ZFSet.mem_range_self _⟩
  · intro z hz
    let α : K := ⟨z, hz⟩
    refine ⟨binarySequenceSet (c α), (familyGraph_members K c _).mpr ⟨α, rfl⟩, ?_⟩
    intro w hw
    obtain ⟨β, he⟩ := (familyGraph_members K c _).mp hw
    obtain ⟨hα, hw⟩ := ZFSet.pair_inj.mp he
    have hβα : β = α := Subtype.ext hα.symm
    subst β
    exact hw

theorem familyGraph_injective (K : ZFSet.{u}) (c : K → ℕ → Bool)
    (hc : Function.Injective c) :
    ∀ x y z : ZFSet.{u}, ZFSet.pair x z ∈ familyGraph K c →
      ZFSet.pair y z ∈ familyGraph K c → x = y := by
  intro x y z hx hy
  obtain ⟨α, hα⟩ := (familyGraph_members K c _).mp hx
  obtain ⟨β, hβ⟩ := (familyGraph_members K c _).mp hy
  obtain ⟨hxα, hzα⟩ := ZFSet.pair_inj.mp hα
  obtain ⟨hyβ, hzβ⟩ := ZFSet.pair_inj.mp hβ
  have hab : α = β := hc (binarySequenceSet_injective (hzα.symm.trans hzβ))
  exact hxα.trans ((congrArg Subtype.val hab).trans hyβ.symm)

/-- The general top-attached indexed-family name used by the displayed construction. -/
def indexedFamilyName (K t : ZFSet.{u}) (σ : K → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun α : K => ZFSet.pair
    (orderedPairName t (checkName t α.val) (σ α)) t)

theorem indexedFamilyName_isName (P K t : ZFSet.{u}) (σ : K → ZFSet.{u})
    (ht : t ∈ P) (hσ : ∀ α, IsName P (σ α)) :
    IsName P (indexedFamilyName K t σ) := by
  apply (isName_iff P _).mpr
  intro z hz
  obtain ⟨α, rfl⟩ := ZFSet.mem_range.mp hz
  exact ⟨_, t, rfl, ht, orderedPairName_isName P t _ _ ht
    (checkName_isName P t α.val ht) (hσ α)⟩

theorem indexedFamilyName_value (K t G : ZFSet.{u}) (σ : K → ZFSet.{u}) (ht : t ∈ G) :
    evaluation G (indexedFamilyName K t σ) =
      ZFSet.range (fun α : K => ZFSet.pair α.val (evaluation G (σ α))) := by
  ext x
  rw [evaluation_mem, ZFSet.mem_range]
  constructor
  · rintro ⟨τ, p, hτp, hp, he⟩
    obtain ⟨α, hα⟩ := ZFSet.mem_range.mp hτp
    obtain ⟨hτ, _⟩ := ZFSet.pair_inj.mp hα
    subst τ
    rw [orderedPairName_value _ _ _ _ ht, checkName_value _ _ _ ht] at he
    exact ⟨α, he.symm⟩
  · rintro ⟨α, he⟩
    refine ⟨orderedPairName t (checkName t α.val) (σ α), t,
      ZFSet.mem_range_self (f := fun α : K =>
        ZFSet.pair (orderedPairName t (checkName t α.val) (σ α)) t) α, ht, ?_⟩
    rw [orderedPairName_value _ _ _ _ ht, checkName_value _ _ _ ht]
    exact he.symm

/-- A uniform name for the graph alpha maps to the value of the alpha coordinate name. -/
def familyName (K : ZFSet.{u}) : ZFSet.{u} :=
  indexedFamilyName K (conditionCode K (⊤ : Conditions K)) (coordinateName K)

theorem familyName_attachments (K : ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ familyName K ↔ ∃ α : K, x = ZFSet.pair
      (orderedPairName (conditionCode K (⊤ : Conditions K))
        (checkName (conditionCode K (⊤ : Conditions K)) α.val) (coordinateName K α))
      (conditionCode K (⊤ : Conditions K)) := by
  rw [familyName, indexedFamilyName, ZFSet.mem_range]
  exact ⟨fun ⟨α, h⟩ => ⟨α, h.symm⟩, fun ⟨α, h⟩ => ⟨α, h.symm⟩⟩

theorem familyName_isName (K : ZFSet.{u}) : IsName (conditionPoset K) (familyName K) := by
  exact indexedFamilyName_isName (conditionPoset K) K _ (coordinateName K)
    (ZFSet.mem_range_self (f := conditionCode K) _) (coordinateName_isName K)

theorem familyName_value (K : ZFSet.{u}) (G : PFilter (Conditions K))
    (hc : ∀ n α, Meets G (coordinateDense n α)) :
    evaluation (filterSet (conditionPoset K) (conditionCoding K) G) (familyName K) =
      familyGraph K (column G hc) := by
  rw [familyName, indexedFamilyName_value K _ _ _ (top_in_filter K G)]
  change ZFSet.range _ = ZFSet.range _
  congr 1
  funext α
  rw [coordinateName_column K α G hc]

theorem familyName_in_extension (K M : ZFSet.{u}) (G : PFilter (Conditions K))
    (hc : ∀ n α, Meets G (coordinateDense n α)) (hname : familyName K ∈ M) :
    familyGraph K (column G hc) ∈
      extension (conditionPoset K) M (filterSet (conditionPoset K) (conditionCoding K) G) := by
  exact (extension_mem _ _ _ _).mpr
    ⟨familyName K, hname, familyName_isName K, familyName_value K G hc⟩

/-- The native old-real disagreement requirements exclude the actual old graph codes. -/
theorem column_not_ground (K M : ZFSet.{u}) (G : PFilter (Conditions K))
    (S : Set (Set (Conditions K))) (hG : GenericFor G S)
    (hcoord : ∀ n α, coordinateDense n α ∈ S)
    (hold : ∀ α f, binarySequenceSet.{u} f ∈ M → disagreementDense α f ∈ S) :
    let hc : ∀ n α, Meets G (coordinateDense n α) :=
      fun n α => hG _ (hcoord n α) (coordinate_dense n α)
    ∀ α, binarySequenceSet (column G hc α) ∉ M := by
  dsimp only
  let hc : ∀ n α, Meets G (coordinateDense n α) :=
    fun n α => hG _ (hcoord n α) (coordinate_dense n α)
  intro α hmem
  obtain ⟨n, hn⟩ := column_disagrees G hc α _
    (hG _ (hold α _ hmem) (disagreement_dense α _))
  exact hn rfl

end
end Lemmatheca.SetTheory.ManyCohenReals
