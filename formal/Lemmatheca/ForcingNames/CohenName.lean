import Lemmatheca.ForcingNames.StructuralAxioms

namespace Lemmatheca.SetTheory.ForcingNames
open Set Order
open scoped ZFSet
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.FinitePartialMaps
open Lemmatheca.SetTheory.NaturalNumbersAsSets
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def bitSet (b : Bool) : ZFSet.{u} := if b then {∅} else ∅

def conditionSet (p : Cohen) : ZFSet.{u} :=
  ZFSet.range (fun nb : graph p =>
    ZFSet.pair (naturalSet nb.val.1) (bitSet nb.val.2))

def cohenPosetSet : ZFSet.{u} := ZFSet.range (conditionSet.{u})

def cohenRelationSet : ZFSet.{u} :=
  ZFSet.range (fun qp : {qp : Cohen × Cohen // qp.1 ≤ qp.2} =>
    ZFSet.pair (conditionSet qp.val.1) (conditionSet qp.val.2))


private theorem one_ne_empty : ({∅} : ZFSet.{u}) ≠ ∅ := by
  intro h
  have hm : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := by simp
  rw [h] at hm
  exact ZFSet.notMem_empty _ hm

private theorem bit_injective : Function.Injective (bitSet.{u}) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bitSet,one_ne_empty,Ne.symm one_ne_empty]
private theorem nat_injective : Function.Injective (naturalSet.{u}) := by
  intro m n h
  exact Nat.le_antisymm ((naturalSet_order m n).2.mp (fun _ hz => h ▸ hz))
    ((naturalSet_order n m).2.mp (fun _ hz => h.symm ▸ hz))
private theorem bit_mem_two (b : Bool) : bitSet.{u} b ∈ ({∅,{∅}} : ZFSet.{u}) := by
  cases b <;> simp [bitSet]
private theorem decode_pair {n m : ℕ} {b c : Bool}
    (h : ZFSet.pair (naturalSet.{u} n) (bitSet b) =
      ZFSet.pair (naturalSet m) (bitSet c)) : n = m ∧ b = c := by
  obtain ⟨hn,hb⟩ := ZFSet.pair_inj.mp h
  exact ⟨nat_injective hn,bit_injective hb⟩

theorem conditionSet_mem (p : Cohen) (x : ZFSet.{u}) :
    x ∈ conditionSet p ↔
      ∃ n b, (n,b) ∈ graph p ∧ x = ZFSet.pair (naturalSet n) (bitSet b) := by
  rw [conditionSet,ZFSet.mem_range]
  constructor
  · rintro ⟨nb,he⟩
    exact ⟨nb.val.1,nb.val.2,nb.property,he.symm⟩
  · rintro ⟨n,b,hnb,he⟩
    exact ⟨⟨(n,b),hnb⟩,he.symm⟩

theorem conditionSet_injective : Function.Injective (conditionSet.{u}) := by
  intro p q he
  apply cohen_graph_injective
  ext ⟨n,b⟩
  constructor
  · intro hnb
    have hmem := (conditionSet_mem p _).mpr ⟨n,b,hnb,rfl⟩
    rw [he] at hmem
    obtain ⟨m,c,hmc,hpair⟩ := (conditionSet_mem q _).mp hmem
    obtain ⟨rfl,rfl⟩ := decode_pair hpair
    exact hmc
  · intro hnb
    have hmem := (conditionSet_mem q _).mpr ⟨n,b,hnb,rfl⟩
    rw [← he] at hmem
    obtain ⟨m,c,hmc,hpair⟩ := (conditionSet_mem p _).mp hmem
    obtain ⟨rfl,rfl⟩ := decode_pair hpair
    exact hmc

theorem cohen_code_bijective :
    Function.Bijective (fun p : Cohen =>
      (⟨conditionSet.{u} p,ZFSet.mem_range_self (f := conditionSet.{u}) p⟩ : cohenPosetSet.{u})) := by
  refine ⟨fun p q h => conditionSet_injective (congrArg Subtype.val h),?_⟩
  intro x
  obtain ⟨p,hp⟩ := ZFSet.mem_range.mp x.property
  exact ⟨p,Subtype.ext hp⟩

def cohenCoding : Cohen ≃ cohenPosetSet.{u} :=
  Equiv.ofBijective _ cohen_code_bijective

theorem cohenCoding_value (p : Cohen) : (cohenCoding.{u} p).val = conditionSet p := by rfl

theorem conditionSet_order (q p : Cohen) :
    q ≤ p ↔ conditionSet.{u} p ⊆ conditionSet q := by
  rw [(cohen_order q p).1]
  constructor
  · intro h x hx
    obtain ⟨n,b,hnb,rfl⟩ := (conditionSet_mem p x).mp hx
    exact (conditionSet_mem q _).mpr ⟨n,b,h hnb,rfl⟩
  · intro h nb hnb
    rcases nb with ⟨n,b⟩
    have hmem := h ((conditionSet_mem p _).mpr ⟨n,b,hnb,rfl⟩)
    obtain ⟨m,c,hmc,hpair⟩ := (conditionSet_mem q _).mp hmem
    obtain ⟨rfl,rfl⟩ := decode_pair hpair
    exact hmc

theorem cohenRelationSet_correct (q p : Cohen) :
    ZFSet.pair (cohenCoding.{u} q).val (cohenCoding p).val ∈ cohenRelationSet ↔ q ≤ p := by
  simp only [cohenRelationSet,ZFSet.mem_range,cohenCoding_value]
  constructor
  · rintro ⟨qp,hqp⟩
    obtain ⟨hq,hp⟩ := ZFSet.pair_inj.mp hqp
    have hq' := conditionSet_injective hq
    have hp' := conditionSet_injective hp
    exact hq' ▸ hp' ▸ qp.property
  · intro hqp
    exact ⟨⟨(q,p),hqp⟩,rfl⟩

theorem conditionSet_top : conditionSet.{u} (⊤ : Cohen) = ∅ := by
  ext x
  rw [conditionSet_mem]
  simp only [ZFSet.notMem_empty]
  refine ⟨?_,False.elim⟩
  rintro ⟨n,b,hnb,_⟩
  rw [(cohen_order (⊤ : Cohen) (⊤ : Cohen)).2] at hnb
  exact hnb

def binarySequenceSet (f : ℕ → Bool) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (naturalSet n) (bitSet (f n)))


private theorem binary_members (f : ℕ → Bool) (x : ZFSet.{u}) :
    x ∈ binarySequenceSet f ↔ ∃ n, x = ZFSet.pair (naturalSet n) (bitSet (f n)) := by
  simp only [binarySequenceSet,ZFSet.mem_range]
  exact ⟨fun ⟨n,h⟩ => ⟨n,h.symm⟩,fun ⟨n,h⟩ => ⟨n,h.symm⟩⟩

def cohenName : ZFSet.{u} :=
  ZFSet.range (fun pnb : {pnb : Cohen × ℕ × Bool // (pnb.2.1,pnb.2.2) ∈ graph pnb.1} =>
    ZFSet.pair
      (orderedPairName (conditionSet (⊤ : Cohen))
        (checkName (conditionSet (⊤ : Cohen)) (naturalSet pnb.val.2.1))
        (checkName (conditionSet (⊤ : Cohen)) (bitSet pnb.val.2.2)))
      (conditionSet pnb.val.1))

theorem binarySequenceSet_isFunc (f : ℕ → Bool) :
    ZFSet.IsFunc ZFSet.omega.{u} ({∅,{∅}} : ZFSet.{u}) (binarySequenceSet f) := by
  refine ⟨?_,?_⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (binary_members f x).mp hx
    exact ZFSet.pair_mem_prod.mpr ⟨(omega_members _).mpr ⟨n,rfl⟩,bit_mem_two _⟩
  · intro z hz
    obtain ⟨n,rfl⟩ := (omega_members z).mp hz
    refine ⟨bitSet (f n),(binary_members f _).mpr ⟨n,rfl⟩,?_⟩
    intro w hw
    obtain ⟨m,he⟩ := (binary_members f _).mp hw
    obtain ⟨hn,hw⟩ := ZFSet.pair_inj.mp he
    have hm := nat_injective hn
    subst m
    exact hw

theorem binarySequenceSet_injective : Function.Injective (binarySequenceSet.{u}) := by
  intro f g he
  funext n
  have hmem := (binary_members f _).mpr ⟨n,rfl⟩
  rw [he] at hmem
  obtain ⟨m,hm⟩ := (binary_members g _).mp hmem
  obtain ⟨hn,hb⟩ := decode_pair hm
  subst m
  exact hb

theorem binarySequenceSet_complete (x : ZFSet.{u})
    (hx : ZFSet.IsFunc ZFSet.omega.{u} ({∅,{∅}} : ZFSet.{u}) x) :
    ∃! f : ℕ → Bool, binarySequenceSet f = x := by
  have hn (n : ℕ) := hx.2 (naturalSet n) ((omega_members _).mpr ⟨n,rfl⟩)
  let w : ℕ → ZFSet.{u} := fun n => Classical.choose (hn n)
  have hw (n : ℕ) : ZFSet.pair (naturalSet n) (w n) ∈ x := (Classical.choose_spec (hn n)).1
  have huniq (n : ℕ) (v : ZFSet.{u}) (hv : ZFSet.pair (naturalSet n) v ∈ x) : v = w n :=
    (Classical.choose_spec (hn n)).2 v hv
  have hbit (n : ℕ) : w n ∈ ({∅,{∅}} : ZFSet.{u}) :=
    (ZFSet.pair_mem_prod.mp (hx.1 (hw n))).2
  let f : ℕ → Bool := fun n => if w n = ∅ then false else true
  have hf (n : ℕ) : bitSet (f n) = w n := by
    rcases ZFSet.mem_insert_iff.mp (hbit n) with hz | hz
    · simp [f,hz,bitSet]
    · have ho := ZFSet.mem_singleton.mp hz
      simp [f,ho,bitSet,one_ne_empty]
  have he : binarySequenceSet f = x := by
    ext z
    rw [binary_members]
    constructor
    · rintro ⟨n,rfl⟩
      rw [hf]
      exact hw n
    · intro hz
      obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hx.1 hz)
      obtain ⟨n,rfl⟩ := (omega_members a).mp ha
      have he := huniq n b hz
      exact ⟨n,congrArg (ZFSet.pair (naturalSet n)) (he.trans (hf n).symm)⟩
  exact ⟨f,he,fun g hg => binarySequenceSet_injective (hg.trans he.symm)⟩

theorem cohenName_attachments (x : ZFSet.{u}) :
    x ∈ cohenName.{u} ↔
      ∃ p n b, (n,b) ∈ graph p ∧ x = ZFSet.pair
        (orderedPairName (conditionSet (⊤ : Cohen))
          (checkName (conditionSet (⊤ : Cohen)) (naturalSet n))
          (checkName (conditionSet (⊤ : Cohen)) (bitSet b))) (conditionSet p) := by
  rw [cohenName,ZFSet.mem_range]
  constructor
  · rintro ⟨pnb,he⟩
    exact ⟨pnb.val.1,pnb.val.2.1,pnb.val.2.2,pnb.property,he.symm⟩
  · rintro ⟨p,n,b,hnb,he⟩
    exact ⟨⟨(p,n,b),hnb⟩,he.symm⟩


theorem cohenName_isName : IsName cohenPosetSet.{u} cohenName := by
  apply (isName_iff cohenPosetSet _).mpr
  intro z hz
  obtain ⟨p,n,b,hnb,rfl⟩ := (cohenName_attachments z).mp hz
  have ht : conditionSet (⊤ : Cohen) ∈ cohenPosetSet.{u} := ZFSet.mem_range_self _
  exact ⟨_,conditionSet p,rfl,ZFSet.mem_range_self (f := conditionSet.{u}) p,
    orderedPairName_isName cohenPosetSet _ _ _ ht
      (checkName_isName cohenPosetSet _ _ ht) (checkName_isName cohenPosetSet _ _ ht)⟩

private theorem condition_in_filter (G : PFilter Cohen) (p : Cohen) :
    conditionSet.{u} p ∈ filterSet cohenPosetSet cohenCoding G ↔ p ∈ G := by
  rw [filterSet_mem]
  simp only [cohenCoding_value]
  constructor
  · rintro ⟨q,hq,he⟩
    have h := conditionSet_injective he
    exact h.symm ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

private theorem top_in_filter (G : PFilter Cohen) :
    conditionSet (⊤ : Cohen) ∈ filterSet cohenPosetSet.{u} cohenCoding G :=
  (condition_in_filter G ⊤).mpr (show (⊤ : Cohen) ∈ G from PFilter.top_mem)

private theorem op_check_value (G : PFilter Cohen) (n : ℕ) (b : Bool) :
    evaluation (filterSet cohenPosetSet cohenCoding G)
      (orderedPairName (conditionSet (⊤ : Cohen))
        (checkName (conditionSet (⊤ : Cohen)) (naturalSet n))
        (checkName (conditionSet (⊤ : Cohen)) (bitSet b))) =
      ZFSet.pair (naturalSet.{u} n) (bitSet b) := by
  rw [orderedPairName_value _ _ _ _ (top_in_filter G),
    checkName_value _ _ _ (top_in_filter G),checkName_value _ _ _ (top_in_filter G)]

theorem cohenName_value (G : PFilter Cohen) (x : ZFSet.{u}) :
    x ∈ evaluation (filterSet cohenPosetSet cohenCoding G) cohenName ↔
      ∃ n b, (n,b) ∈ cohenUnion G ∧
        x = ZFSet.pair (naturalSet n) (bitSet b) := by
  rw [evaluation_mem]
  constructor
  · rintro ⟨σ,q,hσq,hq,he⟩
    obtain ⟨p,n,b,hnb,hpair⟩ := (cohenName_attachments _).mp hσq
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    have hp := (condition_in_filter G p).mp hq
    exact ⟨n,b,⟨p,hp,hnb⟩,he.trans (op_check_value G n b)⟩
  · rintro ⟨n,b,⟨p,hp,hnb⟩,he⟩
    refine ⟨_,conditionSet p,(cohenName_attachments _).mpr ⟨p,n,b,hnb,rfl⟩,
      (condition_in_filter G p).mpr hp,?_⟩
    exact he.trans (op_check_value G n b).symm

theorem cohenName_union (G : PFilter Cohen) :
    evaluation (filterSet cohenPosetSet cohenCoding G) cohenName =
      ⋃₀(filterSet cohenPosetSet.{u} cohenCoding G) := by
  ext x
  rw [cohenName_value,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨n,b,⟨p,hp,hnb⟩,rfl⟩
    exact ⟨conditionSet p,(condition_in_filter G p).mpr hp,
      (conditionSet_mem p _).mpr ⟨n,b,hnb,rfl⟩⟩
  · rintro ⟨z,hz,hx⟩
    obtain ⟨p,hp,rfl⟩ := (filterSet_mem cohenPosetSet cohenCoding G z).mp hz
    rw [cohenCoding_value] at hx
    obtain ⟨n,b,hnb,he⟩ := (conditionSet_mem p x).mp hx
    exact ⟨n,b,⟨p,hp,hnb⟩,he⟩

theorem cohenReal_name_value (G : PFilter Cohen) (hG : ∀ n, Meets G (coordinateDense n)) :
    evaluation (filterSet cohenPosetSet cohenCoding G) cohenName.{u} =
      binarySequenceSet (cohenReal G hG) := by
  ext x
  rw [cohenName_value,binary_members]
  simp only [(cohen_real_spec G hG).1,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,b,rfl,he⟩
    exact ⟨n,he⟩
  · rintro ⟨n,he⟩
    exact ⟨n,cohenReal G hG n,rfl,he⟩

theorem cohenName_in_extension (M : ZFSet.{u}) (G : PFilter Cohen)
    (hname : cohenName.{u} ∈ M) :
    evaluation (filterSet cohenPosetSet cohenCoding G) cohenName ∈
      extension cohenPosetSet M (filterSet cohenPosetSet cohenCoding G) := by
  exact (extension_mem _ _ _ _).mpr ⟨cohenName,hname,cohenName_isName,rfl⟩

theorem cohen_new_real_in_extension (M : ZFSet.{u}) (G : PFilter Cohen)
    (S : Set (Set Cohen)) (hG : GenericFor G S)
    (hcoord : ∀ n, coordinateDense n ∈ S)
    (hold : ∀ f : ℕ → Bool, binarySequenceSet.{u} f ∈ M → disagreementDense f ∈ S)
    (hname : cohenName.{u} ∈ M) :
    ∃ f : ℕ → Bool,
      evaluation (filterSet cohenPosetSet cohenCoding G) cohenName = binarySequenceSet f ∧
      binarySequenceSet f ∈ extension cohenPosetSet M (filterSet cohenPosetSet cohenCoding G) ∧
      binarySequenceSet f ∉ M ∧ cohenUnion G = {nb | nb.2 = f nb.1} := by
  have hc : ∀ n, Meets G (coordinateDense n) :=
    fun n => hG _ (hcoord n) (coordinate_dense n)
  refine ⟨cohenReal G hc,cohenReal_name_value G hc,?_,?_,(cohen_real_spec G hc).1⟩
  · rw [← cohenReal_name_value G hc]
    exact cohenName_in_extension M G hname
  · intro hmem
    obtain ⟨n,hn⟩ := cohen_real_disagrees G hc _
      (hG _ (hold _ hmem) (disagreement_dense _))
    exact hn rfl

end
end Lemmatheca.SetTheory.ForcingNames
