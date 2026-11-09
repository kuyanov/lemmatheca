import Lemmatheca.FriedbergNumberings.Basic
import Lemmatheca.CodingFiniteSequences.FiniteSequenceCoding
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursiveAutomation

namespace Lemmatheca.ComputabilityTheory.FriedbergNumberings

open Encodable UniversalComputation EffectiveEnumerations

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Source requirement, optional retirement endpoint, and current finite contents. -/
abbrev Row := ℕ × (Option ℕ × List ℕ)

/-- Allocated rows, latest endpoint, and chronological (row,endpoint) retirement events. -/
abbrev State := List Row × (ℕ × List (ℕ × ℕ))

def initialState : State := ([], (0, []))
def rows (z : State) : List Row := z.1
def latest (z : State) : ℕ := z.2.1
def events (z : State) : List (ℕ × ℕ) := z.2.2
def source (r : Row) : ℕ := r.1
def endpoint (r : Row) : Option ℕ := r.2.1
def contents (r : Row) : List ℕ := r.2.2
def rowAt (z : State) (x : ℕ) : Row := (rows z).getD x (0, (none, []))

def Active (z : State) (e x : ℕ) : Prop :=
  x < (rows z).length ∧ source (rowAt z x) = e ∧ endpoint (rowAt z x) = none

def Retired (z : State) (x k : ℕ) : Prop :=
  x < (rows z).length ∧ endpoint (rowAt z x) = some k

def follower (e : ℕ) (z : State) : ℕ :=
  (rows z).findIdx (fun r => decide (source r = e ∧ endpoint r = none))

def stageBit (e s y : ℕ) : Bool := decide (stageTest e s y = 1)

def observedRow (e s : ℕ) : List ℕ :=
  (List.range s).filter (stageBit e s)

def noninitialListTest (L : List ℕ) : Bool :=
  L.any (fun b => (List.range b).any (fun a => !(L.contains a)))

def noninitialTest (e s x : ℕ) : Bool :=
  noninitialListTest ((List.range (x + 1)).filter (stageBit e s))

def differentTest (e j s x : ℕ) : Bool :=
  (List.range (x + 1)).any (fun y => stageBit e s y != stageBit j s y)

def passTest (e s x : ℕ) : Bool :=
  noninitialTest e s x && (List.range e).all (fun j => differentTest e j s x)

def Passes (e s x : ℕ) : Prop :=
  ¬ IsLowerSet (stage e s ∩ Set.Iic x) ∧
    ∀ j < e, stage e s ∩ Set.Iic x ≠ stage j s ∩ Set.Iic x

def freshEndpoint (z : State) (x : ℕ) : ℕ :=
  2 * (max (latest z) ((contents (rowAt z x)).foldl max 0) + 1)

def next (s : ℕ) (z : State) : State :=
  let e := visit s
  let x := follower e z
  if x = (rows z).length then
    ((rows z) ++ [(e, (none, []))], (latest z, events z))
  else if passTest e s x then
    ((rows z).set x (e, (none, observedRow e s)), (latest z, events z))
  else
    let k := freshEndpoint z x
    ((rows z).set x (e, (some k, List.range (k + 1))),
      (k, (events z) ++ [(x, k)]))

def state : ℕ → State
  | 0 => initialState
  | s + 1 => next s (state s)

def packState (z : State) : ℕ := encode z
def unpackState (n : ℕ) : State := (Encodable.decode (α := State) n).getD initialState
def nextCode (s n : ℕ) : ℕ := packState (next s (unpackState n))
def stateCode (s : ℕ) : ℕ := packState (state s)

def allocated (s : ℕ) : ℕ := (rows (state s)).length
def rowStage (x s : ℕ) : Set ℕ := {y | y ∈ contents (rowAt (state s) x)}
def preliminaryRow (x : ℕ) : Set ℕ := {y | ∃ s, y ∈ rowStage x s}
def retirementEndpoints : Set ℕ := {k | ∃ s x, (x, k) ∈ events (state s)}
def Permanent (e x : ℕ) : Prop := ∃ S, ∀ s, S ≤ s → Active (state s) e x

def preliminaryRecognizer (x y : ℕ) : Part ℕ :=
  (Nat.rfind (fun s => Part.some (decide (y ∈ contents (rowAt (state s) x))))).map
    (fun _ => 0)

private theorem list_filter_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → List β) (p : α → β → Bool) (hf : Primrec f)
    (hp : Primrec fun q : α × β => p q.1 q.2) :
    Primrec (fun x => (f x).filter (p x)) := by
  have hR : PrimrecRel (fun b a => p a b = true) :=
    Primrec.eq.comp (hp.comp (Primrec.snd.pair Primrec.fst)) (Primrec.const true)
  exact (hR.listFilter.comp hf Primrec.id).of_eq (fun x => by simp)

private theorem stage_bit_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => stageBit p.1.1 p.1.2 p.2) := by
  exact Primrec.eq.decide.comp stage_test_primitive (Primrec.const 1)

@[local fun_prop] private theorem stageBit_closure {α : Type*} [Primcodable α]
    {e s y : α → ℕ} (he : Primrec e) (hs : Primrec s) (hy : Primrec y) :
    Primrec (fun x => stageBit (e x) (s x) (y x)) :=
  stage_bit_primitive.comp ((he.pair hs).pair hy)

@[local fun_prop] private theorem listFilter_closure {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f)
    (hp : Primrec fun q : α × β => p q.1 q.2) :
    Primrec (fun x => (f x).filter (p x)) := list_filter_primitive f p hf hp

@[local fun_prop] private theorem listContains_closure {α β : Type*} [Primcodable α]
    [Primcodable β] [DecidableEq β] [BEq β] [LawfulBEq β]
    {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => (g x).contains (f x)) := by
  exact (PrimitiveRecursiveAutomation.listMem hf hg).of_eq (fun x => by simp)

@[local fun_prop] private theorem boolNe_closure {α : Type*} [Primcodable α]
    {f g : α → Bool} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => f x != g x) :=
  (Primrec.dom_bool₂ (fun a b : Bool => a != b)).comp hf hg

@[local fun_prop] private theorem listSet_closure {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {i : α → ℕ} {v : α → β}
    (hf : Primrec f) (hi : Primrec i) (hv : Primrec v) :
    Primrec (fun x => (f x).set (i x) (v x)) :=
  Primrec.list_set.comp hf (hi.pair hv)

private theorem observed_row_primitive : Primrec₂ observedRow := by
  unfold Primrec₂ observedRow
  fun_prop

@[local fun_prop] private theorem observedRow_closure {α : Type*} [Primcodable α]
    {e s : α → ℕ} (he : Primrec e) (hs : Primrec s) :
    Primrec (fun x => observedRow (e x) (s x)) := observed_row_primitive.comp he hs

private theorem noninitial_list_primitive : Primrec noninitialListTest := by
  unfold noninitialListTest
  fun_prop

@[local fun_prop] private theorem noninitialList_closure {α : Type*} [Primcodable α]
    {f : α → List ℕ} (hf : Primrec f) :
    Primrec (fun x => noninitialListTest (f x)) := noninitial_list_primitive.comp hf

private theorem pass_test_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => passTest p.1.1 p.1.2 p.2) := by
  unfold passTest noninitialTest differentTest
  fun_prop

@[local fun_prop] private theorem passTest_closure {α : Type*} [Primcodable α]
    {e s x : α → ℕ} (he : Primrec e) (hs : Primrec s) (hx : Primrec x) :
    Primrec (fun a => passTest (e a) (s a) (x a)) :=
  pass_test_primitive.comp ((he.pair hs).pair hx)

private theorem follower_primitive : Primrec₂ follower := by
  unfold Primrec₂ follower rows source endpoint
  simp only [Bool.decide_and]
  apply Primrec.list_findIdx
  · fun_prop
  · unfold Primrec₂
    fun_prop

@[local fun_prop] private theorem follower_closure {α : Type*} [Primcodable α]
    {e : α → ℕ} {z : α → State} (he : Primrec e) (hz : Primrec z) :
    Primrec (fun a => follower (e a) (z a)) := follower_primitive.comp he hz

@[local fun_prop] private theorem optionSome_closure {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → β} (hf : Primrec f) : Primrec (fun x => some (f x)) := Primrec.option_some.comp hf

@[local fun_prop] private theorem rows_closure {α : Type*} [Primcodable α]
    {z : α → State} (hz : Primrec z) : Primrec (fun x => rows (z x)) := Primrec.fst.comp hz

@[local fun_prop] private theorem latest_closure {α : Type*} [Primcodable α]
    {z : α → State} (hz : Primrec z) : Primrec (fun x => latest (z x)) :=
  Primrec.fst.comp (Primrec.snd.comp hz)

@[local fun_prop] private theorem events_closure {α : Type*} [Primcodable α]
    {z : α → State} (hz : Primrec z) : Primrec (fun x => events (z x)) :=
  Primrec.snd.comp (Primrec.snd.comp hz)

@[local fun_prop] private theorem rowAt_closure {α : Type*} [Primcodable α]
    {z : α → State} {i : α → ℕ} (hz : Primrec z) (hi : Primrec i) :
    Primrec (fun x => rowAt (z x) (i x)) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp hz) hi)
    (Primrec.const (0, (none, [])))

private theorem fresh_endpoint_primitive : Primrec₂ freshEndpoint := by
  unfold Primrec₂ freshEndpoint contents
  fun_prop

@[local fun_prop] private theorem freshEndpoint_closure {α : Type*} [Primcodable α]
    {z : α → State} {i : α → ℕ} (hz : Primrec z) (hi : Primrec i) :
    Primrec (fun x => freshEndpoint (z x) (i x)) := fresh_endpoint_primitive.comp hz hi

set_option maxHeartbeats 1600000 in
private theorem next_primitive : Primrec₂ next := by
  unfold Primrec₂ next visit
  fun_prop

private theorem state_primitive : Primrec state := by
  apply (Primrec.nat_rec₁ initialState next_primitive).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change next n (Nat.rec initialState next n) = next n (state n)
    rw [ih]

@[local fun_prop] private theorem state_closure {α : Type*} [Primcodable α]
    {f : α → ℕ} (hf : Primrec f) : Primrec (fun x => state (f x)) := state_primitive.comp hf

theorem observed_row_spec (e s y : ℕ) : y ∈ observedRow e s ↔ y ∈ stage e s := by
  simp only [observedRow, List.mem_filter, List.mem_range, stageBit, decide_eq_true_eq]
  constructor
  · intro h
    exact (stage_test_spec e s y).2.mp h.2
  · intro h
    exact ⟨(stage_bounds e s).1 h, (stage_test_spec e s y).2.mpr h⟩

theorem noninitial_list_test_spec (L : List ℕ) :
    noninitialListTest L = true ↔ ¬ IsLowerSet {y | y ∈ L} := by
  rw [noninitial_witness]
  simp only [noninitialListTest, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨b, hb, a, ha, hna⟩
    exact ⟨a, b, ha, by simpa using hna, hb⟩
  · rintro ⟨a, b, hab, hna, hb⟩
    exact ⟨b, hb, a, hab, by simpa using hna⟩

theorem noninitial_list_test_computable : Computable noninitialListTest := by
  exact noninitial_list_primitive.to_comp

private theorem finite_observation_spec (e s x : ℕ) :
    {y | y ∈ ((List.range (x + 1)).filter (stageBit e s))} = stage e s ∩ Set.Iic x := by
  ext y
  simp only [Set.mem_ofPred_eq, List.mem_filter, List.mem_range, stageBit, decide_eq_true_eq,
    (stage_test_spec e s y).2, Set.mem_inter_iff, Set.mem_Iic]
  constructor
  · rintro ⟨hy, hs⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hy⟩
    exact ⟨by omega, hs⟩

private theorem different_test_spec (e j s x : ℕ) :
    differentTest e j s x = true ↔ stage e s ∩ Set.Iic x ≠ stage j s ∩ Set.Iic x := by
  simp only [differentTest, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨y, hy, hb⟩ heq
    have hne : stageBit e s y ≠ stageBit j s y := by simpa using hb
    apply hne
    apply Bool.eq_iff_iff.mpr
    have hm : y ∈ stage e s ∩ Set.Iic x ↔ y ∈ stage j s ∩ Set.Iic x := by rw [heq]
    have hyx : y ≤ x := by omega
    simpa only [stageBit, decide_eq_true_eq, (stage_test_spec e s y).2,
      (stage_test_spec j s y).2, Set.mem_inter_iff, Set.mem_Iic, hyx, and_true] using hm
  · intro heq
    by_contra hn
    apply heq
    ext y
    by_cases hy : y ≤ x
    · have hb : stageBit e s y = stageBit j s y := by
        by_contra hb
        apply hn
        exact ⟨y, by omega, by simpa using hb⟩
      have hm := Bool.eq_iff_iff.mp hb
      simpa only [stageBit, decide_eq_true_eq, (stage_test_spec e s y).2,
        (stage_test_spec j s y).2, Set.mem_inter_iff, Set.mem_Iic, hy, and_true] using hm
    · simp [hy]

theorem pass_test_spec (e s x : ℕ) : passTest e s x = true ↔ Passes e s x := by
  simp only [passTest, Bool.and_eq_true, noninitialTest, noninitial_list_test_spec,
    finite_observation_spec, List.all_eq_true, List.mem_range, different_test_spec, Passes]

theorem unpack_pack_state (z : State) : unpackState (packState z) = z := by
  unfold unpackState packState
  rw [Encodable.encodek]
  rfl

theorem state_code_recursion : stateCode 0 = packState initialState ∧
    ∀ s, stateCode (s + 1) = nextCode s (stateCode s) := by
  constructor
  · rfl
  · intro s
    simp only [stateCode, state, nextCode, unpack_pack_state]

theorem state_code_decoding (s : ℕ) : unpackState (stateCode s) = state s := by
  exact unpack_pack_state (state s)

theorem next_computable : Computable₂ next := by
  exact next_primitive.to_comp

theorem next_code_computable : Computable₂ nextCode := by
  have hp : Primrec₂ nextCode := by
    unfold Primrec₂ nextCode packState unpackState
    exact Primrec.encode.comp (next_primitive.comp Primrec.fst
      (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const initialState)))
  exact hp.to_comp

theorem state_code_computable : Computable stateCode := by
  exact (Primrec.encode.comp state_primitive).to_comp

theorem state_computable : Computable state := by
  exact state_primitive.to_comp

private theorem row_test_primitive :
    Primrec (fun t : ℕ × (ℕ × ℕ) => decide (t.2.2 ∈ rowStage t.1 t.2.1)) := by
  have hl : Primrec (fun t : ℕ × (ℕ × ℕ) => contents (rowAt (state t.2.1) t.1)) := by
    unfold contents
    fun_prop
  have hm : Primrec (fun t : ℕ × (ℕ × ℕ) =>
      decide (t.2.2 ∈ contents (rowAt (state t.2.1) t.1))) :=
    PrimitiveRecursiveAutomation.listMem (Primrec.snd.comp Primrec.snd) hl
  apply hm.of_eq
  intro t
  exact congrArg (@decide (t.2.2 ∈ contents (rowAt (state t.2.1) t.1)))
    (Subsingleton.elim _ _)

theorem row_stage_computable : ComputablePred
    (fun t : ℕ × (ℕ × ℕ) => t.2.2 ∈ rowStage t.1 t.2.1) := by
  exact row_test_primitive.to_comp.computablePred

def StateProgramIndex (r : ℕ) : Prop := ∀ s, phi r s = Part.some (stateCode s)

theorem state_program_index_exists : ∃ r, StateProgramIndex r := by
  obtain ⟨r, hr⟩ := phi_complete (Partrec.nat_iff.mp state_code_computable.partrec)
  exact ⟨r, fun s => congrFun hr s⟩

attribute [local irreducible] rowStage

theorem preliminary_recognizer_partial : Partrec₂ preliminaryRecognizer := by
  have hi : Computable (fun q : (ℕ × ℕ) × ℕ => (q.1.1, (q.2, q.1.2))) :=
    (Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  have hbase := row_test_primitive.to_comp.comp hi
  have htest : Computable (fun q : (ℕ × ℕ) × ℕ =>
      decide (q.1.2 ∈ rowStage q.1.1 q.2)) := hbase.of_eq (fun q => by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq])
  have hs := (Partrec.rfind htest.to₂.partrec₂).map (Computable.const 0).to₂
  apply hs.of_eq
  intro p
  unfold preliminaryRecognizer
  apply congrArg (fun f : ℕ →. Bool => (Nat.rfind f).map (fun _ => 0))
  funext s
  simp only [PFun.coe_val]
  apply congrArg Part.some
  apply Bool.eq_iff_iff.mpr
  simp only [rowStage, Set.mem_ofPred_eq]

theorem preliminary_recognizer_spec (x y : ℕ) :
    preliminaryRecognizer x y = if y ∈ preliminaryRow x then Part.some 0 else Part.none := by
  classical
  unfold preliminaryRecognizer
  by_cases hy : y ∈ preliminaryRow x
  · rw [ite_eq_left hy]
    apply Part.eq_some_iff.mpr
    obtain ⟨s, hs⟩ := hy
    have hd : (Nat.rfind (fun s => Part.some (decide (y ∈ contents (rowAt (state s) x))))).Dom := by
      apply Nat.rfind_dom.mpr
      exact ⟨s, by simpa [rowStage, eq_comm] using hs, fun _ => trivial⟩
    exact Part.mem_map (fun _ => 0) (Part.get_mem hd)
  · rw [ite_eq_right hy]
    apply Part.eq_none_iff'.mpr
    intro hd
    obtain ⟨s, hs, _⟩ := Nat.rfind_dom.mp hd
    apply hy
    refine ⟨s, ?_⟩
    simpa [rowStage, eq_comm] using hs

theorem preliminary_uniform : UniformCE preliminaryRow := by
  have hp : Partrec (fun z : ℕ => preliminaryRecognizer z.unpair.1 z.unpair.2) :=
    preliminary_recognizer_partial.comp (Computable.fst.comp Computable.unpair)
      (Computable.snd.comp Computable.unpair)
  apply hp.dom_re.of_eq
  intro z
  rw [preliminary_recognizer_spec]
  by_cases hz : z.unpair.2 ∈ preliminaryRow z.unpair.1 <;> simp [hz]

end
end Lemmatheca.ComputabilityTheory.FriedbergNumberings
