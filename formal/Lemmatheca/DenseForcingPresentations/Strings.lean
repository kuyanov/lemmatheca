import Lemmatheca.DenseForcingPresentations.Names
import Lemmatheca.ForcingNames.CohenName

namespace Lemmatheca.SetTheory.DenseForcingPresentations
open Set Order
open Lemmatheca.SetTheory.ForcingAndGenericFilters
open Lemmatheca.SetTheory.ForcingNames
open Lemmatheca.SetTheory.FinitePartialMaps
universe u
noncomputable section
local instance denseStringsPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
local instance denseStringsNatDecidableEq : DecidableEq ℕ := inferInstance

def BinaryString := Σ n : ℕ, Fin n → Bool

def stringMap : (n : ℕ) → (Fin n → Bool) → Cohen
  | 0, _ => ∅
  | n+1, f => Finmap.insert n (f (Fin.last n)) (stringMap n (fun i => f i.castSucc))

def stringCondition (s : BinaryString) : Cohen := stringMap s.1 s.2

theorem string_map_lookup (n : ℕ) (f : Fin n → Bool) (k : ℕ) :
    (stringMap n f).lookup k = if h : k < n then some (f ⟨k,h⟩) else none := by
  induction n generalizing k with
  | zero => simp [stringMap]
  | succ n ih =>
    by_cases hkn : k = n
    · subst k
      rw [stringMap,Finmap.lookup_insert,dite_eq_left (Nat.lt_succ_self n)]
      rfl
    · rw [stringMap,Finmap.lookup_insert_of_ne _ hkn,ih]
      by_cases h : k < n
      · rw [dite_eq_left h,dite_eq_left (Nat.lt_succ_of_lt h)]
        exact congrArg (fun i : Fin (n+1) => some (f i)) (Fin.ext rfl)
      · have h' : ¬ k < n+1 := by omega
        rw [dite_eq_right h,dite_eq_right h']

theorem string_condition_keys (s : BinaryString) :
    (stringCondition s).keys = Finset.range s.1 := by
  ext k
  rw [Finmap.mem_keys,Finmap.mem_iff]
  simp only [stringCondition,string_map_lookup,Finset.mem_range]
  by_cases h : k < s.1 <;> simp [h]

theorem string_condition_injective : Function.Injective stringCondition := by
  intro s t he
  have hlen : s.1 = t.1 := by
    have hk := congrArg (fun p : Cohen => p.keys.card) he
    simpa only [string_condition_keys,Finset.card_range] using hk
  rcases s with ⟨n,f⟩
  rcases t with ⟨m,g⟩
  change n = m at hlen
  subst m
  apply congrArg (Sigma.mk n)
  funext i
  have hl := congrArg (fun p : Cohen => p.lookup i.val) he
  change (stringMap n f).lookup i.val = (stringMap n g).lookup i.val at hl
  simp only [string_map_lookup,dite_eq_left i.isLt] at hl
  exact Option.some.inj hl

instance binaryStringOrder : PartialOrder BinaryString :=
  PartialOrder.lift stringCondition string_condition_injective

def StringPrefix (s t : BinaryString) : Prop :=
  ∃ h : s.1 ≤ t.1, ∀ i : Fin s.1, t.2 ⟨i.val,lt_of_lt_of_le i.isLt h⟩ = s.2 i


private theorem string_graph (s : BinaryString) (k : ℕ) (b : Bool) :
    (k,b) ∈ graph (stringCondition s) ↔ ∃ h : k < s.1, s.2 ⟨k,h⟩ = b := by
  change (Sigma.mk k b ∈ (stringMap s.1 s.2).entries) ↔ _
  rw [← Finmap.lookup_eq_some_iff,string_map_lookup]
  by_cases h : k < s.1 <;> simp [h]

theorem string_order_iff (s t : BinaryString) : t ≤ s ↔ StringPrefix s t := by
  change graph (stringCondition s) ⊆ graph (stringCondition t) ↔ _
  constructor
  · intro h
    have hlen : s.1 ≤ t.1 := by
      by_contra hn
      have hi : t.1 < s.1 := Nat.lt_of_not_ge hn
      have hs := (string_graph s t.1 (s.2 ⟨t.1,hi⟩)).mpr ⟨hi,rfl⟩
      obtain ⟨hlt,_⟩ := (string_graph t _ _).mp (h hs)
      exact Nat.lt_irrefl _ hlt
    refine ⟨hlen,?_⟩
    intro i
    obtain ⟨ht,hbit⟩ := (string_graph t i.val (s.2 i)).mp
      (h ((string_graph s _ _).mpr ⟨i.isLt,rfl⟩))
    exact hbit
  · rintro ⟨hlen,hbit⟩ ⟨k,b⟩ hkb
    obtain ⟨hk,hb⟩ := (string_graph s k b).mp hkb
    exact (string_graph t k b).mpr ⟨lt_of_lt_of_le hk hlen,(hbit ⟨k,hk⟩).trans hb⟩

def stringEmbedding : BinaryString ↪o Cohen where
  toFun := stringCondition
  inj' := string_condition_injective
  map_rel_iff' := Iff.rfl

def fillString (p : Cohen) : BinaryString :=
  ⟨p.keys.sup Nat.succ, fun i => (p.lookup i.val).getD false⟩

theorem fill_string_extends (p : Cohen) : stringCondition (fillString p) ≤ p := by
  change graph p ⊆ graph (stringCondition (fillString p))
  rintro ⟨k,b⟩ hkb
  have hlook : p.lookup k = some b := Finmap.lookup_eq_some_iff.mpr hkb
  have hk : k ∈ p.keys := Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hlook)
  have hlt : k < p.keys.sup Nat.succ := Nat.lt_of_succ_le (Finset.le_sup hk)
  apply (string_graph (fillString p) k b).mpr
  refine ⟨hlt,?_⟩
  change (p.lookup k).getD false = b
  rw [hlook]
  rfl

theorem string_embedding_dense : DenseEmbedding stringEmbedding := by
  intro p
  exact ⟨fillString p,fill_string_extends p⟩

theorem string_image_initial_segments : Set.range stringCondition =
    {p : Cohen | ∃ n, p.keys = Finset.range n} := by
  ext p
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s.1,string_condition_keys s⟩
  · rintro ⟨n,hn⟩
    let s : BinaryString := ⟨n,fun i => (p.lookup i.val).getD false⟩
    refine ⟨s,?_⟩
    apply Finmap.ext_lookup
    intro k
    change (stringMap n (fun i => (p.lookup i.val).getD false)).lookup k = p.lookup k
    rw [string_map_lookup]
    by_cases hk : k < n
    · have hkp : k ∈ p := Finmap.mem_keys.mp (hn.symm ▸ Finset.mem_range.mpr hk)
      obtain ⟨b,hb⟩ := Finmap.mem_iff.mp hkp
      rw [dite_eq_left hk,hb]
      rfl
    · have hkp : k ∉ p := by
        intro hmem
        have hkeys := Finmap.mem_keys.mpr hmem
        rw [hn] at hkeys
        exact hk (Finset.mem_range.mp hkeys)
      rw [dite_eq_right hk,Finmap.lookup_eq_none.mpr hkp]

def stringUnion (H : PFilter BinaryString) : Set (ℕ × Bool) :=
  {nb | ∃ s ∈ H, nb ∈ graph (stringCondition s)}

theorem string_union_lift (H : PFilter BinaryString) :
    stringUnion H = cohenUnion (liftFilter stringEmbedding H) := by
  ext nb
  constructor
  · rintro ⟨s,hs,hnb⟩
    exact ⟨stringCondition s,(lift_filter_members stringEmbedding H _).mpr ⟨s,hs,le_rfl⟩,hnb⟩
  · rintro ⟨p,hp,hnb⟩
    obtain ⟨s,hs,hsp⟩ := (lift_filter_members stringEmbedding H p).mp hp
    change graph p ⊆ graph (stringCondition s) at hsp
    exact ⟨s,hs,hsp hnb⟩

def stringPosetSet : ZFSet.{u} := ZFSet.range (fun s => conditionSet.{u} (stringCondition s))

theorem string_coding_bijective : Function.Bijective (fun s : BinaryString =>
    (⟨conditionSet.{u} (stringCondition s),
      ZFSet.mem_range_self (f := fun s => conditionSet.{u} (stringCondition s)) s⟩ : stringPosetSet.{u})) := by
  constructor
  · intro s t he
    exact string_condition_injective (conditionSet_injective (congrArg Subtype.val he))
  · intro z
    obtain ⟨s,hs⟩ := ZFSet.mem_range.mp z.property
    exact ⟨s,Subtype.ext hs⟩

def stringCoding : BinaryString ≃ stringPosetSet.{u} := Equiv.ofBijective _ string_coding_bijective

theorem string_coding_value (s : BinaryString) :
    (stringCoding.{u} s).val = conditionSet (stringCondition s) := by rfl

end
end Lemmatheca.SetTheory.DenseForcingPresentations
