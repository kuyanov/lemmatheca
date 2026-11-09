import Lemmatheca.OracleProgramNumberings.Parameters
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion

/-! The actual all-oracle padding compiler and bounded finite avoidance. -/
namespace Lemmatheca.ComputabilityTheory.OraclePadding

open OracleComputation OracleProgramNumberings

set_option backward.isDefEq.respectTransparency false

theorem constantIndex_injective : Function.Injective constantIndex := by
  intro a b h
  have hc : constantCode a = constantCode b := code_bijective.1 h
  have he := congrArg (fun c => eval (∅ : Set ℕ) c 0) hc
  simpa only [constant_eval, Part.some_inj] using he

theorem specialize_injective {e a f b : ℕ} (h : specialize e a = specialize f b) :
    e = f ∧ a = b := by
  have hs := code_bijective.1 h
  change Code.comp (decodeCode e) (.pair (constantCode a) identityCode) =
    Code.comp (decodeCode f) (.pair (constantCode b) identityCode) at hs
  injection hs with he hp
  have hc : constantCode a = constantCode b := by injection hp
  refine ⟨?_, constantIndex_injective (congrArg encodeCode hc)⟩
  simpa only [encode_decode] using congrArg encodeCode he

def pad (e t : ℕ) : ℕ := specialize (compIndex e 3) t

theorem pad_decode (e t : ℕ) :
    decodeCode (pad e t) =
      .comp (.comp (decodeCode e) .right) (.pair (constantCode t) identityCode) := by
  have hcomp : decodeCode (compIndex e 3) = .comp (decodeCode e) .right := by
    have he : compIndex e 3 = encodeCode (.comp (decodeCode e) .right) := by
      simp only [compIndex, encodeCode, encode_decode]
    rw [he, decode_encode]
  simp only [pad, specialize, decode_encode, hcomp]

theorem pad_primitive : Primrec₂ pad := by
  exact specialize_primitive.comp
    (compIndex_primitive.comp Primrec.fst (Primrec.const 3)) Primrec.snd

theorem pad_injective {e t f u : ℕ} (h : pad e t = pad f u) : e = f ∧ t = u := by
  have hs := specialize_injective h
  have he : 7 + 4 * Nat.pair e 3 = 7 + 4 * Nat.pair f 3 := hs.1
  have hp : Nat.pair e 3 = Nat.pair f 3 := by omega
  exact ⟨(Nat.pair_eq_pair.mp hp).1, hs.2⟩

theorem pad_eval (A : Set ℕ) (e t x : ℕ) : phi A (pad e t) x = phi A e x := by
  change eval A (decodeCode (pad e t)) x = _
  rw [pad_decode]
  simp only [eval, constant_eval, identity_eval, Part.bind_some, Part.map_some,
    Nat.unpair_pair, phi]

theorem equivalent_indices_infinite (e : ℕ) :
    Set.Infinite {j | ∀ A : Set ℕ, ∀ x, phi A j x = phi A e x} := by
  exact Set.infinite_of_injective_forall_mem
    (fun _ _ h => (pad_injective h).2) (fun t A x => pad_eval A e t x)

noncomputable def escapingTag (e lcode : ℕ) : ℕ :=
  PrimitiveRecursion.boundedSearch
    (fun p t => pad p.1 t ∉ FiniteSequenceCoding.decode p.2)
    (e, lcode) (FiniteSequenceCoding.length lcode + 1)

noncomputable def freshIndex (e lcode : ℕ) : ℕ := pad e (escapingTag e lcode)

theorem escapingTag_primitive : Primrec₂ escapingTag := by
  have hm : PrimrecRel (fun (L : List ℕ) (n : ℕ) => n ∈ L) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  have hR : PrimrecRel
      (fun (p : ℕ × ℕ) t => pad p.1 t ∉ FiniteSequenceCoding.decode p.2) :=
    (hm.comp ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.fst))
      (pad_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).not
  exact (PrimitiveRecursion.boundedSearch_primrec hR).comp Primrec.id
    (Primrec.succ.comp (FiniteSequenceCoding.primrec_length.comp Primrec.snd))

theorem freshIndex_primitive : Primrec₂ freshIndex := by
  exact pad_primitive.comp Primrec.fst escapingTag_primitive

theorem escapingTag_spec (e lcode : ℕ) :
    escapingTag e lcode ≤ FiniteSequenceCoding.length lcode ∧
      freshIndex e lcode ∉ FiniteSequenceCoding.decode lcode ∧
      ∀ t < escapingTag e lcode, pad e t ∈ FiniteSequenceCoding.decode lcode := by
  classical
  let R : (ℕ × ℕ) → ℕ → Prop :=
    fun p t => pad p.1 t ∉ FiniteSequenceCoding.decode p.2
  have hex : ∃ t < FiniteSequenceCoding.length lcode + 1, R (e, lcode) t := by
    by_contra hn
    have hm : ∀ t < FiniteSequenceCoding.length lcode + 1,
        pad e t ∈ FiniteSequenceCoding.decode lcode := by
      intro t ht
      by_contra hh
      exact hn ⟨t, ht, hh⟩
    have hc := Finset.le_card_of_inj_on_range
      (s := (FiniteSequenceCoding.decode lcode).toFinset)
      (n := FiniteSequenceCoding.length lcode + 1) (pad e)
      (fun t ht => List.mem_toFinset.mpr (hm t ht))
      (fun _ _ _ _ hij => (pad_injective hij).2)
    have hl := List.toFinset_card_le (FiniteSequenceCoding.decode lcode)
    change _ ≤ FiniteSequenceCoding.length lcode at hl
    omega
  have hs := PrimitiveRecursion.boundedSearch_spec R (e, lcode)
    (FiniteSequenceCoding.length lcode + 1)
  have hlt : PrimitiveRecursion.boundedSearch R (e, lcode)
      (FiniteSequenceCoding.length lcode + 1) < FiniteSequenceCoding.length lcode + 1 := by
    by_contra hn
    have heq : PrimitiveRecursion.boundedSearch R (e, lcode)
        (FiniteSequenceCoding.length lcode + 1) = FiniteSequenceCoding.length lcode + 1 := by
      omega
    obtain ⟨t, ht, hr⟩ := hex
    exact hs.2.2.mp heq t ht hr
  have hm := hs.2.1 hlt
  refine ⟨by simpa only [escapingTag] using Nat.le_of_lt_succ hlt, ?_, ?_⟩
  · exact hm.1
  · intro t ht
    exact not_not.mp (hm.2 t ht)

theorem freshIndex_eval (A : Set ℕ) (e lcode x : ℕ) :
    phi A (freshIndex e lcode) x = phi A e x := by
  exact pad_eval A e (escapingTag e lcode) x

end Lemmatheca.ComputabilityTheory.OraclePadding
