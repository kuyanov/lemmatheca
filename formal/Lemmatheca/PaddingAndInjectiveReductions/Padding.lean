import Lemmatheca.UniversalComputation.UniversalComputation
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion

/-! Explicit padding and finite avoidance in the established numerical numbering. -/
namespace Lemmatheca.ComputabilityTheory.PaddingAndInjectiveReductions

open Encodable Denumerable
open Nat.Partrec (Code)
open UniversalComputation

def paddingProgram (c : Code) (t : ℕ) : Code := Code.curry (.comp c .right) t

def pad (e t : ℕ) : ℕ := encode (paddingProgram (ofNat Code e) t)

theorem pad_eval (e t x : ℕ) : phi (pad e t) x = phi e x := by
  simp only [phi, pad, paddingProgram, ofNat_encode, Code.eval_curry, Code.eval]
  change (Part.some (Nat.unpair (Nat.pair t x)).2).bind
    (fun z => Code.eval (ofNat Code e) z) = _
  rw [Nat.unpair_pair, Part.bind_some]

theorem pad_primitive : Primrec₂ pad := by
  have hc : Primrec (fun e => Code.comp (ofNat Code e) Code.right) :=
    Code.primrec₂_comp.comp (Primrec.ofNat Code) (Primrec.const Code.right)
  exact Primrec.encode.comp₂
    (Code.primrec₂_curry.comp₂ (hc.comp₂ Primrec₂.left) Primrec₂.right)

theorem pad_injective {e t f u : ℕ} (h : pad e t = pad f u) : e = f ∧ t = u := by
  have hs := Code.curry_inj (Encodable.encode_injective h)
  have hc : ofNat Code e = ofNat Code f := by injection hs.1
  exact ⟨by simpa using congrArg encode hc, hs.2⟩

theorem equivalent_indices_infinite (e : ℕ) :
    Set.Infinite {j | ∀ x, phi j x = phi e x} := by
  exact Set.infinite_of_injective_forall_mem
    (fun _ _ h => (pad_injective h).2) (fun t x => pad_eval e t x)

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

theorem freshIndex_eval (e lcode x : ℕ) : phi (freshIndex e lcode) x = phi e x := by
  exact pad_eval e (escapingTag e lcode) x

theorem specialize_injective {e a f b : ℕ} (h : specialize e a = specialize f b) :
    e = f ∧ a = b := by
  have hs := Code.curry_inj (Encodable.encode_injective h)
  exact ⟨by simpa using congrArg encode hs.1, hs.2⟩

end Lemmatheca.ComputabilityTheory.PaddingAndInjectiveReductions
