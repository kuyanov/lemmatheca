import Lemmatheca.PostsTheorem.FiniteCertificates
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion

/-! Finite binary words and bounded certificates in the existing oracle numbering. -/
namespace Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees

open OracleComputation OracleProgramNumberings PostsTheorem UniversalComputation

set_option backward.isDefEq.respectTransparency false

noncomputable section

abbrev wordLength := FiniteSequenceCoding.length
abbrev wordBit := PostsTheorem.beta

def word (u : ℕ) : List ℕ := (FiniteSequenceCoding.decode u).map (· % 2)

def BinaryWord (l : List ℕ) : Prop := ∀ b ∈ l, b = 0 ∨ b = 1

def Prefix (u v : ℕ) : Prop :=
  wordLength u ≤ wordLength v ∧ ∀ q < wordLength u, wordBit u q = wordBit v q

def Realizes (u : ℕ) (A : Set ℕ) : Prop :=
  ∀ q < wordLength u, wordBit u q = indicator (fun x => x ∈ A) q

def appendBit (u b : ℕ) : ℕ :=
  FiniteSequenceCoding.append u (FiniteSequenceCoding.code [b % 2])

def certificateValue (u e x : ℕ) : ℕ := finiteValue u (wordLength u) e x

def unionSet (u : ℕ → ℕ) : Set ℕ := {x | wordBit (u (x + 1)) x = 1}

theorem word_interpretation (u q : ℕ) :
    BinaryWord (word u) ∧ (word u).length = wordLength u ∧
      (word u)[q]?.getD 0 = wordBit u q := by
  constructor
  · intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
    have hm := Nat.mod_lt a (by decide : 0 < 2)
    omega
  · constructor
    · simp [word, wordLength, FiniteSequenceCoding.length]
    · unfold word wordBit beta FiniteSequenceCoding.entry
      cases h : (FiniteSequenceCoding.decode u)[q]? <;> simp [List.getElem?_map, h]

theorem binary_word_recovery (l : List ℕ) (hl : BinaryWord l) :
    word (FiniteSequenceCoding.code l) = l := by
  rw [word, FiniteSequenceCoding.decode_code]
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := hl a (by simp)
    have ht : BinaryWord l := fun b hb => hl b (by simp [hb])
    simp only [List.map_cons]
    rw [ih ht]
    rcases ha with rfl | rfl <;> rfl

private theorem word_get (u i : ℕ) (hi : i < (word u).length) :
    (word u)[i] = wordBit u i := by
  have h := (word_interpretation u i).2.2
  simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using h

theorem prefix_native (u v : ℕ) : Prefix u v ↔ List.IsPrefix (word u) (word v) := by
  have hu := (word_interpretation u 0).2.1
  have hv := (word_interpretation v 0).2.1
  rw [List.prefix_iff_getElem]
  constructor
  · rintro ⟨hlen, hbits⟩
    refine ⟨by omega, ?_⟩
    intro i hi
    rw [word_get, word_get]
    exact hbits i (by omega)
  · rintro ⟨hlen, hbits⟩
    refine ⟨by omega, ?_⟩
    intro i hi
    rw [← word_get u i (by omega), ← word_get v i (by omega)]
    exact hbits i (by omega)

theorem prefix_refl (u : ℕ) : Prefix u u := by
  exact ⟨le_rfl, fun _ _ => rfl⟩

theorem prefix_trans {u v w : ℕ} (huv : Prefix u v) (hvw : Prefix v w) : Prefix u w := by
  exact ⟨huv.1.trans hvw.1, fun q hq =>
    (huv.2 q hq).trans (hvw.2 q (lt_of_lt_of_le hq huv.1))⟩

theorem prefix_primitive : PrimrecPred (fun p : ℕ × ℕ => Prefix p.1 p.2) := by
  have hr : PrimrecRel (fun p : ℕ × ℕ => fun q => wordBit p.1 q = wordBit p.2 q) :=
    Primrec.eq.comp
      (beta_primitive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (beta_primitive.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hb := (PrimitiveRecursion.bounded_forall_primrec hr).comp Primrec.id
    (FiniteSequenceCoding.primrec_length.comp Primrec.fst)
  exact (Primrec.nat_le.comp (FiniteSequenceCoding.primrec_length.comp Primrec.fst)
    (FiniteSequenceCoding.primrec_length.comp Primrec.snd)).and hb

theorem appendBit_primitive : Primrec₂ appendBit := by
  have h := FiniteSequenceCoding.primrec_append.comp Primrec.fst
    (FiniteSequenceCoding.primrec_cons.comp
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
  apply h.to₂.of_eq
  intro u b
  change FiniteSequenceCoding.append u (FiniteSequenceCoding.cons (b % 2) 0) =
    FiniteSequenceCoding.append u (FiniteSequenceCoding.code [b % 2])
  rw [FiniteSequenceCoding.code_cons]
  rfl

private theorem append_decode (u b : ℕ) :
    FiniteSequenceCoding.decode (appendBit u b) =
      FiniteSequenceCoding.decode u ++ [b % 2] := by
  simp [appendBit, FiniteSequenceCoding.append]

theorem appendBit_spec (u b : ℕ) :
    wordLength (appendBit u b) = wordLength u + 1 ∧
      Prefix u (appendBit u b) ∧ wordBit (appendBit u b) (wordLength u) = b % 2 := by
  have hlen : wordLength (appendBit u b) = wordLength u + 1 := by
    simp [wordLength, FiniteSequenceCoding.length, append_decode]
  refine ⟨hlen, ?_, ?_⟩
  · apply (prefix_native _ _).mpr
    have hw : word (appendBit u b) = word u ++ [b % 2] := by
      simp [word, append_decode]
    rw [hw]
    exact List.prefix_append _ _
  · simp [wordBit, beta, FiniteSequenceCoding.entry, append_decode,
      wordLength, FiniteSequenceCoding.length]

theorem appendBit_word (u b : ℕ) : word (appendBit u b) = word u ++ [b % 2] := by
  simp [word, append_decode]

theorem realizes_prefix {u v : ℕ} {A : Set ℕ} (huv : Prefix u v)
    (hv : Realizes v A) : Realizes u A := by
  intro q hq
  exact (huv.2 q hq).trans (hv q (lt_of_lt_of_le hq huv.1))

theorem prefix_finiteOracle {u v : ℕ} (h : Prefix u v) : Realizes u (finiteOracle v) := by
  intro q hq
  exact (h.2 q hq).trans (finiteOracle_indicator v q).symm

theorem certificate_primitive :
    Primrec (fun p : (ℕ × ℕ) × ℕ => certificateValue p.1.1 p.1.2 p.2) := by
  have hp : Primrec (fun p : (ℕ × ℕ) × ℕ =>
      pack4 p.1.1 (wordLength p.1.1) p.1.2 p.2) :=
    Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst)
      (Primrec₂.natPair.comp
        (FiniteSequenceCoding.primrec_length.comp (Primrec.fst.comp Primrec.fst))
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  apply (finiteValue_primitive.comp hp).of_eq
  intro p
  simp only [finiteValueInput, pack4, Nat.unpair_pair, certificateValue]

theorem certificate_sound (A : Set ℕ) (u e x y : ℕ) (hu : Realizes u A)
    (h : certificateValue u e x = y + 1) : y ∈ phi A e x := by
  have hb : boundedValue A (wordLength u) e x = y + 1 := by
    rw [← finiteValue_agreement A u (wordLength u) e x hu]
    exact h
  exact bounded_sound A _ _ x y ((boundedValue_output A _ e x y).mp hb)

theorem certificate_persists (u v e x y : ℕ) (huv : Prefix u v)
    (h : certificateValue u e x = y + 1) : certificateValue v e x = y + 1 := by
  have hu := prefix_finiteOracle huv
  have hb : boundedValue (finiteOracle v) (wordLength u) e x = y + 1 := by
    rw [← finiteValue_agreement (finiteOracle v) u (wordLength u) e x hu]
    exact h
  have hk := (boundedValue_output (finiteOracle v) (wordLength u) e x y).mp hb
  have hm := bounded_monotone (indicator (fun q => q ∈ finiteOracle v))
    (wordLength u) (wordLength v - wordLength u) (decodeCode e) x y hk
  have hlen : wordLength u + (wordLength v - wordLength u) = wordLength v := by
    have := huv.1
    omega
  change finiteValue v (wordLength v) e x = y + 1
  rw [finiteValue_identity, OracleProgramNumberings.boundedValue_output]
  simpa only [bounded, hlen] using hm

theorem prefix_adequacy (A : Set ℕ) (u e x y : ℕ) (hu : Realizes u A)
    (hy : y ∈ phi A e x) :
    ∃ v, Prefix u v ∧ Realizes v A ∧ certificateValue v e x = y + 1 := by
  obtain ⟨k, hk⟩ := (phi_output_certificate A e x y).mp hy
  have hb := (boundedValue_output A k e x y).mp hk
  have hm := bounded_monotone (indicator (fun q => q ∈ A)) k (wordLength u)
    (decodeCode e) x y hb
  let K := k + wordLength u
  let v := prefixCode A K
  have hv := prefixCode_spec A K
  have hvlen : wordLength v = K := hv.1
  have hvreal : Realizes v A := by
    intro q hq
    exact hv.2 q (by omega)
  refine ⟨v, ⟨by rw [hvlen]; dsimp [K]; omega, ?_⟩, hvreal, ?_⟩
  · intro q hq
    exact (hu q hq).trans (hv.2 q (by dsimp [K]; omega)).symm
  · change finiteValue v (wordLength v) e x = y + 1
    rw [hvlen, finiteValue_agreement A v K e x hv.2,
      OracleProgramNumberings.boundedValue_output]
    exact hm

theorem prefix_output_iff (A : Set ℕ) (e x y : ℕ) :
    y ∈ phi A e x ↔ ∃ u, Realizes u A ∧ certificateValue u e x = y + 1 := by
  constructor
  · intro h
    have h0 : Realizes 0 A := by
      intro q hq
      simp [wordLength, FiniteSequenceCoding.length] at hq
    obtain ⟨v, _, hv, hc⟩ := prefix_adequacy A 0 e x y h0 h
    exact ⟨v, hv, hc⟩
  · rintro ⟨u, hu, hc⟩
    exact certificate_sound A u e x y hu hc

private theorem prefix_chain (u : ℕ → ℕ) (hp : ∀ n, Prefix (u n) (u (n + 1)))
    {n m : ℕ} (hnm : n ≤ m) : Prefix (u n) (u m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact prefix_refl _
  | succ m hnm ih => exact prefix_trans ih (hp m)

private theorem union_indicator (u : ℕ → ℕ) (x : ℕ) :
    indicator (fun q => q ∈ unionSet u) x = wordBit (u (x + 1)) x := by
  classical
  rcases beta_bits (u (x + 1)) x with h | h <;> simp [indicator, unionSet, h]

theorem coherent_union (u : ℕ → ℕ) (hp : ∀ n, Prefix (u n) (u (n + 1)))
    (hg : ∀ n, n ≤ wordLength (u n)) :
    (∀ n, Realizes (u n) (unionSet u)) ∧
      ∀ A : Set ℕ, (∀ n, Realizes (u n) A) → A = unionSet u := by
  constructor
  · intro n q hq
    let m := max n (q + 1)
    have hn := prefix_chain u hp (show n ≤ m by exact le_max_left _ _)
    have hqq := prefix_chain u hp (show q + 1 ≤ m by exact le_max_right _ _)
    have hq' : q < wordLength (u (q + 1)) := by have := hg (q + 1); omega
    exact (hn.2 q hq).trans ((hqq.2 q hq').symm.trans (union_indicator u q).symm)
  · intro A hA
    apply Set.ext
    intro q
    have hq : q < wordLength (u (q + 1)) := by have := hg (q + 1); omega
    have he := hA (q + 1) q hq
    classical
    by_cases hmem : q ∈ A <;> simp_all [indicator, unionSet]

theorem union_bit (u : ℕ → ℕ) (x : ℕ) :
    indicator (fun q => q ∈ unionSet u) x = wordBit (u (x + 1)) x := by
  exact union_indicator u x

end
end Lemmatheca.ComputabilityTheory.IncomparableTuringDegrees

/-! Valid numerical binary-word codes are part of the finite-prefix interface. -/
namespace Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths

open IncomparableTuringDegrees PostsTheorem UniversalComputation

noncomputable section

def ValidCode (u : ℕ) : Prop := BinaryWord (FiniteSequenceCoding.decode u)

theorem valid_code_primitive : PrimrecPred ValidCode := by
  have hb : PrimrecPred (fun b : ℕ => b = 0 ∨ b = 1) :=
    (Primrec.eq.comp Primrec.id (Primrec.const 0)).or
      (Primrec.eq.comp Primrec.id (Primrec.const 1))
  exact hb.forall_mem_list.comp (Primrec.ofNat (List ℕ))

theorem valid_code_interpretation (u : ℕ) (hu : ValidCode u) :
    word u = FiniteSequenceCoding.decode u := by
  simpa only [FiniteSequenceCoding.code_decode] using binary_word_recovery
    (FiniteSequenceCoding.decode u) hu

theorem prefix_code_valid (X : Set ℕ) (n : ℕ) :
    ValidCode (prefixCode X n) := by
  classical
  intro b hb
  simp only [prefixCode, FiniteSequenceCoding.decode_code, List.mem_map,
    List.mem_range] at hb
  obtain ⟨q, _, rfl⟩ := hb
  by_cases h : q ∈ X <;> simp [indicator, h]

theorem append_valid (u b : ℕ) (hu : ValidCode u) : ValidCode (appendBit u b) := by
  intro a ha
  simp only [appendBit, FiniteSequenceCoding.append, FiniteSequenceCoding.decode_code,
    List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact hu a ha
  · have h := Nat.mod_lt b (by decide : 0 < 2)
    omega

end
end Lemmatheca.ComputabilityTheory.ComputableTreesAndPaths
