import Lemmatheca.CodingTuringComputations.Labeling
import Lemmatheca.CodingTuringComputations.Data
import Lemmatheca.PrimitiveRecursion.PrimitiveRecursion
import Lemmatheca.MachinesAndComputationHistories.MachinesAndComputationHistories

namespace Lemmatheca.ComputabilityTheory.TapeCoding

open TuringMachines (Alphabet Move)
open scoped BigOperators

variable {Γ Q : Type*} {A : Alphabet Γ} [Fintype Γ] [Fintype Q]
variable {T : TuringMachines.Machine A Q}

def instruction (L : Labeling T) (i : Fin (Fintype.card Q)) (j : Fin (Fintype.card Γ)) : ℕ :=
  match T.table (L.state.symm i) (L.symbol.symm j) with
  | none => 0
  | some row => 1 + Nat.pair (L.state row.1).val
      (Nat.pair (L.symbol row.2.1).val (moveCode row.2.2))

noncomputable def lookup (L : Labeling T) (q a : ℕ) : ℕ :=
  ∑ i : Fin (Fintype.card Q), ∑ j : Fin (Fintype.card Γ),
    PrimitiveRecursion.characteristic (fun x : ℕ => x = i.val) q *
    PrimitiveRecursion.characteristic (fun x : ℕ => x = j.val) a * instruction L i j

theorem lookup_actual (L : Labeling T) (q : Q) (a : Γ) :
    lookup L (L.state q).val (L.symbol a).val =
      match T.table q a with
      | none => 0
      | some row => 1 + Nat.pair (L.state row.1).val
          (Nat.pair (L.symbol row.2.1).val (moveCode row.2.2)) := by
  classical
  simp [lookup, PrimitiveRecursion.characteristic, ← Fin.ext_iff, instruction]

theorem lookup_outside (L : Labeling T) (q a : ℕ)
    (h : Fintype.card Q ≤ q ∨ Fintype.card Γ ≤ a) : lookup L q a = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  rcases h with h | h
  · have he : q ≠ i.val := by have := i.isLt; omega
    simp [PrimitiveRecursion.characteristic, he]
  · have he : a ≠ j.val := by have := j.isLt; omega
    simp [PrimitiveRecursion.characteristic, he]

private theorem primrec_finite_sum {α ι : Type*} [Primcodable α]
    (s : Finset ι) (f : ι → α → ℕ) (hf : ∀ i ∈ s, Primrec (f i)) :
    Primrec (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Primrec.const (α := α) 0)
  | @insert a s ha ih =>
    have hpa := hf a (by simp)
    have hps := ih (fun i hi => hf i (by simp [hi]))
    simpa [Finset.sum_insert ha] using Primrec.nat_add.comp hpa hps

theorem lookup_primrec (L : Labeling T) : Primrec₂ (lookup L) := by
  classical
  apply primrec_finite_sum
  intro i _
  apply primrec_finite_sum
  intro j _
  have hi : Primrec (fun p : ℕ × ℕ =>
      PrimitiveRecursion.characteristic (fun x => x = i.val) p.1) :=
    (PrimitiveRecursion.PRRelation_iff _).mpr
      (Primrec.eq.comp Primrec.fst (Primrec.const i.val))
  have hj : Primrec (fun p : ℕ × ℕ =>
      PrimitiveRecursion.characteristic (fun x => x = j.val) p.2) :=
    (PrimitiveRecursion.PRRelation_iff _).mpr
      (Primrec.eq.comp Primrec.snd (Primrec.const j.val))
  exact Primrec.nat_mul.comp (Primrec.nat_mul.comp hi hj) (Primrec.const _)

noncomputable def haltTest (L : Labeling T) (c : ℕ) : Bool :=
  !(validTest (Fintype.card Γ) (Fintype.card Q) c) ||
    (lookup L (stateCode c) (currentCode c) == 0)

noncomputable def haltCode (L : Labeling T) (c : ℕ) : ℕ := if haltTest L c then 1 else 0

theorem haltCode_spec (L : Labeling T) (c : ℕ) :
    (haltCode L c = 1 ↔ haltTest L c = true) ∧
    (haltCode L c = 0 ↔ haltTest L c = false) := by
  cases h : haltTest L c <;> simp [haltCode, h]

noncomputable def transition (L : Labeling T) (c : ℕ) : ℕ :=
  if haltTest L c then c else
    let w := lookup L (stateCode c) (currentCode c)
    let q := (Nat.unpair (w - 1)).1
    let b := (Nat.unpair (Nat.unpair (w - 1)).2).1
    let d := (Nat.unpair (Nat.unpair (w - 1)).2).2
    if d = 0 then pack q (FiniteSequenceCoding.head (leftCode c))
      (FiniteSequenceCoding.tail (leftCode c)) (FiniteSequenceCoding.cons b (rightCode c))
    else if d = 1 then pack q b (leftCode c) (rightCode c)
    else pack q (FiniteSequenceCoding.head (rightCode c))
      (FiniteSequenceCoding.cons b (leftCode c)) (FiniteSequenceCoding.tail (rightCode c))

theorem transition_rows (L : Labeling T) (c q b : ℕ) (m : Move)
    (hc : Valid (Fintype.card Γ) (Fintype.card Q) c)
    (hw : lookup L (stateCode c) (currentCode c) = 1 + Nat.pair q (Nat.pair b (moveCode m))) :
    transition L c = match m with
    | .left => pack q (FiniteSequenceCoding.head (leftCode c))
        (FiniteSequenceCoding.tail (leftCode c)) (FiniteSequenceCoding.cons b (rightCode c))
    | .stay => pack q b (leftCode c) (rightCode c)
    | .right => pack q (FiniteSequenceCoding.head (rightCode c))
        (FiniteSequenceCoding.cons b (leftCode c)) (FiniteSequenceCoding.tail (rightCode c)) := by
  have hv := (validTest_spec _ _ _).mpr hc
  have hh : haltTest L c = false := by simp [haltTest, hv, hw]
  cases m <;> simp [transition, hh, hw, moveCode ]

theorem halted_fixed (L : Labeling T) (c : ℕ) (h : haltTest L c = true) :
    transition L c = c := by
  simp [transition, h]

private theorem entry_head (c : ℕ) :
    FiniteSequenceCoding.entry c 0 = FiniteSequenceCoding.head c := by
  rw [← FiniteSequenceCoding.code_decode c, FiniteSequenceCoding.entry_code,
    FiniteSequenceCoding.head_code]
  cases FiniteSequenceCoding.decode c <;> rfl

private theorem entry_tail (c i : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.tail c) i =
      FiniteSequenceCoding.entry c (i + 1) := by
  rw [← FiniteSequenceCoding.code_decode c, FiniteSequenceCoding.tail_code,
    FiniteSequenceCoding.entry_code, FiniteSequenceCoding.entry_code]
  simp

private theorem entry_cons_zero (b c : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.cons b c) 0 = b := by
  have hh := FiniteSequenceCoding.code_cons b (FiniteSequenceCoding.decode c)
  rw [FiniteSequenceCoding.code_decode] at hh
  rw [← hh, FiniteSequenceCoding.entry_code]
  rfl

private theorem entry_cons_succ (b c i : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.cons b c) (i + 1) =
      FiniteSequenceCoding.entry c i := by
  have hh := FiniteSequenceCoding.code_cons b (FiniteSequenceCoding.decode c)
  rw [FiniteSequenceCoding.code_decode] at hh
  rw [← hh, FiniteSequenceCoding.entry_code]
  simp [FiniteSequenceCoding.entry]

private theorem entries_cons {g b c : ℕ} (hb : b < g)
    (hc : ∀ i, FiniteSequenceCoding.entry c i < g) :
    ∀ i, FiniteSequenceCoding.entry (FiniteSequenceCoding.cons b c) i < g := by
  intro i
  cases i with
  | zero => rw [entry_cons_zero]; exact hb
  | succ i => rw [entry_cons_succ]; exact hc i

private theorem entries_tail {g c : ℕ}
    (hc : ∀ i, FiniteSequenceCoding.entry c i < g) :
    ∀ i, FiniteSequenceCoding.entry (FiniteSequenceCoding.tail c) i < g := by
  intro i
  rw [entry_tail]
  exact hc _

private theorem valid_pack {g s q a l r : ℕ} (hq : q < s) (ha : a < g)
    (hl : ∀ i, FiniteSequenceCoding.entry l i < g)
    (hr : ∀ i, FiniteSequenceCoding.entry r i < g) : Valid g s (pack q a l r) := by
  simp only [Valid, pack, stateCode, currentCode, leftCode, rightCode, Nat.unpair_pair]
  exact ⟨hq, ha, fun i _ => hl i, fun i _ => hr i⟩

theorem transition_valid (L : Labeling T) (c : ℕ)
    (hc : Valid (Fintype.card Γ) (Fintype.card Q) c) :
    Valid (Fintype.card Γ) (Fintype.card Q) (transition L c) := by
  have hg : 0 < Fintype.card Γ := by have := (cardinal_bounds T).1; omega
  have hall (d : ℕ) (hd : ∀ i < FiniteSequenceCoding.length d,
      FiniteSequenceCoding.entry d i < Fintype.card Γ) (i : ℕ) :
      FiniteSequenceCoding.entry d i < Fintype.card Γ := by
    by_cases hi : i < FiniteSequenceCoding.length d
    · exact hd i hi
    · rw [FiniteSequenceCoding.entry_out_of_range d i (by omega)]; exact hg
  have hl := hall _ hc.2.2.1
  have hr := hall _ hc.2.2.2
  have hhl : FiniteSequenceCoding.head (leftCode c) < Fintype.card Γ := by
    rw [← entry_head]; exact hl 0
  have hhr : FiniteSequenceCoding.head (rightCode c) < Fintype.card Γ := by
    rw [← entry_head]; exact hr 0
  let q := L.state.symm ⟨stateCode c, hc.1⟩
  let a := L.symbol.symm ⟨currentCode c, hc.2.1⟩
  have hq : (L.state q).val = stateCode c := by simp [q]
  have ha : (L.symbol a).val = currentCode c := by simp [a]
  have hw := lookup_actual L q a
  rw [hq, ha] at hw
  cases ht : T.table q a with
  | none =>
    have hh : haltTest L c = true := by simp [haltTest, hw, ht]
    rw [halted_fixed L c hh]
    exact hc
  | some row =>
    rcases row with ⟨q', b, m⟩
    have hh := transition_rows L c (L.state q').val (L.symbol b).val m hc
      (by simpa [ht] using hw)
    rw [hh]
    cases m with
    | left =>
      exact valid_pack (L.state q').isLt hhl (entries_tail hl)
        (entries_cons (L.symbol b).isLt hr)
    | stay =>
      exact valid_pack (L.state q').isLt (L.symbol b).isLt hl hr
    | right =>
      exact valid_pack (L.state q').isLt hhr
        (entries_cons (L.symbol b).isLt hl) (entries_tail hr)

theorem haltTest_primrec (L : Labeling T) : Primrec (haltTest L) := by
  have hv := validTest_primrec (Fintype.card Γ) (Fintype.card Q)
  have hw := (lookup_primrec L).comp fields_primrec.1 fields_primrec.2.1
  exact (Primrec.dom_bool₂ Bool.or).comp ((Primrec.dom_bool Bool.not).comp hv)
    ((Primrec.eq.comp hw (Primrec.const 0)).decide)
theorem haltCode_primrec (L : Labeling T) : Primrec (haltCode L) := by
  exact Primrec.ite ((Primrec.eq.comp (haltTest_primrec L) (Primrec.const true)))
    (Primrec.const 1) (Primrec.const 0)
theorem transition_primrec (L : Labeling T) : Primrec (transition L) := by
  have hh := haltTest_primrec L
  have hs := fields_primrec.1
  have ha := fields_primrec.2.1
  have hl := fields_primrec.2.2.1
  have hr := fields_primrec.2.2.2
  have hw : Primrec (fun c => lookup L (stateCode c) (currentCode c) - 1) :=
    Primrec.nat_sub.comp ((lookup_primrec L).comp hs ha) (Primrec.const 1)
  have hq := (Primrec.fst.comp Primrec.unpair).comp hw
  have hb := (Primrec.fst.comp Primrec.unpair).comp ((Primrec.snd.comp Primrec.unpair).comp hw)
  have hd := (Primrec.snd.comp Primrec.unpair).comp ((Primrec.snd.comp Primrec.unpair).comp hw)
  have hp {q a l r : ℕ → ℕ}
      (hq : Primrec q) (ha : Primrec a) (hl : Primrec l) (hr : Primrec r) :
      Primrec (fun x => pack (q x) (a x) (l x) (r x)) :=
    pack_primrec.comp (hq.pair (ha.pair (hl.pair hr)))
  exact Primrec.ite (Primrec.eq.comp hh (Primrec.const true)) Primrec.id
    (Primrec.ite (Primrec.eq.comp hd (Primrec.const 0))
      (hp hq (FiniteSequenceCoding.primrec_head.comp hl)
        (FiniteSequenceCoding.primrec_tail.comp hl) (FiniteSequenceCoding.primrec_cons.comp hb hr))
      (Primrec.ite (Primrec.eq.comp hd (Primrec.const 1)) (hp hq hb hl hr)
        (hp hq (FiniteSequenceCoding.primrec_head.comp hr)
          (FiniteSequenceCoding.primrec_cons.comp hb hl) (FiniteSequenceCoding.primrec_tail.comp hr))))

def marks : ℕ → ℕ
  | 0 => 0
  | n + 1 => FiniteSequenceCoding.cons 1 (marks n)

def initialCode : ℕ → ℕ
  | 0 => pack 0 0 0 0
  | n + 1 => pack 0 1 0 (marks n)

theorem marks_list (n : ℕ) : marks n = FiniteSequenceCoding.code (List.replicate n 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [marks, ih, List.replicate_succ, FiniteSequenceCoding.cons, Nat.add_comm]
theorem marks_primrec : Primrec marks := by
  exact (Primrec.nat_rec₁ 0
    (FiniteSequenceCoding.primrec_cons.comp₂ (Primrec₂.const 1) Primrec₂.right)).of_eq
      (fun n => by induction n <;> simp_all [marks])
theorem initialCode_primrec : Primrec initialCode := by
  have hh : Primrec (fun p : ℕ × ℕ => pack 0 1 0 (marks p.2)) :=
    pack_primrec.comp ((Primrec.const 0).pair
      ((Primrec.const 1).pair ((Primrec.const 0).pair (marks_primrec.comp Primrec.snd))))
  exact (Primrec.nat_casesOn Primrec.id (Primrec.const (pack 0 0 0 0)) hh.to₂).of_eq
    (fun n => by cases n <;> rfl)

def readoutBound (c : ℕ) : ℕ :=
  FiniteSequenceCoding.length (FiniteSequenceCoding.cons (currentCode c) (rightCode c))

noncomputable def rawReadout (c : ℕ) : ℕ :=
  PrimitiveRecursion.boundedSearch (fun w i => FiniteSequenceCoding.entry w i ≠ 1)
    (FiniteSequenceCoding.cons (currentCode c) (rightCode c)) (readoutBound c)

noncomputable def readoutCode (g s c : ℕ) : ℕ :=
  if validTest g s c then rawReadout c else 0

theorem readoutBound_eq (c : ℕ) : readoutBound c = 1 + FiniteSequenceCoding.length (rightCode c) := by
  have hh := FiniteSequenceCoding.code_cons (currentCode c)
    (FiniteSequenceCoding.decode (rightCode c))
  rw [FiniteSequenceCoding.code_decode] at hh
  have hd : FiniteSequenceCoding.decode
      (FiniteSequenceCoding.cons (currentCode c) (rightCode c)) =
      currentCode c :: FiniteSequenceCoding.decode (rightCode c) := by
    rw [← hh, FiniteSequenceCoding.decode_code]
  change (FiniteSequenceCoding.decode _).length = 1 + (FiniteSequenceCoding.decode _).length
  rw [hd, List.length_cons, Nat.add_comm]

theorem rawReadout_spec (c : ℕ) :
    FiniteSequenceCoding.entry (FiniteSequenceCoding.cons (currentCode c) (rightCode c)) (rawReadout c) ≠ 1 ∧
    (∀ i < rawReadout c,
      FiniteSequenceCoding.entry (FiniteSequenceCoding.cons (currentCode c) (rightCode c)) i = 1) ∧
    rawReadout c ≤ readoutBound c := by
  have hs := PrimitiveRecursion.boundedSearch_spec
    (fun w i => FiniteSequenceCoding.entry w i ≠ 1)
    (FiniteSequenceCoding.cons (currentCode c) (rightCode c)) (readoutBound c)
  change rawReadout c ≤ readoutBound c ∧ _ at hs
  refine ⟨?_, ?_, hs.1⟩
  · by_cases he : rawReadout c < readoutBound c
    · exact (hs.2.1 he).1
    · have heq : rawReadout c = readoutBound c := by omega
      rw [heq, FiniteSequenceCoding.entry_out_of_range _ _ (by rfl)]
      decide
  · intro i hi
    by_cases he : rawReadout c < readoutBound c
    · exact not_ne_iff.mp ((hs.2.1 he).2 i hi)
    · have heq : rawReadout c = readoutBound c := by omega
      exact not_ne_iff.mp ((hs.2.2.mp heq) i (by omega))

theorem readoutCode_bound (g s c : ℕ) : readoutCode g s c ≤ readoutBound c := by
  unfold readoutCode
  split_ifs
  · exact (rawReadout_spec c).2.2
  · exact Nat.zero_le _
theorem rawReadout_primrec : Primrec rawReadout := by
  have ht : PrimrecRel (fun w i => FiniteSequenceCoding.entry w i ≠ 1) :=
    (Primrec.eq.comp FiniteSequenceCoding.primrec_entry (Primrec.const 1)).not
  have hw := FiniteSequenceCoding.primrec_cons.comp fields_primrec.2.1 fields_primrec.2.2.2
  exact (PrimitiveRecursion.boundedSearch_primrec ht).comp hw
    (FiniteSequenceCoding.primrec_length.comp hw)
theorem readoutCode_primrec (g s : ℕ) : Primrec (readoutCode g s) := by
  exact Primrec.ite (Primrec.eq.comp (validTest_primrec g s) (Primrec.const true))
    rawReadout_primrec (Primrec.const 0)

noncomputable def arithmeticMachine (L : Labeling T) : MachinesAndComputationHistories.Machine where
  initial := initialCode
  transition := transition L
  halt := haltTest L
  output := readoutCode (Fintype.card Γ) (Fintype.card Q)

theorem arithmeticMachine_primitive (L : Labeling T) :
    MachinesAndComputationHistories.Primitive (arithmeticMachine L) := by
  exact ⟨initialCode_primrec, transition_primrec L, haltTest_primrec L,
    readoutCode_primrec _ _⟩

end Lemmatheca.ComputabilityTheory.TapeCoding
