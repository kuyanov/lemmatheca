import Lemmatheca.TruthTableAndWeakTruthTableReductions.Programs

/-! Finite certificate bars, computable level search and the total-functional criterion. -/
namespace Lemmatheca.ComputabilityTheory.StrongReductions

open OracleComputation OracleProgramNumberings UniversalComputation PostsTheorem
open IncomparableTuringDegrees

noncomputable section

def GoodLevel (e x n : ℕ) : Prop :=
  ∀ l ∈ binaryRows n, 0 < certificateValue (FiniteSequenceCoding.code l) e x

instance (e x n : ℕ) : Decidable (GoodLevel e x n) :=
  inferInstanceAs (Decidable (∀ l ∈ binaryRows n,
    0 < certificateValue (FiniteSequenceCoding.code l) e x))

def levelTest (e : ℕ) (p : ℕ × ℕ) : Bool := decide (GoodLevel e p.1 p.2)

theorem level_test_computable (e : ℕ) : Computable (levelTest e) := by
  have hv : Primrec (fun p : List ℕ × ℕ =>
      certificateValue (FiniteSequenceCoding.code p.1) e p.2) :=
    certificate_primitive.comp
      (((Primrec.encode.comp Primrec.fst).pair (Primrec.const e)).pair Primrec.snd)
  have hp : PrimrecRel (fun l x => 0 < certificateValue (FiniteSequenceCoding.code l) e x) :=
    (Primrec.nat_lt.comp (Primrec.const 0) hv).primrecRel
  have hall := hp.forall_mem_list
  exact (hall.decide.to_comp.comp
    (binaryRows_primrec.to_comp.comp Computable.snd) Computable.fst).of_eq
      (fun p => by simp only [levelTest, GoodLevel]; rfl)

theorem successful_level_exists (e : ℕ) (ht : AllOracleTotal (decodeCode e)) (x : ℕ) :
    ∃ n, GoodLevel e x n := by
  classical
  by_contra hn
  have hbad (n : ℕ) : ∃ l, l ∈ binaryRows n ∧
      certificateValue (FiniteSequenceCoding.code l) e x = 0 := by
    have hnot : ¬ ∀ l ∈ binaryRows n, 0 < certificateValue (FiniteSequenceCoding.code l) e x :=
      fun h => hn ⟨n, h⟩
    push Not at hnot
    obtain ⟨l, hl, hz⟩ := hnot
    exact ⟨l, hl, by omega⟩
  let α : ℕ → Type := fun n => {l : List ℕ // l ∈ binaryRows n ∧
    certificateValue (FiniteSequenceCoding.code l) e x = 0}
  have : ∀ n, Finite (α n) := fun n =>
    ((binaryRows n).finite_toSet.subset (fun _ h => h.1)).to_subtype
  have : ∀ n, Nonempty (α n) := fun n => by
    obtain ⟨l, hl, hz⟩ := hbad n
    exact ⟨⟨l, hl, hz⟩⟩
  let π : {i j : ℕ} → i ≤ j → α j → α i := fun {i j} hij a => by
    have hs := (binaryRows_spec j).1 a.val |>.mp a.property.1
    have hb : BinaryWord (a.val.take i) := fun b h => hs.1 b (List.mem_of_mem_take h)
    have hl : (a.val.take i).length = i := by simp [List.length_take, hs.2, min_eq_left hij]
    have hp : Prefix (FiniteSequenceCoding.code (a.val.take i)) (FiniteSequenceCoding.code a.val) := by
      apply (prefix_native _ _).mpr
      rw [binary_word_recovery _ hb, binary_word_recovery _ hs.1]
      exact List.take_prefix i a.val
    refine ⟨a.val.take i, (binaryRows_spec i).1 _ |>.mpr ⟨hb, hl⟩, ?_⟩
    by_contra hz
    obtain ⟨y, hy⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hpos := certificate_persists _ _ e x y hp hy
    rw [a.property.2] at hpos
    omega
  have hrefl : ∀ (i : ℕ) (a : α i), π (show i ≤ i from le_rfl) a = a := by
    intro i a
    apply Subtype.ext
    change a.val.take i = a.val
    have hl := ((binaryRows_spec i).1 a.val |>.mp a.property.1).2
    exact List.take_of_length_le hl.le
  have htrans : ∀ (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (a : α k),
      π hij (π hjk a) = π (hij.trans hjk) a := by
    intro i j k hij hjk a
    apply Subtype.ext
    change (a.val.take j).take i = a.val.take i
    simp only [List.take_take, min_eq_left hij]
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
    (fun {i} a => hrefl i a) (fun {i j k} hij hjk a => htrans i j k hij hjk a)
    (fun _ _ => Set.toFinite _)
  let u : ℕ → ℕ := fun n => FiniteSequenceCoding.code (f n).val
  have hlen (n : ℕ) : wordLength (u n) = n := by
    have hl := ((binaryRows_spec n).1 (f n).val |>.mp (f n).property.1).2
    simpa [u, wordLength, FiniteSequenceCoding.length] using hl
  have hprefix (n : ℕ) : Prefix (u n) (u (n + 1)) := by
    have he := congrArg Subtype.val (hf (Nat.le_succ n))
    change (f (n + 1)).val.take n = (f n).val at he
    apply (prefix_native _ _).mpr
    change List.IsPrefix (word (FiniteSequenceCoding.code (f n).val))
      (word (FiniteSequenceCoding.code (f (n + 1)).val))
    rw [binary_word_recovery _ (((binaryRows_spec n).1 _).mp (f n).property.1).1,
      binary_word_recovery _ (((binaryRows_spec (n + 1)).1 _).mp (f (n + 1)).property.1).1,
      ← he]
    exact List.take_prefix n _
  let G := unionSet u
  have hreal : ∀ n, Realizes (u n) G := (coherent_union u hprefix (fun n => (hlen n).ge)).1
  have hd := ht G x
  change (OracleProgramNumberings.phi G e x).Dom at hd
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨v, hv, hc⟩ := (prefix_output_iff G e x y).mp hy
  have hp : Prefix v (u (wordLength v)) := by
    refine ⟨by rw [hlen], fun q hq => ?_⟩
    exact (hv q hq).trans ((hreal _ q (by simpa only [hlen] using hq)).symm)
  have hpos := certificate_persists _ _ e x y hp hc
  have hz := (f (wordLength v)).property.2
  change certificateValue (u (wordLength v)) e x = 0 at hz
  rw [hz] at hpos
  omega


def uniformAllowance (e : ℕ) (ht : AllOracleTotal (decodeCode e)) (x : ℕ) : ℕ :=
  Nat.find (successful_level_exists e ht x)

theorem uniform_allowance (e : ℕ) (ht : AllOracleTotal (decodeCode e)) :
    Computable (uniformAllowance e ht) ∧
      (∀ x, GoodLevel e x (uniformAllowance e ht x)) ∧
      (∀ x n, GoodLevel e x n → uniformAllowance e ht x ≤ n) ∧
      ∀ x l, BinaryWord l → l.length = uniformAllowance e ht x →
        0 < certificateValue (FiniteSequenceCoding.code l) e x := by
  have hp : ComputablePred (fun p : ℕ × ℕ => GoodLevel e p.1 p.2) :=
    (level_test_computable e).computablePred.of_eq (fun p => by simp)
  refine ⟨Computable.find hp (successful_level_exists e ht),
    fun x => Nat.find_spec (successful_level_exists e ht x),
    fun x n hn => Nat.find_min' (successful_level_exists e ht x) hn, ?_⟩
  intro x l hl hn
  exact Nat.find_spec (successful_level_exists e ht x) l
    ((binaryRows_spec _).1 l |>.mpr ⟨hl,hn⟩)

def boundedData (e : ℕ) (h : ℕ → ℕ) : TableData :=
  ⟨h, fun x w => if finiteValue w (h x) e x = 2 then 1 else 0⟩

theorem bounded_allowance_scheme {e : ℕ} {h : ℕ → ℕ} {A B : Set ℕ}
    (hb : BoundedAllowance e h A B) : Presents (boundedData e h) A B := by
  have hpack : Computable (fun p : ℕ × ℕ => pack4 p.2 (h p.1) e p.1) :=
    Primrec₂.natPair.to_comp.comp Computable.snd
      (Primrec₂.natPair.to_comp.comp (hb.1.comp Computable.fst)
        (Primrec₂.natPair.to_comp.comp (Computable.const e) Computable.fst))
  have hv : Computable (fun p : ℕ × ℕ => finiteValue p.2 (h p.1) e p.1) :=
    (finiteValue_primitive.to_comp.comp hpack).of_eq (fun p => by
      simp only [finiteValueInput, pack4, Nat.unpair_pair])
  have hp : Computable (fun p : ℕ × ℕ => decide (finiteValue p.2 (h p.1) e p.1 = 2)) :=
    Primrec.eq.decide.to_comp.comp hv (Computable.const 2)
  have hc : Computable (fun p : ℕ × ℕ => if finiteValue p.2 (h p.1) e p.1 = 2 then 1 else 0) :=
    (Computable.cond hp (Computable.const 1) (Computable.const 0)).of_eq
      (fun p => by simp only [Bool.cond_decide])
  refine ⟨⟨hb.1, hc, ?_⟩, ?_⟩
  · intro x w
    change (if finiteValue w (h x) e x = 2 then 1 else 0) = 0 ∨ (if finiteValue w (h x) e x = 2 then 1 else 0) = 1
    split_ifs <;> simp
  · intro x
    change (if finiteValue (prefixCode B (h x)) (h x) e x = 2 then 1 else 0) = _
    rw [finiteValue_agreement B _ _ e x (prefixCode_spec B (h x)).2, hb.2 x]
    rcases indicator_bits A x with he | he <;> simp [he]

/-- Exact reusable interface: the bound is the allowance of the existing evaluator. -/
theorem tt_of_boundedAllowance {e : ℕ} {h : ℕ → ℕ} {A B : Set ℕ}
    (hh : Computable h)
    (hb : ∀ x, boundedValue B (h x) e x = indicator (fun n => n ∈ A) x + 1) :
    TruthTableReducible A B := by
  exact ⟨boundedData e h, bounded_allowance_scheme ⟨hh,hb⟩⟩

theorem total_program_bounded_allowance {A B : Set ℕ} (c : Code)
    (ht : AllOracleTotal c) (hc : TuringDegrees.Reduces c A B) :
    ∃ h : ℕ → ℕ, BoundedAllowance (encodeCode c) h A B := by
  have hi : AllOracleTotal (decodeCode (encodeCode c)) := by simpa only [decode_encode] using ht
  let h := uniformAllowance (encodeCode c) hi
  have hu := uniform_allowance (encodeCode c) hi
  refine ⟨h, hu.1, fun x => ?_⟩
  let w := prefixCode B (h x)
  have hwlen : wordLength w = h x := (prefixCode_spec B (h x)).1
  have hw : Realizes w B := by
    intro q hq
    exact (prefixCode_spec B (h x)).2 q (by simpa only [hwlen] using hq)
  have hl : BinaryWord (FiniteSequenceCoding.decode w) := by
    intro b hb
    change b ∈ FiniteSequenceCoding.decode (prefixCode B (h x)) at hb
    simp only [prefixCode, FiniteSequenceCoding.decode_code] at hb
    obtain ⟨q,_hq,rfl⟩ := List.mem_map.mp hb
    exact indicator_bits B q
  have hpos := hu.2.2.2 x (FiniteSequenceCoding.decode w) hl hwlen
  rw [FiniteSequenceCoding.code_decode] at hpos
  obtain ⟨y,hy⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hout := certificate_sound B w (encodeCode c) x y hw hy
  change y ∈ eval B (decodeCode (encodeCode c)) x at hout
  rw [decode_encode, hc x] at hout
  have heq : y = indicator (fun n => n ∈ A) x := Part.mem_some_iff.mp hout
  rw [heq] at hy
  have hag : Agreement w (h x) B := by
    intro q hq
    exact hw q (by simpa only [hwlen] using hq)
  change finiteValue w (wordLength w) (encodeCode c) x = _ at hy
  rw [hwlen, finiteValue_agreement B w (h x) (encodeCode c) x hag] at hy
  exact hy

theorem tt_iff_allOracleTotal (A B : Set ℕ) :
    TruthTableReducible A B ↔
      ∃ c : Code, AllOracleTotal c ∧ TuringDegrees.Reduces c A B := by
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨tableProgram s hs.1, (table_program_reduces hs).2,
      fun x => (table_program s hs.1 B x).1.trans (congrArg Part.some (hs.2 x))⟩
  · rintro ⟨c,ht,hc⟩
    obtain ⟨h,hh,hb⟩ := total_program_bounded_allowance c ht hc
    exact tt_of_boundedAllowance hh hb

theorem tt_iff_boundedAllowance (A B : Set ℕ) :
    TruthTableReducible A B ↔ ∃ e h, BoundedAllowance e h A B := by
  constructor
  · intro h
    obtain ⟨c,ht,hc⟩ := (tt_iff_allOracleTotal A B).mp h
    obtain ⟨u,hu⟩ := total_program_bounded_allowance c ht hc
    exact ⟨encodeCode c,u,hu⟩
  · rintro ⟨e,h,hh,hb⟩
    exact tt_of_boundedAllowance hh hb

end
end Lemmatheca.ComputabilityTheory.StrongReductions
